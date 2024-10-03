#lang eopl
#| 
Sheila Marcela Valencia Chito - 2243011
Victoria Andrea Volveras Parra - 2241874
github: https://github.com/Vovleras/Taller-3-FLP
 |#
 
;; Interpretador para tercer taller

;; La definición BNF para las expresiones del lenguaje:
;;
;;  <programa>       ::= <expresion>
;;                      <un-programa (exp)>
;;  <expresion>     ::= <numero>
;;                      <numero-lit (num)>
;;                  ::= "\"" <texto> "\""
;;                      <texto-lit (num)>
;;                  ::= <identificador>
;;                      <var-exp (id)>
;;                  ::= (<expresion> <primitiva-binaria> <expresion>)
;;                      <primapp-bin-exp (exp1 prim-binaria exp2)>
;;                  ::= <primitiva-unaria> (<expresion>)
;;                      <primapp-un-exp (prim-unaria exp)>
;;                  ::= Si <expresion> "{" <expresion>  "}" "sino" "{" <expresion> "}"
;;                      <condicional-exp (test-exp true-exp false-exp)>
;;                  ::= declarar ({<identificador> = <expresion> ';' }*)) { <expresion> }
;;                      <variableLocal-exp (ids exps cuerpo)>
;;                  ::= procedimiento (<identificador>*(',') ) "{" <expresion> "}"
;;                      <procedimiento-exp (ids cuero)>
;;                  ::= "evaluar" expresion   (expresion *(",") )  finEval
;;                      <app-exp(exp exps)>
;;                  ::= recursion  {identificador ({identificador}*(,)) = <expression>}* en <expression>
;;                      <recursion-exp (proc-namess idss bodies cuerpo-rec)>
;;  <primitiva-binaria>     ::= + | ~ | / | * | concat | > | < | >= | <= | != | == |
;;  <primitiva-unaria>      ::= longitud | add1 | sub1 | neg


;; Especificación léxica

(define scanner-spec-simple-interpreter
'((white-sp
    (whitespace) skip)
  (comment
    ("//" (arbno (not #\newline))) skip)
  (identificador
    ("@" letter (arbno (or letter digit ))) symbol)
  (texto
    ((or letter "_" ) (arbno (or letter digit "_" ":"))) string)
  (numero
    (digit (arbno digit)) number)
  (numero
    ("-" digit (arbno digit)) number)
  (numero
    (digit (arbno digit) "." digit (arbno digit)) number)
  (numero
    ("-" digit (arbno digit) "." digit (arbno digit)) number)))


;; Especificación sintáctica (gramática)

(define grammar-simple-interpreter
  '((programa (expresion) un-programa)
    
    (expresion (numero) numero-lit)
    (expresion ("\""texto"\"") texto-lit)
    (expresion (identificador) var-exp)
    (expresion ( primitiva-unaria "(" expresion ")" ) primapp-un-exp)
    (expresion ("(" expresion primitiva-binaria expresion ")" ) primapp-bin-exp)
    (expresion ("Si" expresion "{" expresion "}" "sino" "{" expresion "}") condicional-exp)
    (expresion ("declarar" "(" (arbno identificador "=" expresion ";" ) ")" "{" expresion "}" ) variableLocal-exp)
    (expresion ( "procedimiento" "(" (separated-list identificador "," ) ")" "{" expresion "}") procedimiento-exp) 
    (expresion ("evaluar" expresion "(" (separated-list expresion ",") ")" "finEval" )app-exp)
    (expresion ("recursion" (arbno "{" identificador "(" (separated-list identificador ",") ")" "=" expresion "}") "en" expresion) recursion-exp)
    
    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("~") primitiva-resta)
    (primitiva-binaria ("/") primitiva-div)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("concat") primitiva-concat)
    (primitiva-binaria (">") primitiva-mayor)
    (primitiva-binaria ("<") primitiva-menor)
    (primitiva-binaria (">=") primitiva-mayor-igual)
    (primitiva-binaria ("<=") primitiva-menor-igual)
    (primitiva-binaria ("!=") primitiva-diferente)
    (primitiva-binaria ("==") primitiva-comparador-igual)
    
    (primitiva-unaria ("longitud") primitiva-longitud)
    (primitiva-unaria ("add1") primitiva-add1)
    (primitiva-unaria ("sub1") primitiva-sub1)
    (primitiva-unaria ("neg") primitiva-negacion-booleana)))

;; Construidos automáticamente:
(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)))


;; Parser, Scanner, Interfaz

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados)
(define scan&parse
  (sllgen:make-string-parser scanner-spec-simple-interpreter grammar-simple-interpreter))

;; El Analizador Léxico (Scanner)
(define just-scan
  (sllgen:make-string-scanner scanner-spec-simple-interpreter grammar-simple-interpreter))

;; El Interpretador (FrontEnd + Evaluación + señal para lectura)
(define interpretador
  (sllgen:make-rep-loop "--> "
    (lambda (pgm) (evaluar-pgm pgm))
    (sllgen:make-stream-parser 
      scanner-spec-simple-interpreter
      grammar-simple-interpreter)))

;; Ambientes
;definición del tipo de dato ambiente
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record (syms (list-of symbol?))
                       (vals (list-of scheme-value?))
                       (env environment?))
  (recursive-env-extended    (proc-names (list-of symbol?))
                             (idss (list-of (list-of scheme-value?)))
                             (bodies (list-of expresion?))
                             (env environment?)))

(define scheme-value? (lambda (v) #t))

;empty-env:      -> enviroment
;Función que crea un ambiente vacío
(define empty-env  
  (lambda ()
    (empty-env-record)))       ;llamado al constructor de ambiente vacío 


;extend-env: <list-of symbols> <list-of numbers> enviroment -> enviroment
;Función que crea un ambiente extendido
(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define extend-env-recursive
  (lambda (names-proc idss bodies env)
    (recursive-env-extended names-proc idss bodies env)))

; Ambiente inicial
(define amb-inicial
  (extend-env '(@a @b @c @d @e) '(1 2 3 "hola" "FLP")
  (empty-env)))

; DATATYPE PROCEDIMIENTO

(define-datatype procVal procVal?
  (cerradura  (lista-ID (list-of symbol?))
              (exp expresion?)
              (amb environment?)
  ))

; Funcion que evalua una cerradura

(define apply-cerradura
  (lambda(proc operadores)
    (cases procVal proc
      (cerradura (ids exp amb)
        (evaluar-expresion exp (extend-env ids operadores amb))))))

;Función que evalúa un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)
(define evaluar-pgm
  (lambda (exp)
    (cases programa exp
      (un-programa (expresion) (evaluar-expresion expresion amb-inicial)))
    )
)

;Evalua la expresión en el ambiente de entrada
(define evaluar-expresion
  (lambda (exp amb)
    (cases expresion exp
        (numero-lit (num) num)
        (texto-lit (txt) txt)
        (var-exp (id) (buscar-variable amb id))
        (primapp-bin-exp (exp1 pim-binario exp2)
                    (apply-bin-exp pim-binario (evaluar-expresion exp1 amb) (evaluar-expresion exp2 amb)))
        (primapp-un-exp (prim-un exp) 
                    (apply-un-exp prim-un (evaluar-expresion exp amb)))
        (condicional-exp (test-exp true-exp false-exp)
                    (if (determinar-if? (evaluar-expresion test-exp amb))
                        (evaluar-expresion true-exp amb)
                        (evaluar-expresion false-exp amb)))
        (variableLocal-exp (ids exps cuerpo)
          (let ((args (evaluar-operadores exps amb))) 
              (evaluar-expresion cuerpo (extend-env ids args amb))))
        (procedimiento-exp (ids cuerpo)
          (cerradura ids cuerpo amb))
        (app-exp (exp exps)
          (let ((params (evaluar-operadores exps amb))    
                (procedimiento (evaluar-expresion exp amb)))  
              (if (procVal? procedimiento)                  
                  (apply-cerradura procedimiento params)   
                  (eopl:error 'evaluar-expresion "Intento de aplicar un enfoque no proedimental ~s" procedimiento))))
        (recursion-exp (noms-procss idss bodies body-recur)
          (evaluar-expresion body-recur 
              (extend-env-recursive noms-procss idss bodies amb)))                     
    )
  )
)

;Aplicar operación binaria
(define apply-bin-exp
  (lambda (pim-bin arg1 arg2)
    (cases primitiva-binaria pim-bin
      (primitiva-suma () (+ arg1 arg2))
      (primitiva-resta () (- arg1 arg2))
      (primitiva-div () (/ arg1 arg2))
      (primitiva-multi () (* arg1 arg2))
      (primitiva-concat () (string-append arg1 arg2))
      (primitiva-mayor () (valor-verdad? > arg1 arg2))
      (primitiva-menor () (valor-verdad? < arg1 arg2))
      (primitiva-mayor-igual () (valor-verdad? >= arg1 arg2))
      (primitiva-menor-igual () (valor-verdad? <= arg1 arg2))
      (primitiva-diferente () (desigualdad? arg1 arg2))
      (primitiva-comparador-igual () (valor-verdad? equal? arg1 arg2))
    )
  )
)

;Aplicar operación unaria
(define apply-un-exp
  (lambda (prim-un arg)
    (cases primitiva-unaria prim-un
      (primitiva-longitud () (saber-longitud arg))
      (primitiva-add1 () (+ arg 1))
      (primitiva-sub1 () (- arg 1))
      (primitiva-negacion-booleana () (negar-arg arg))
    )
  )
)

;Evaluar valor de verdad
(define valor-verdad?
  (lambda(pim arg1 arg2)
    (if (pim arg1 arg2) 1 0)))

;determinar-if?: determina si un valor dado corresponde a un valor booleano falso o verdadero
(define determinar-if?
  (lambda (x)
    (not (zero? x))))

;Funcion que permite evaluar la desigualdad
(define desigualdad?
  (lambda(arg1 arg2)
    (if (equal? arg1 arg2) 0 1)))

;Funcion que permite evaluar la longitud de un elemento
(define saber-longitud
  (lambda(arg)
    (if (string? arg) (string-length arg) (length arg))))

;Funcion para obtener la negación booleana
(define negar-arg
  (lambda(arg)
    (if (equal? arg 1) #f #t)))

;Funcion que evalua una lista de expresiones

(define evaluar-operadores
  (lambda(args env)
    (map (lambda(x) (evaluar-expresion x env))args)))

;Función que busca un símbolo en un ambiente
(define buscar-variable
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
                        (eopl:error 'empty-env "No binding for ~s" sym))
      (extended-env-record (syms vals old-env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (buscar-variable old-env sym))))
      (recursive-env-extended (proc-names idss bodies old-env)
                (let ((pos (list-find-position sym proc-names)))
                    (if (number? pos) 
                      (cerradura (list-ref idss pos)
                                  (list-ref bodies pos)
                                  env)
                      (buscar-variable old-env sym)))))))


;Funciones Auxiliares

; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de unambiente

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

(interpretador)



#| 

Punto A
recursion {@valorEntero(@dividendo, @divisor) = Si (@dividendo < @divisor) { 0 } sino {(1 + evaluar @valorEntero((@dividendo ~  @divisor),@divisor) finEval)}} 
          {@sumarDigitos(@num) = Si (@num < 10) { @num } sino {((@num ~ (evaluar  @valorEntero(@num, 10) finEval * 10)) + evaluar @sumarDigitos(evaluar  @valorEntero(@num, 10) finEval) finEval )}} 
          en 
           evaluar  @sumarDigitos(147) finEval

PUNTO B

recursion { @fact (@x) = Si @x {(@x * evaluar @fact (sub1(@x)) finEval) } sino {1} }
          en
           evaluar @fact (5) finEval


recursion { @fact (@x) = Si @x {(@x * evaluar @fact (sub1(@x)) finEval) } sino {1} } 
          en 
            evaluar @fact (10) finEval

PUNTO C 
recursion { @potencia(@base, @exp) = Si (@exp == 0) { 1 } sino {(@base * evaluar @potencia(@base, (@exp ~ 1)) finEval)}}
          en 
            evaluar @potencia(4,2) finEval

PUNTO D

recursion { @sumaRango (@a,@b) = Si (@a > @b) {0} sino {(@a + evaluar @sumaRango ((@a + 1) , @b) finEval)} } 
          en
            evaluar @sumaRango (2 , 5) finEval

PUNTO E

  recursion { @integrantes () = "Victoria_y_Sheila"}
            { @saludar (@proc) = procedimiento () { ("Hola:" concat evaluar @proc () finEval)}}

            en
              declarar (
                          @decorate = evaluar @saludar (@integrantes) finEval;
                        )
                        {
                          evaluar @decorate () finEval
                        } 


  PUNTO F             
  recursion { @integrantes () = "Victoria_y_Sheila"}
             { @saludar (@proc) = procedimiento () { ("Hola:" concat  evaluar @proc () finEval )}}

             en
                declarar (
                            @decorate = procedimiento (@arg) {(evaluar evaluar @saludar (@integrantes) finEval () finEval concat @arg)};
                          )
                          {
                            evaluar @decorate ("_ProfesoresFLP") finEval 
                          }                  
                        
|#
