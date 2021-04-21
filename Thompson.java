/**
 *
 */
package com.py.compilers.algorithms;

import com.py.compilers.structures. *;
import com.py.compilers.analysis.Alphabet;

/**
 * Esta classe implementa os algoritmos de Thompson para cada
 * um dos operadores de uma expressão regular. <br> <br>
 * Deve-se notar que as operações implementadas neste
 * classe tem efeitos colaterais sobre
 * os AFNs recebidos como argumentos, visto que em certos casos
 * estes são alterados. No entanto, para fins práticos
 * isso não é um problema, pois na tradução de um
 * expressão regular para AFN sempre será significativa apenas o
 * último AFN construído. <br> <br>
 * A solução que poderia ser aplicada para corrigir este efeito
 * é implementar uma função de cópia para AFNs.
 * @author Lucas Vilela
 */
public class Thompson {

    /**
     * Construir um AFN a partir de um símbolo, que pode ser
     * um símbolo do alfabeto ou o símbolo vazio.
     * símbolo @param O símbolo a partir do qual construir o AFN.
     * @return O AFN para o <code> símbolo </code>.
     */
    public static AFN basico(String simbolo) {
        AFN afn = new AFN ();
       
        /* Estados inicial e final */
        Estado ini = new Estado (0);
        Estado fin = new Estado (1, true);
       
        /* Transição entre os estados inicial e final */
        Transition tran = new Transition (fin, simbolo);
        ini.getTransitions().agregar(tran);
       
        /* Adicionamos os estados ao AFN */
        afn.addState (ini);
        afn.addState (end);
       
        return afn;
    }
   
    /**
     * Aplica o cadeado Kleene (*) a um determinado AFN.
     * @param afn O AFN no qual aplicar a trava Kleene.
     * @return O AFN resultante da aplicação do bloqueio de Kleene a <code> afn </code>.
     */
    public static AFN lockKleene (AFN afn) {
        AFN afn_out = novo AFN ();
               
        /* Adicionamos o estado inicial */
        NewStartState = new Status (afn_output.QuantityStates ());
        afn_output.addState (new Start);
       
        /*
         * Adicionamos os outros estados, o incremento é o mesmo
         * para a quantidade de status no AFN de destino.
         */
        Automata.CopyStates (afn, afn_output, afn_output.quantityStates ());
       
        /* Adicionamos o estado final */
        New StateEnd = novo estado (afn_output.quantityStates (), true);
        afn_output.addState (newEnd);
       
        /* Adicionamos transições adicionais do novo estado inicial*/
        newStart.getTransitions (). add (new Transition (afn_exit.getState (1), Alphabet.EMPTY));
        newStart.getTransitions (). add (new Transition (newEnd, Alphabet.EMPTY));
       
        /* Estado antes do fim */
        Estado beforeEnd = afn_output.getEstado (afn_output.quantidadEstados () - 2);
       
        /* Adicionamos transições adicionais do estado final anterior */
        beforeEnd.getTransitions (). add (new Transition (afn_out.getState (1), Alphabet.EMPTY));
        beforeEnd.getTransitions (). add (new Transition (newEnd, Alphabet.EMPTY));
       
        return afn_out;
    }
   
    /**
     * Aplica bloqueio positivo (+) a um determinado AFN.
     * @param afn O AFN no qual aplicar o bloqueio positivo.
     * @return O AFN resultante da aplicação de bloqueio positivo a <code> afn </code>.
     */
    public static AFN bloqueioPositivo (AFN afn) {
        return.concatenacao (afn, lockKleene (afn));
    }
   
    /**
     * Aplica o operador de opção (?) A um determinado AFN.
     * @param afn O AFN no qual aplicar o operador de opção.
     * @return O AFN resultante da aplicação do operador de opção a <code> afn </code>.
     */
    public static AFN option (AFN afn) {
        return.union (afn, basic (Alphabet.EMPTY));
    }
   
    /**
     * Aplique o operador sindical a dois AFNs fornecidos.
     * @param afn1 O primeiro operando da união.
     * @param afn2 O segundo operando da união.
     * @return O AFN resultante da união de
     * <code> afn1 </code> e <code> afn2 </code>.
     */
    public static AFN union(AFN afn1, AFN afn2) {
        Transition trans;
        AFN afn = new AFN ();
       
        /* Adicionamos o estado inicial */
        NewStart State = new State (afn.quantityStates ());
        afn.addState (newStart);
       
        /*
         * Adicionamos os estados de afn1, o incremento é igual
         * para a quantidade de status no AFN de destino.
         */
        Automata.CopyStates (afn1, afn, afn.states quantity ());
       
        /*
         * Adicionamos os estados de afn2, o incremento é igual
         * para a quantidade de status no AFN de destino.
         */
        Automata.CopyStates (afn2, afn, afn.states quantity ());
       
        /*Adicionamos o estado final */
        New StateEnd = new State (afn.quantityStates (), true);
        afn.addState (newEnd);
       
        /*
         * Criamos uma transição vazia do estado inicial
         * de afn para o estado inicial de afn1 (agora em afn).
         */
        trans = new Transition ();
        trans.setState (afn.getState (1));
        trans.setSymbol (EMPTY Alphabet);
        newStart.getTransitions (). add (trans);
       
        /*
         * Criamos uma transição vazia do estado inicial
         * de afn para o estado inicial de afn2 (agora em afn).
         */
        trans = nova Transição ();
        trans.setState (afn.getState (afn1.quantityStates () + 1));
        trans.setSymbol (Alphabet.EMPTY);
        newStart.getTransitions (). add (trans);
       
        /*
         * Criamos uma transição vazia do estado final
         * de afn1 (agora em afn) para o estado final de afn.
         */
        trans =  new Transition ();
        trans.setState (afn.getState (afn.state quantidade () - 1));
        trans.setSymbol (Alphabet.EMPTY);
        afn.getState (afn1.quantityStates ()). getTransitions (). add (trans);
       
        /*
         * Criamos uma transição vazia do estado final
         * de afn2 (agora em afn) para o estado final de afn.
         */
        trans = new Transition ();
        trans.setState (afn.getState (afn.state quantidade () - 1));
        trans.setSymbol (Alphabet.EMPTY);
        afn.getState (afn.quantityStates () - 2) .getTransitions (). add (trans);
       
        return afn;
    }
   
    /**
     * Aplique o operador de concatenação a dois AFNs fornecidos.
     * @param afn1 O primeiro operando da concatenação.
     * @param afn2 O segundo operando da concatenação.
     * @return O AFN resultante da concatenação de
     * <code> afn1 </code> e <code> afn2 </code>.
     */
    public static AFN concentration (AFN afn1, AFN afn2) {
        AFN afn = new AFN ();
       
        /*
         * Adicionamos os estados de afn1, o incremento é igual
         * à quantidade de status no AFN de destino, que neste
         * caso é igual a zero.
         */
        Automata.CopyStates (afn1, afn, afn.states quantity ());
       
        /* Último estado atual do autômato que estamos gerando */
        Estado lastActual = afn.getState (afn.quantityStates () - 1);
       
        /*
         * Adicionamos os estados de afn2, exceto o primeiro.
         * Neste caso, o incremento é igual ao máximo
         * identificador de estados no destino AFN e não para
         * o número de estados desde que um estado seja omitido aqui.
         */
        Automata.CopyStates (afn2, afn, afn.states quantidade () - 1, 1);
       
        /* Estado inicial de afn2 */
        StartStateAfn2 = afn2.getInitState ();
       
        /*
         * Adicionamos as transições do estado inicial de afn2
         * (agora em afn) para o estado final de afn1 (agora em afn).
         */
        Automata.CopyTransitions (afn, startAfn2.getTransitions (),
                            lastActual, lastActual.getIdentifier ());
       
        /* Definir estado final */
        afn.getState (afn.quantityStates () - 1) .setEsFinal (true);
       
        return afn;
    }
}
