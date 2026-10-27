module

public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def RawK (n w : Nat) (PS PSI LR TR TRI : Nat → Nat) (kS kO : Nat) (D : List (List Int))
    (nb BP NS CH : Nat) : Prop :=
  headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true ∧
    LevelsOK n w PS PSI LR TR TRI kS nb BP ∧ n ≤ NS * CH ∧
    ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true

theorem rawK_sound {n w kS kO nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base) (h : RawK n w PS PSI LR TR TRI kS kO D nb BP NS CH)
    (chunks : Nat) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      chunks = true :=
  rawChainK_sound hb h.1 h.2.1 h.2.2.1 h.2.2.2

end CFSG.KS.Raw

end
