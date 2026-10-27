module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsS8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Sec128WrAct {G : Type} [Group G] (V : Subgroup G) (Y : Subgroup (MulAut ↥V)) :
    Prop :=
  ∃ (e : WrZ2 ↥(alternatingGroup (Fin 5)) ≃* ↥Y)
    (φ : Multiplicative (ZMod 2) → (Fin 5 → ZMod 2) → ↥V)
    (Vq : Multiplicative (ZMod 2) → Subgroup ↥V),
    (∀ q, Sec128Coord (Vq q) (φ q)) ∧
      Vq 1 ⊔ Vq (Multiplicative.ofAdd 1) = ⊤ ∧ Vq 1 ⊓ Vq (Multiplicative.ofAdd 1) = ⊥ ∧
      ∀ (w : WrZ2 ↥(alternatingGroup (Fin 5))) (q : Multiplicative (ZMod 2)) (v : Fin 5 → ZMod 2),
        IsEvenVec v →
          ((e w : ↥Y) : MulAut ↥V) (φ q v) =
            φ (w.right * q)
              (permVec ((w.left (w.right * q) : ↥(alternatingGroup (Fin 5))) :
                Equiv.Perm (Fin 5)) v)

end CFSG.OddStandard.SmallF3.Omega
