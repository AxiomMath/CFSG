module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def Sec63PTFactAt (P : Type) [Group P] (α : MulAut P) : Prop :=
  ∀ V : Subgroup P, IsComponentIn V (fixSub α) → IsL29 V →
    ∀ b ∈ V, orderOf b = 2 →
      IsI4PlusIn (⊤ : Subgroup P) b ∨
      ∃ Vb : Subgroup P, IsComponentIn Vb (centralizer ({b} : Set P)) ∧ IsL29 Vb ∧
        (∀ K : Subgroup P, IsComponentIn K (centralizer ({b} : Set P)) → K = Vb) ∧
        (∀ Q : Subgroup P, IsPGroup 2 Q →
          Q ≤ V ⊓ centralizer ({b} : Set P) ⊓ centralizer (Vb : Set P) → Nat.card Q ≤ 2) ∧
        ∃ R : Subgroup P, IsPGroup 2 R ∧ R ≤ V ⊓ centralizer ({b} : Set P) ∧ Nat.card R = 8 ∧
          R = closure {r : P | r ∈ R ∧ orderOf r = 2}

@[expose] def Asc82FactOm6PA6Bar : Prop :=
  ∀ α : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 (ZMod 3)),
    (∃ (A : GL (Fin 4) (ZMod 3)) (ε : ℕ), ε ≤ 1 ∧
      α = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 4 (ZMod 3) A *
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut 4 (ZMod 3) ^ ε) →
    orderOf α = 2 →
    Sec63PTFactAt (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 (ZMod 3)) α

end CFSG.OddStandard.SmallF3.Omega
