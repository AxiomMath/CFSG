module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] def Sec63PCAt (Y V : Subgroup G) (b : G) : Prop :=
  IsI4PlusIn Y b ∨
    ∃ Vb : Subgroup G, IsComponentIn Vb (Y ⊓ centralizer ({b} : Set G)) ∧ IsL29 Vb ∧
      (∀ K : Subgroup G, IsComponentIn K (Y ⊓ centralizer ({b} : Set G)) → K = Vb) ∧
      (∀ Q : Subgroup G, IsPGroup 2 Q →
        Q ≤ V ⊓ centralizer ({b} : Set G) ⊓ centralizer (Vb : Set G) → Nat.card Q ≤ 2) ∧
      ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ V ⊓ centralizer ({b} : Set G) ∧ Nat.card R = 8 ∧
        R = closure {r : G | r ∈ R ∧ orderOf r = 2}

@[expose] def Sec63PCFact (Y : Subgroup G) (s : G) : Prop :=
  ∀ V : Subgroup G, IsComponentIn V (Y ⊓ centralizer ({s} : Set G)) → IsL29 V →
    ∀ b ∈ V, orderOf b = 2 → Sec63PCAt Y V b

@[expose] def Sec63PCA6 (Y : Subgroup G) (s : G) (L : Subgroup G) : Prop :=
  L ≤ Y ⊓ centralizer ({s} : Set G) ∧
    (∀ h ∈ Y ⊓ centralizer ({s} : Set G), ∀ x ∈ L, h * x * h⁻¹ ∈ L) ∧
    (∃ a : ℕ, L.relIndex (Y ⊓ centralizer ({s} : Set G)) = 2 ^ a) ∧ IsSimpleGroup ↥L

end CFSG.OddStandard.SmallF3.Omega
