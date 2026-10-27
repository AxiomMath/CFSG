module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAbs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTri

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

section Model

@[expose] def E4TwinLayW (M : Type) [Group M] : Prop :=
  ∀ (K K' : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
    (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
    K' ∈ CoreAssembly.conjClass K → K' ≠ K → K' ≤ Subgroup.normalizer (K : Set M) →
    (∀ J ∈ CoreAssembly.conjClass K, J ≠ K → J ≤ Subgroup.normalizer (K : Set M) → J = K') →
    ∀ a b : M, a ≠ 1 → b ≠ 1 → a ≠ b →
      K ≤ Subgroup.centralizer ({a} : Set M) → K' ≤ Subgroup.centralizer ({a} : Set M) →
      K ≤ Subgroup.centralizer ({b} : Set M) → K' ≤ Subgroup.centralizer ({b} : Set M) →
      ¬ Group.IsSolvable ↥(Ea (CoreAssembly.conjClass K) a) →
      ¬ Group.IsSolvable ↥(Ea (CoreAssembly.conjClass K) b) →
      ∃ x ∈ Ea (CoreAssembly.conjClass K) a, x * b * x⁻¹ * b⁻¹ ≠ 1 ∧ (x * b * x⁻¹ * b⁻¹) ^ 3 = 1

@[expose] def E4TwinLayModel : Prop :=
  ∀ (M : Type) [Group M] [Finite M],
    (CFSG.Blueprint.LieModel M .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) → E4TwinLayW M

end Model

section Leaf

@[expose] def L7NoE4T (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y) (Z : Subgroup Y) (f : Y), L7Ctx n Y R S t K' W u e g Z f →
      LemL.Q8Pre (SecQuot (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f)))
        (p23SecFamV R (aSub R Z e ⊓ aSub R Z f)) →
      ∀ K ∈ p23SecFamV R (aSub R Z e ⊓ aSub R Z f),
        ∀ τ : SecQuot (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f)), IsUniqueInvolution K τ →
          ¬ TightInO2 τ → ¬ TwinE4 (SecQuot (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f)))

end Leaf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
