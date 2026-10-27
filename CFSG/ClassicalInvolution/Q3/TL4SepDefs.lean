module

public import CFSG.ClassicalInvolution.Q3.TL3C11R

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

structure T4Hyp (r : ℕ) (G : Type) [Group G] (Δ : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Δ
  twoGroup : ∀ J ∈ Δ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)
  quat : ∀ J ∈ Δ, ∀ P : Subgroup G, IsSylow2In P J →
    Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))
  tight : ∀ J ∈ Δ, ∀ u : G, IsUniqueInvolution J u →
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)
  noTwins : ∀ J ∈ Δ, ∀ J' ∈ Δ, ∀ u : G, IsUniqueInvolution J u → IsUniqueInvolution J' u →
    J = J'
  aEmpty : ∀ J ∈ Δ, AEmpty Δ J
  odd : classicalInvolutionOddCore G = ⊥

@[expose] def Thm4RBelow (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ Δ : Set (Subgroup G), T4Hyp r G Δ →
    ∀ J ∈ Δ, ∀ L ∈ Δ, (¬ ∃ g : G, conjSub g J = L) → Commutes J L

theorem Thm4RBelow.mono {r m n : ℕ} (hmn : m ≤ n) (h : Thm4RBelow r n) : Thm4RBelow r m :=
  fun G _ _ hG Δ hΔ => h G (lt_of_lt_of_le hG hmn) Δ hΔ

@[expose] def TightSepAlpha {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
    IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥

section Cit3


@[expose] def TightSepLeafR' (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → TC.SepHyp (CoreAssembly.conjClass (tightCore R))

theorem tightSepLeafR_of_R' {r n : ℕ} (h : TightSepLeafR' r n) : TightSepLeafR r n :=
  fun Y _ _ R S t hL _ => h Y R S t hL

@[expose] def TightSepLeafRα (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → TightSepAlpha R t →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
