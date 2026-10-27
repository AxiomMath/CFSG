module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedNormal

public section

namespace CFSG.ComponentClassification.CatFC.OmegaSmall

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

theorem card_mul_card_le_card_inf_mul_card {X : Type*} [Group X] [Finite X]
    (N F : Subgroup X) :
    Nat.card N * Nat.card F ≤ Nat.card (N ⊓ F : Subgroup X) * Nat.card X := by
  have hN := Subgroup.card_mul_index N
  have hF := Subgroup.card_mul_index F
  have hI := Subgroup.card_mul_index (N ⊓ F)
  have hle := Subgroup.index_inf_le (H := N) (K := F)
  have hNi : 0 < N.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hFi : 0 < F.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hX : 0 < Nat.card X := Nat.card_pos
  have h1 : (Nat.card N * Nat.card F) * (N.index * F.index) =
      Nat.card X * Nat.card X := by
    calc (Nat.card N * Nat.card F) * (N.index * F.index) =
        (Nat.card N * N.index) * (Nat.card F * F.index) := by ring
      _ = Nat.card X * Nat.card X := by rw [hN, hF]
  have h2 : Nat.card X * Nat.card X ≤
      (Nat.card (N ⊓ F : Subgroup X) * Nat.card X) * (N.index * F.index) := by
    calc Nat.card X * Nat.card X = (Nat.card (N ⊓ F : Subgroup X) * (N ⊓ F).index) *
          Nat.card X := by rw [hI]
      _ = (Nat.card (N ⊓ F : Subgroup X) * Nat.card X) * (N ⊓ F).index := by ring
      _ ≤ (Nat.card (N ⊓ F : Subgroup X) * Nat.card X) * (N.index * F.index) :=
          Nat.mul_le_mul_left _ hle
  exact Nat.le_of_mul_le_mul_right (h1 ▸ h2) (Nat.mul_pos hNi hFi)

theorem card_eq_card_range_mul_card_ker {G H : Type*} [Group G] [Group H] [Finite G]
    (φ : G →* H) : Nat.card G = Nat.card φ.range * Nat.card φ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]

theorem card_subgroupOf_eq_card_inf {X : Type*} [Group X] (N F : Subgroup X) :
    Nat.card (N.subgroupOf F) = Nat.card (N ⊓ F : Subgroup X) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ F ≤ F)).toEquiv

theorem card_fixed_normalCentralQuotient_ge {X : Type*} [Group X] [Finite X]
    (N Z : Subgroup X) [Z.Normal] (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z) :
    Nat.card (N ⧸ Z.subgroupOf N) * Nat.card (fixedSubgroup ψ) ≤
      Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) * Nat.card X := by
  have hZ'inv := restricted_central_invariant N Z ψ hN hZ
  set P := fixedProjection (Z.subgroupOf N) (restrictAutomorphism N ψ hN) hZ'inv with hP
  have hker := fixedProjection_kernel (Z.subgroupOf N) (restrictAutomorphism N ψ hN) hZ'inv
  have h1 := card_eq_card_range_mul_card_ker P
  have h2 : Nat.card P.ker ≤ Nat.card (Z.subgroupOf N) := by
    rw [hP, hker]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨x.val.val, x.property⟩ : Z.subgroupOf N)) ?_
    intro x y hxy
    have h := congrArg (fun z : Z.subgroupOf N => (z : N)) hxy
    exact Subtype.ext (Subtype.ext h)
  have h3 : Nat.card P.range ≤
      Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) :=
    Subgroup.card_le_card_group _
  have h4 : Nat.card (fixedSubgroup (restrictAutomorphism N ψ hN)) =
      Nat.card (N ⊓ fixedSubgroup ψ : Subgroup X) := by
    rw [Nat.card_congr (fixedNormalEquiv N ψ hN).toEquiv, card_subgroupOf_eq_card_inf]
  have h5 : Nat.card N = Nat.card (N ⧸ Z.subgroupOf N) * Nat.card (Z.subgroupOf N) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf N)
  have h6 := card_mul_card_le_card_inf_mul_card N (fixedSubgroup ψ)
  have hZpos : 0 < Nat.card (Z.subgroupOf N) := Nat.card_pos
  have h7 : Nat.card (fixedSubgroup (restrictAutomorphism N ψ hN)) ≤
      Nat.card (Z.subgroupOf N) *
        Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) := by
    rw [h1]
    calc Nat.card P.range * Nat.card P.ker ≤
        Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) *
          Nat.card (Z.subgroupOf N) := Nat.mul_le_mul h3 h2
      _ = _ := mul_comm _ _
  have h8 : Nat.card (N ⧸ Z.subgroupOf N) * Nat.card (fixedSubgroup ψ) *
      Nat.card (Z.subgroupOf N) ≤
      Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) * Nat.card X *
        Nat.card (Z.subgroupOf N) := by
    calc Nat.card (N ⧸ Z.subgroupOf N) * Nat.card (fixedSubgroup ψ) *
          Nat.card (Z.subgroupOf N) =
        Nat.card N * Nat.card (fixedSubgroup ψ) := by rw [h5]; ring
      _ ≤ Nat.card (N ⊓ fixedSubgroup ψ : Subgroup X) * Nat.card X := h6
      _ ≤ (Nat.card (Z.subgroupOf N) *
          Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ))) * Nat.card X := by
          rw [← h4]; exact Nat.mul_le_mul_right _ h7
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h8 hZpos

end CFSG.ComponentClassification.CatFC.OmegaSmall
