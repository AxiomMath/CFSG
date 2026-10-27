module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClSpInner
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClSpFieldMain

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem u42_sp_fieldAut_not_inner {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (A : gsp r K) {τ : K ≃+* K} (hτ : τ ≠ 1) :
    conjAut r K A * fieldAut r K τ ∉ inner (StatedProj (StatedSp r K)) := by
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := proj_surjective x
  have h1 : conjAut r K ⟨g, statedSp_le_gsp g.2⟩ = conjAut r K A * fieldAut r K τ := by
    rw [conjAut_statedSp]
    exact hx
  have h2 : conjAut r K (⟨g, statedSp_le_gsp g.2⟩⁻¹ * A) * fieldAut r K τ = 1 := by
    rw [map_mul, map_inv, mul_assoc, ← h1]
    exact inv_mul_cancel _
  exact hτ ((CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
    hodd hr).2.1 _ τ |>.1 h2).1

theorem u42_psp43_false {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {σ : MulAut (StatedProj (StatedSp 2 K))} (hσ : orderOf σ = 2)
    {J : Subgroup ↥(fixedSubgroup σ)} (hJ : U42Hyp σ J) : False := by
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three (le_refl 1)
    (by rw [hK]; norm_num)
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have h2 := Ring.two_ne_zero hchar
  have hP := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (K := K) (n := 2) h2
    (by norm_num)
  have hprod : ∏ j ∈ Finset.Icc 1 2, (Nat.card K ^ (2 * j) - 1) =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  rw [hprod, hK] at hP
  norm_num at hP
  have hP' : Nat.card (StatedProj (StatedSp 2 K)) = 25920 := by omega
  have hle := Subgroup.card_le_card_group (fixedSubgroup σ)
  have hdvd := hJ.dvd_card
  have hpos : 0 < Nat.card ↥(fixedSubgroup σ) := Nat.card_pos
  have hge := Nat.le_of_dvd hpos hdvd
  have htop : fixedSubgroup σ = ⊤ := Subgroup.eq_top_of_card_eq _ (by omega)
  have hone : σ = 1 := by
    ext x
    have hx : x ∈ fixedSubgroup σ := htop ▸ Subgroup.mem_top x
    exact hx
  rw [hone, orderOf_one] at hσ
  exact absurd hσ (by norm_num)

theorem oddU42Free_PSp : OddU42Free .PSp := by
  apply oddU42Free_of_concrete
  intro S _ _ n f hadm hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel' hadm hm
  refine ⟨StatedProj (StatedSp n K), inferInstance, inferInstance, e, ?_⟩
  intro σ J hσ hJ
  have hn : 2 ≤ n := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  by_cases hsmall : n = 2 ∧ f = 1
  · obtain ⟨hn2, hf1⟩ := hsmall
    subst hn2 hf1
    exact u42_psp43_false (by rw [hK]; norm_num) hσ hJ
  have h2f : n = 2 → 2 ≤ f := fun hn2 => by
    by_contra hlt
    exact hsmall ⟨hn2, by omega⟩
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have hβ2 : σ * σ = 1 := by
    have h2 := pow_orderOf_eq_one σ
    rw [hσ] at h2
    rw [← pow_two]
    exact h2
  have hβ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨A, τ, hAτ, hτ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar hn).2.2 σ hβ2 hβ1
  by_cases hτ : τ = 1
  · subst hτ
    rw [map_one, mul_one] at hAτ
    subst hAτ
    exact u42_sp_inner_false hn hf h2f hK A hσ hJ
  · exact u42_sp_field_false hn hf hK A τ hAτ hτ2 hτ d hd
      (hAτ ▸ u42_sp_fieldAut_not_inner hn hchar A hτ) hJ

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
