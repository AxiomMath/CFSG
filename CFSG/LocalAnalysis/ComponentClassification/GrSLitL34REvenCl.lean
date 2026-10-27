module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.Models.Blueprint

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder odd_tableOrder odd_gcd_of_odd_right
  odd_two_pow_sub_one odd_two_pow_add_one)

namespace L34R

set_option linter.unusedVariables false in
theorem models_lieModel_of_classical {X : Type} [Group X] {τ : StatedLieTag} {n p f : ℕ}
    (hτ : τ ∈ Blueprint.classicalTags) (hadm : StatedLieAdmissible τ n p f)
    (hm : Blueprint.LieModel X τ n p f) : Models.LieModel X τ n p f :=
  CFSG.Models.LieModel.of_blueprint hτ hm

theorem classical_even_tableOrder {τ : StatedLieTag} {n f : ℕ}
    (hτ : τ ∈ Blueprint.classicalTags) (hadm : StatedLieAdmissible τ n 2 f)
    (h2 : 2 ∣ tableOrder τ n 2 f) :
    (τ = .PSL ∧ n = 2 ∧ f = 2) ∨ (τ = .PSL ∧ n = 3 ∧ f = 1) ∨ (τ = .PSL ∧ n = 4 ∧ f = 1) ∨
      (τ = .PSL ∧ n = 3 ∧ f = 2) ∨ (τ = .PSU ∧ n = 4 ∧ f = 1) ∨ (τ = .PSU ∧ n = 6 ∧ f = 1) ∨
      (τ = .PSp ∧ n = 3 ∧ f = 1) ∨ (τ = .POmegaPlus ∧ n = 4 ∧ f = 1) := by
  have hf : 1 ≤ f := hadm.2.1
  by_contra hne
  refine (Nat.not_even_iff_odd.mpr ?_) (even_iff_two_dvd.mpr h2)
  simp only [Blueprint.classicalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_sub_one hf)) odd_one ?_
    unfold exceptionalOrders
    split <;> simp_all
  · refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_add_one hf)) odd_one ?_
    unfold exceptionalOrders
    split <;> simp_all
  · refine odd_tableOrder (odd_gcd_of_odd_right (odd_two_pow_sub_one hf)) odd_one ?_
    unfold exceptionalOrders
    split <;> simp_all
  · exact absurd rfl hadm.2.2.2
  · have hev : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hg : genericOrders .POmegaPlus n 2 f = (1, 1) := by
      simp [genericOrders, hev]
    refine odd_tableOrder (by rw [hg]; exact odd_one) (by rw [hg]; exact odd_one) ?_
    unfold exceptionalOrders
    split <;> simp_all
  · have hn : 4 ≤ n := hadm.2.2
    have hodd : Odd ((2 ^ f) ^ n + 1) :=
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by omega⟩).add_one
    refine odd_tableOrder (odd_gcd_of_odd_right hodd) odd_one ?_
    unfold exceptionalOrders
    split <;> simp_all

theorem card_mul_eq_of_lieModel (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hm : Blueprint.LieModel X t n p f) {d N : ℕ} (hd : lieOrderDivisor t n (p ^ f) = d)
    (hN : lieOrderNumerator t n (p ^ f) = N) : Nat.card X * d = N := by
  have h := (hO X t n p f hadm hm).2.1
  rwa [hd, hN] at h

theorem false_of_classical_outer (hO : LieOrderFormulasInput)
    (hR1 : EvenLieExcOuterL34Input) {S : Type} [Group S] [Finite S] {τ : StatedLieTag} {n f : ℕ}
    (hτ : τ ∈ Blueprint.classicalTags) (hadm : StatedLieAdmissible τ n 2 f)
    (hm : Blueprint.LieModel S τ n 2 f) (h2 : 2 ∣ tableOrder τ n 2 f) {σ : MulAut S}
    (hσ2 : orderOf σ = 2) (hσo : σ ∉ (MulAut.conj : S →* MulAut S).range) {P : Subgroup S}
    (h : ProperFixedComponent σ P) (htype : IsL34Type (P ⧸ Open.fusionZStar P)) : False := by
  have hPS : 20160 ∣ Nat.card S := by
    rw [← card_of_isL34Type htype]
    exact card_dvd_of_fusionZStar_equiv (Equiv.refl _)
  have hP : 20160 ∣ Nat.card P := by
    rw [← card_of_isL34Type htype]
    exact Subgroup.card_quotient_dvd_card _
  have hne : Nat.card S ≠ 20160 := fun hS =>
    h.2.2.2 ((Subgroup.card_eq_iff_eq_top P).mp
      (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card P) (hS ▸ hP)))
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hL : IsPComponent 2 L := h.2.2.1
  obtain ⟨eP⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
  have htypeL : IsL34Type (L ⧸ Open.fusionZStar L) :=
    LieType.CurtisTits.lieModel_of_mulEquiv eP htype
  rcases classical_even_tableOrder hτ hadm h2 with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have := card_mul_eq_of_lieModel hO hadm hm (d := 1) (N := 60) (by decide) (by decide)
    omega
  · have := card_mul_eq_of_lieModel hO hadm hm (d := 1) (N := 168) (by decide) (by decide)
    omega
  · have := card_mul_eq_of_lieModel hO hadm hm (d := 1) (N := 20160) (by decide) (by decide)
    omega
  · have := card_mul_eq_of_lieModel hO hadm hm (d := 3) (N := 60480) (by decide) (by decide)
    omega
  · have := card_mul_eq_of_lieModel hO hadm hm (d := 1) (N := 25920) (by decide) (by decide)
    omega
  · exact hR1 S .PSU 6 1 (by simp) hm σ hσ2 hσo L hL htypeL
  · obtain ⟨g, hg⟩ := LocalAnalysis.ComponentInitial.BinarySymplecticSix.exists_eq_conj_of_lieModel
      hm σ
    exact hσo ⟨g, hg.symm⟩
  · exact hR1 S .POmegaPlus 4 1 (by simp) hm σ hσ2 hσo L hL htypeL

end L34R

end CFSG.ComponentClassification.GrSLit
