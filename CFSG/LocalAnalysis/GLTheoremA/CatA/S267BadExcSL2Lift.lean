module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2Hq
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankCarrier
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped MatrixGroups

section Hq

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem false_of_hq_of_lift {p q r : ℕ} (hBr : CFSG.Open.pRank p B < r)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B)
    {F : Type} [Group F] (eF : PSimple p S ≃* F)
    (hlift : ∀ (X : Type) [Group X] [Finite X] (φ : X →* F), Function.Surjective φ →
      r ≤ GLATwoLocalRank q X) : False := by
  obtain ⟨K', _, _, ⟨eK⟩, hrk⟩ := hHq
  obtain ⟨φ, hφ⟩ := exists_surjective_of_pquot eK eF
  have := hlift K' φ hφ
  omega

theorem pRank_le_of_card_le_pow {p n : ℕ} (hp : p.Prime) (hB : Nat.card B ≤ p ^ n) :
    CFSG.Open.pRank p B ≤ n :=
  CFSG.SectionRank.pRank_le hp.one_lt fun _ hEB _ => (Subgroup.card_le_of_le hEB).trans hB

end Hq

section SL2

theorem le_twoLocalRank_of_SL2 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {L : Type} [Field L]
    [Finite L] {m r : ℕ} (hm : 3 ≤ m) (hL : Nat.card L = q ^ m) (hrm : r ≤ m)
    (hr : r ^ 2 / 4 < 2 * m) {F : Type} [Group F] (φ : SL(2, L) →* F)
    (hφ : Function.Injective φ) {X : Type} [Group X] [Finite X] (ψ : X →* F)
    (hψ : Function.Surjective ψ) : r ≤ GLATwoLocalRank q X := by
  haveI : Fintype L := Fintype.ofFinite L
  haveI : Fact q.Prime := ⟨hq⟩
  have hchar : CharP L q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hL])
  have h2 : (2 : L) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq L q]; exact hq2)
  set J : Subgroup F := φ.range with hJ
  let eJ : SL(2, L) ≃* ↥J := MonoidHom.ofInjective hφ
  set t : F := φ (-1) with ht
  have ht2 : t ^ 2 = 1 := by rw [ht, ← map_pow, neg_one_sq, map_one]
  have hneg : (-1 : SL(2, L)) ≠ 1 := by
    intro h
    have h00 := congrArg (fun A : SL(2, L) => (A : Matrix (Fin 2) (Fin 2) L) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h00
    apply h2
    linear_combination -h00
  have ht1 : t ≠ 1 := fun h => hneg (hφ (by rw [← ht, h, map_one]))
  have hJU : J ≤ Subgroup.normalizer (Subgroup.zpowers t : Set F) := by
    rintro _ ⟨A, rfl⟩
    refine CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.mem_normalizer_of_forall_comm
      fun k hk => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hc : φ A * t = t * φ A := by
      rw [ht, ← map_mul, ← map_mul, mul_neg_one, neg_one_mul]
    exact (Commute.zpow_right hc n).eq
  refine CFSG.LocalAnalysis.GLTheoremA.S267.HqRank.le_twoLocalRank_of_section hq
    (CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.isPGroup_two_zpowers_of_sq ht2)
    (CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.zpowers_ne_bot_of_ne_one ht1) hJU
    (fun X' _ _ φ' hφ' => ?_) ψ hψ
  exact CFSG.LocalAnalysis.GLTheoremA.S267.HqRank.le_pRank_of_surj_SL2 hq hq2
    (by rw [← Nat.card_eq_fintype_card]; exact hL) hm hrm hr (eJ.symm.toMonoidHom.comp φ')
    (eJ.symm.surjective.comp hφ')

theorem le_twoLocalRank_of_SL2_cat (d : TauCeti.ValidLieTypeIndex) {q f : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hfo : d.fieldOrder = q ^ f) (hf : 3 ≤ f) {r : ℕ} (hrf : r ≤ f)
    (hr : r ^ 2 / 4 < 2 * f)
    (φ : SL(2, ↥(TauCeti.ValidLieTypeIndex.fixedField d)) →* (TauCeti.CFSGIndex.lie d).Group)
    (hφ : Function.Injective φ) {X : Type} [Group X] [Finite X]
    (ψ : X →* (TauCeti.CFSGIndex.lie d).Group) (hψ : Function.Surjective ψ) :
    r ≤ GLATwoLocalRank q X := by
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField d) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank.finite_fixedField d
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d) = q ^ f := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField, hfo]
  exact le_twoLocalRank_of_SL2 hq hq2 hf hcard hrf hr φ hφ ψ hψ

end SL2

section Cat

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank

theorem le_twoLocalRank_cat_F4 (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 Q).Valid)
    (hQ2 : Q.p ≠ 2) (hf : 3 ≤ Q.exponent) {r : ℕ} (hrf : r ≤ Q.exponent)
    (hr : r ^ 2 / 4 < 2 * Q.exponent) {X : Type} [Group X] [Finite X]
    (ψ : X →* (TauCeti.CFSGIndex.lie ⟨.F4 Q, hv⟩).Group) (hψ : Function.Surjective ψ) :
    r ≤ GLATwoLocalRank Q.p X := by
  obtain ⟨φ, hφ, -⟩ := f4_commuting_SL2 Q hv
  exact le_twoLocalRank_of_SL2_cat ⟨.F4 Q, hv⟩ Q.prime_p hQ2
    ((TauCeti.LieTypeIndex.fieldOrder_F4 Q).trans (TauCeti.PrimePower.card_def Q)) hf hrf hr (φ 0)
    (hφ 0) ψ hψ

theorem le_twoLocalRank_cat_E6 (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hQ2 : Q.p ≠ 2) (hf : 3 ≤ Q.exponent) {r : ℕ} (hrf : r ≤ Q.exponent)
    (hr : r ^ 2 / 4 < 2 * Q.exponent) {X : Type} [Group X] [Finite X]
    (ψ : X →* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hψ : Function.Surjective ψ) :
    r ≤ GLATwoLocalRank Q.p X := by
  obtain ⟨φ, hφ, -⟩ := e6_commuting_SL2' Q hv
  exact le_twoLocalRank_of_SL2_cat ⟨.E6 Q, hv⟩ Q.prime_p hQ2
    ((TauCeti.LieTypeIndex.fieldOrder_E6 Q).trans (TauCeti.PrimePower.card_def Q)) hf hrf hr (φ 0)
    (hφ 0) ψ hψ

theorem le_twoLocalRank_cat_twistedE6 (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid) (hQ2 : Q.p ≠ 2) (hf : 3 ≤ Q.exponent)
    {r : ℕ} (hrf : r ≤ Q.exponent) (hr : r ^ 2 / 4 < 2 * Q.exponent) {X : Type} [Group X]
    [Finite X] (ψ : X →* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group)
    (hψ : Function.Surjective ψ) : r ≤ GLATwoLocalRank Q.p X := by
  obtain ⟨φ, hφ, -⟩ := twistedE6_commuting_SL2' Q hv
  exact le_twoLocalRank_of_SL2_cat ⟨.twistedE6 Q, hv⟩ Q.prime_p hQ2
    ((TauCeti.LieTypeIndex.fieldOrder_twistedE6 Q).trans (TauCeti.PrimePower.card_def Q)) hf hrf hr (φ 0)
    (hφ 0) ψ hψ

theorem le_twoLocalRank_cat_E7 (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 Q).Valid)
    (hQ2 : Q.p ≠ 2) (hf : 3 ≤ Q.exponent) {r : ℕ} (hrf : r ≤ Q.exponent)
    (hr : r ^ 2 / 4 < 2 * Q.exponent) {X : Type} [Group X] [Finite X]
    (ψ : X →* (TauCeti.CFSGIndex.lie ⟨.E7 Q, hv⟩).Group) (hψ : Function.Surjective ψ) :
    r ≤ GLATwoLocalRank Q.p X := by
  obtain ⟨φ, hφ, -⟩ := e7_commuting_SL2' Q hv
  exact le_twoLocalRank_of_SL2_cat ⟨.E7 Q, hv⟩ Q.prime_p hQ2
    ((TauCeti.LieTypeIndex.fieldOrder_E7 Q).trans (TauCeti.PrimePower.card_def Q)) hf hrf hr (φ 0)
    (hφ 0) ψ hψ

end Cat

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
