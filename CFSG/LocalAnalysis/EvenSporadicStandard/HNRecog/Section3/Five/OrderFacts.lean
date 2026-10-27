module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.ElevenCent

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_orderOf_eleven (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) : ∃ ω : G, ω ∈ Gx a ∧ orderOf ω = 11 := by
  have hcard := card_centralizer_a_of_isF5Type hI h
  have hdvd : 11 ∣ Nat.card ↥(Gx a) := by rw [hcard]; norm_num
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Gx a)) 11 hdvd
  exact ⟨(g : G), g.2, (Subgroup.orderOf_coe g).trans hg⟩

theorem isConj_of_orderOf_eleven (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z)
    (hcard : Nat.card G = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) {ω ω' : G} (hω : orderOf ω = 11)
    (hω' : orderOf ω' = 11) : IsConj ω ω' := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hpcard : padicValNat 11 (Nat.card G) = 1 := by
    have hk : 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 19 ≠ 0 := by norm_num
    rw [hcard, show 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19
        = 11 * (2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 19) by ring,
      padicValNat.mul (p := 11) (show (11 : ℕ) ≠ 0 by norm_num) hk, padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (p := 11)
        (by norm_num : ¬ 11 ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 19), add_zero]
  obtain ⟨ω₀, hω₀a, hω₀⟩ := exists_orderOf_eleven hI h
  have hT₀le : Subgroup.zpowers ω₀ ≤ Gx a := Subgroup.zpowers_le.mpr hω₀a
  have hT₀card : Nat.card ↥(Subgroup.zpowers ω₀) =
      11 ^ padicValNat 11 (Nat.card ↥(⊤ : Subgroup G)) := by
    rw [Subgroup.card_top, hpcard, pow_one, Nat.card_zpowers, hω₀]
  obtain ⟨g, -, hg⟩ := exists_conj_mem_of_card_eq (p := 11) (K := ⊤)
    (T₀ := Subgroup.zpowers ω₀) le_top hT₀card (Subgroup.mem_top ω) hω
  obtain ⟨g', -, hg'⟩ := exists_conj_mem_of_card_eq (p := 11) (K := ⊤)
    (T₀ := Subgroup.zpowers ω₀) le_top hT₀card (Subgroup.mem_top ω') hω'
  have hω₁a : g⁻¹ * ω * g ∈ Gx a := hT₀le hg
  have hω₁'a : g'⁻¹ * ω' * g' ∈ Gx a := hT₀le hg'
  have hω₁ord : orderOf (g⁻¹ * ω * g) = 11 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) ω
    rw [MulAut.conj_apply, inv_inv] at h1
    rw [h1, hω]
  have hω₁'ord : orderOf (g'⁻¹ * ω' * g') = 11 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g'⁻¹) ω'
    rw [MulAut.conj_apply, inv_inv] at h1
    rw [h1, hω']
  obtain ⟨E, hE⟩ := h.cent_a
  have hconjH : IsConj (⟨g⁻¹ * ω * g, hω₁a⟩ : ↥(Gx a))
      ⟨g'⁻¹ * ω' * g', hω₁'a⟩ :=
    hS.eleven_one_class ↥(Gx a) E hE _ _
      ((Subgroup.orderOf_mk (g⁻¹ * ω * g) hω₁a).trans hω₁ord)
      ((Subgroup.orderOf_mk (g'⁻¹ * ω' * g') hω₁'a).trans hω₁'ord)
  have hconjG : IsConj (g⁻¹ * ω * g) (g'⁻¹ * ω' * g') := by
    have := (Gx a).subtype.map_isConj hconjH
    simpa using this
  have hωω₁ : IsConj ω (g⁻¹ * ω * g) := isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩
  have hω₁'ω' : IsConj (g'⁻¹ * ω' * g') ω' :=
    (isConj_iff.2 ⟨g'⁻¹, by rw [inv_inv]⟩).symm
  exact hωω₁.trans (hconjG.trans hω₁'ω')

theorem isShapeCentralizerEleven_of_orderOf (hI : TwoHSInterface) (hS : SuborbitFacts)
    (hU : U35Facts) {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hcard : Nat.card G = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) (hGam : GammaFacts a z)
    (hT7 : TableVIIFacts a z) (hFive : FiveFacts a z) {ω : G} (hω : orderOf ω = 11) :
    IsShapeCentralizerEleven ↥(Gx ω) := by
  obtain ⟨ω₀, hω₀a, hω₀⟩ := exists_orderOf_eleven hI h
  have hshape₀ := isShapeCentralizerEleven_of_mem_Gx hI hU h hcard hGam hT7 hFive hω₀a hω₀
  have hconj : IsConj ω₀ ω := isConj_of_orderOf_eleven hI hS h hcard hω₀ hω
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  exact ⟨(centralizerMulEquiv (MulAut.conj c)
    (by simpa [MulAut.conj_apply] using hc)).symm.trans hshape₀.some⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
