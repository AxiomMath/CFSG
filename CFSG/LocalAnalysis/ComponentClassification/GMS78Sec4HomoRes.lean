module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Prelim

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G} {f : ℕ}

theorem isSylowOf_inf_sup (h : Sec3 G L T) :
    IsSylowOf 2 (T ⊓ (L ⊔ centralizer (L : Set G))) (L ⊔ centralizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLKN : L ⊔ centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    sup_le le_normalizer h.centralizer_le_normalizer
  have hLKn : normalizer (L : Set G) ≤
      normalizer ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup hx (h.normalizer_le_normalizer_centralizer hx)
  exact h.sylow.inf_of_le_normalizer hLKN hLKn

theorem exists_conj_mem_V_of_mem_sup (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {x : G}
    (hx : x ∈ L ⊔ centralizer (L : Set G)) (hxL : x ∉ L) (hxx : x * x = 1) :
    ∃ k : G, k * x * k⁻¹ ∈ gmsV L T ∧ k * x * k⁻¹ ∉ gmsA L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (zpowers x) := by
    have h2 : orderOf x ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, hxx])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨k, hk, hkx⟩ := exists_conj_le_of_isSylowOf h.isSylowOf_inf_sup (zpowers_le.mpr hx) hQ
  have hV : gmsV L T = T ⊓ (L ⊔ centralizer (L : Set G)) := by
    rw [h.inf_sup_eq]
    show gmsA L T ⊔ _ = _
    rw [h.gmsA_eq_of_psl2 hf e]
  refine ⟨k, hV ▸ hkx x (mem_zpowers x), fun hA => hxL ?_⟩
  have hkL : k ∈ normalizer (L : Set G) := (sup_le le_normalizer h.centralizer_le_normalizer) hk
  have hA' : k * x * k⁻¹ ∈ T ⊓ L := h.gmsA_eq_of_psl2 hf e ▸ hA
  exact (mem_normalizer_iff.mp hkL x).mpr (mem_inf.mp hA').2

theorem conj_mem_of_mem_sup (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {q : ℕ} (h313 : Lemma313 L T q) {a y : G}
    (ha : a ∈ gmsA L T) (haa : a * a = 1) (hy : y * a * y⁻¹ ∈ L ⊔ centralizer (L : Set G)) :
    y * a * y⁻¹ ∈ L := by
  by_contra hn
  obtain ⟨k, hkV, hkA⟩ := h.exists_conj_mem_V_of_mem_sup hf e hy hn (by
    calc y * a * y⁻¹ * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [haa]; group)
  have h1 : (k * y) * a * (k * y)⁻¹ = k * (y * a * y⁻¹) * k⁻¹ := by group
  rw [← h1] at hkV hkA
  exact hkA (h313.stronglyClosed a ha _ hkV)

theorem card_le_two_mul_inf_rightConjugate
    (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {q : ℕ} (h313 : Lemma313 L T q) {w y : G}
    (hw : y * w * y⁻¹ ∈ centralizer (L : Set G)) (hw1 : w ≠ 1) (hww : w * w = 1)
    {E : Subgroup G} (hEA : E ≤ gmsA L T) (hEw : E ≤ centralizer ({w} : Set G)) :
    Nat.card E ≤ 2 * Nat.card (E ⊓ rightConjugate L y : Subgroup G) := by
  have hZ := odd_card_center_of_psl2 h.hyp.standard.1.1 hf e
  have hAel : IsElemAbelian 2 (gmsA L T) := by
    rw [h.gmsA_eq_of_psl2 hf e]
    exact isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁
  have hEel : IsElemAbelian 2 E := isElemAbelian_of_le hAel hEA
  have hB := (rankTwoBenderType_iff.mp h.hyp.bender).fusionIsBenderGroup
  set c := MulAut.conj y with hc
  set E' := E.map c.toMonoidHom with hE'
  have hE'el : IsElemAbelian 2 E' := isElemAbelian_map _ hEel
  have ht1 : y * w * y⁻¹ ≠ 1 := fun h1 => hw1 (conj_eq_one_iff.mp h1)
  have htt : y * w * y⁻¹ * (y * w * y⁻¹) = 1 := by
    calc y * w * y⁻¹ * (y * w * y⁻¹) = y * (w * w) * y⁻¹ := by group
      _ = 1 := by rw [hww]; group
  have hE'N : E' ≤ normalizer (L : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    refine h.centralizer_le_normalizer_of_mem hw ht1 htt (mem_centralizer_singleton_iff.mpr ?_)
    have haw : a * w = w * a := mem_centralizer_singleton_iff.mp (hEw ha)
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * a * y⁻¹ * (y * w * y⁻¹) = y * (a * w) * y⁻¹ := by group
      _ = y * (w * a) * y⁻¹ := by rw [haw]
      _ = y * w * y⁻¹ * (y * a * y⁻¹) := by group
  have h1 := card_le_two_mul_inf h.hyp.standard.1.1 hB hE'N hE'el
  have h2 : E' ⊓ (L ⊔ centralizer (L : Set G)) ≤ (E ⊓ rightConjugate L y).map c.toMonoidHom := by
    rintro _ ⟨⟨a, ha, rfl⟩, hLK⟩
    refine ⟨a, mem_inf.mpr ⟨ha, (mem_rightConjugate_iff _ _ _).mpr ?_⟩, rfl⟩
    have haa : a * a = 1 := by rw [← sq]; exact hAel.2 a (hEA ha)
    exact h.conj_mem_of_mem_sup hf e h313 (hEA ha) haa hLK
  have h3 := card_le_of_le h2
  rw [card_map_of_injective c.injective] at h3
  have h4 : Nat.card E' = Nat.card E := card_map_of_injective c.injective
  omega

end Sec3

end CFSG.ComponentClassification.GMS78
