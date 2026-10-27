module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D4

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_isDihedralRot_of_isCyclic (hΩ : Assumption41 Ω) {J K R U V : Subgroup G}
    (hJ : J ∈ Ω) (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R) (hVJ : V ≤ J)
    (hV2 : IsPGroup 2 V) (hVc : IsCyclic V) (hcard : Nat.card V = Nat.card U) :
    ∃ T, IsSylowOf 2 T J ∧ IsDihedralRot V T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hVT⟩ := exists_isSylowOf_le hV2 hVJ
  obtain ⟨V', hV'⟩ := Assumption41.exists_rot hΩ hJ hT
  have hidx : V.relIndex T = 2 := by
    have h1 := Subgroup.relIndex_mul_card V T
    rw [inf_eq_left.mpr hVT, Assumption41.card_sylow_eq hΩ hJ hK hT hR, hU.card_eq,
      ← hcard] at h1
    have hpos : 0 < Nat.card V := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  exact ⟨T, hT, (hV'.eq_of_isCyclic hVT hVc hidx) ▸ hV'⟩

theorem card_eq_two_of_not_dStarAdj (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {J L V : Subgroup G} (hJ : J ∈ Ω) (hL : L ∈ Ω) (hJL : ¬ DStarAdj Ω L J)
    (hV : IsSylowOf 2 V (J ⊓ normalizer (L : Set G))) (hV1 : V ≠ ⊥) : Nat.card V = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, hVR⟩ := exists_isSylowOf_normalized hV.isPGroup (hV.le.trans inf_le_right)
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hL hR
  rcases lemma415 h22 hΩ hL hJ hR hU hV hV1 hVR with ⟨-, hJL', hLJ'⟩ | ⟨⟨e⟩, hcomm, -⟩ |
    ⟨h2, -⟩
  · exact absurd (dStarAdj_of_le_normalizer hΩ hL hJ hJL' hLJ') hJL
  · exfalso
    have hVc : IsCyclic V := by
      have := hU.isCyclic
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    have hcard : Nat.card V = Nat.card U := Nat.card_congr e.toEquiv
    obtain ⟨T, hT, hVT⟩ := exists_isDihedralRot_of_isCyclic hΩ hJ hL hR hU
      (hV.le.trans inf_le_left) hV.isPGroup hVc hcard
    apply hJL
    refine dStarAdj_of_commute hΩ hL hJ hR hU hT hVT fun u hu v hv => ?_
    have := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hv
    exact ((mem_centralizer_iff.mp this) u hu)
  · exact h2

theorem conj_eq_inv_of_not_dStarAdj (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {J L R U : Subgroup G} (hJ : J ∈ Ω) (hL : L ∈ Ω) (hJL : ¬ DStarAdj Ω L J) {t : G}
    (htJ : t ∈ J) (ht1 : t ≠ 1) (htt : t * t = 1) (htL : t ∈ normalizer (L : Set G))
    (hR : IsSylowOf 2 R L) (hU : IsDihedralRot U R) (htR : t ∈ normalizer (R : Set G)) :
    ∀ u ∈ U, t * u * t⁻¹ = u⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := zpowers t with hVdef
  have hV2 : IsPGroup 2 V := isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  have hVle : V ≤ J ⊓ normalizer (L : Set G) :=
    (zpowers_le).mpr (mem_inf.mpr ⟨htJ, htL⟩)
  have hVcard : Nat.card V = 2 := by
    rw [hVdef, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  obtain ⟨V₁, hV₁, hVV₁⟩ := exists_isSylowOf_le hV2 hVle
  have hV₁1 : V₁ ≠ ⊥ := by
    intro h
    rw [h] at hVV₁
    exact ht1 (mem_bot.mp (hVV₁ (mem_zpowers t)))
  have hV₁card := card_eq_two_of_not_dStarAdj h22 hΩ hJ hL hJL hV₁ hV₁1
  have hVV : V = V₁ := eq_of_le_of_card_ge hVV₁ (by rw [hV₁card, hVcard])
  have hVsyl : IsSylowOf 2 V (J ⊓ normalizer (L : Set G)) := hVV ▸ hV₁
  have hVR : V ≤ normalizer (R : Set G) := (zpowers_le).mpr htR
  have hV1 : V ≠ ⊥ := hVV ▸ hV₁1
  rcases lemma415 h22 hΩ hL hJ hR hU hVsyl hV1 hVR with ⟨-, hJL', hLJ'⟩ | ⟨⟨e⟩, hcomm, -⟩ |
    ⟨-, -, hinv⟩
  · exact absurd (dStarAdj_of_le_normalizer hΩ hL hJ hJL' hLJ') hJL
  · exfalso
    have : Nat.card V = Nat.card U := Nat.card_congr e.toEquiv
    have h4 := hU.four_le
    omega
  · exact hinv t (mem_zpowers t) ht1

end CFSG.ComponentClassification.Asc76.Sec4
