module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Q1
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Rep

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_and_isTwoNilpotent_oddCoreIn_sup {P U : Subgroup G} (hUP : U ≤ P)
    (hU : IsPGroup 2 U) :
    IsSylowOf 2 U (oddCoreIn P ⊔ U) ∧ IsTwoNilpotent (oddCoreIn P ⊔ U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreIn P with hO
  have hUO : U ≤ normalizer (O : Set G) := hUP.trans (le_normalizer_oddCoreIn P)
  have hOU : O ⊓ U = ⊥ := oddCoreIn_inf_eq_bot hU
  have hcard : Nat.card (O ⊔ U : Subgroup G) = Nat.card O * Nat.card U :=
    card_sup_of_le_normalizer hUO hOU
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU
  have hOodd : Nat.card O % 2 = 1 := Nat.odd_iff.mp (odd_card_oddCoreIn P)
  have hrel : O.relIndex (O ⊔ U) = 2 ^ m := by
    rw [relIndex_sup_of_le_normalizer hUO]
    have h1 := relIndex_mul_card O U
    rw [hOU, card_bot, mul_one, hm] at h1
    exact h1
  refine ⟨isSylowOf_of_card le_sup_right ?_, ⟨O, le_sup_left, ?_, odd_card_oddCoreIn P, m, hrel⟩⟩
  · have hnd : ¬ 2 ∣ Nat.card O := by omega
    rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, zero_add, hm, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one]
  · exact (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le le_normalizer hUO)

theorem normalizer_le_normalizer_oddCoreIn_sup_omegaOne {P R : Subgroup G}
    (hR : IsSylowOf 2 R P) (hRc : IsMulCommutative R)
    (h2 : ∀ k ∈ P, ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ oddCoreIn P ⊔ R) :
    normalizer (P : Set G) ≤ normalizer ((oddCoreIn P ⊔ omegaOne R : Subgroup G) : Set G) := by
  set O := oddCoreIn P with hOdef
  have hRO : R ≤ normalizer (O : Set G) := hR.le.trans (le_normalizer_oddCoreIn P)
  intro w hw
  refine mem_normalizer_of_map_conj_le ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨o, ho, rfl⟩
    exact mem_sup_left ((mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn P hw) o).mp ho)
  · rintro _ ⟨u, hu0, rfl⟩
    have hu := (mem_omegaOne_iff hRc).mp hu0
    have hxP : w * u * w⁻¹ ∈ P := (mem_normalizer_iff.mp hw u).mp (hR.le hu.1)
    have hx2 : (w * u * w⁻¹) ^ 2 = 1 := by rw [conj_pow, hu.2]; group
    have hxOR := h2 _ hxP 1 (by simpa using hx2)
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left O R hRO] at hxOR
    obtain ⟨o, ho, t, ht, hot⟩ := hxOR
    have hot' : o * t = w * u * w⁻¹ := hot
    have ht2 : t ^ 2 = 1 := by
      have h1 : t ^ 2 ∈ O := by
        have hx2' : (o * t) * (o * t) = 1 := by rw [hot', ← sq, hx2]
        have heq : t ^ 2 = (t * o⁻¹ * t⁻¹) * o⁻¹ * ((o * t) * (o * t)) := by rw [sq]; group
        rw [heq, hx2', mul_one]
        exact O.mul_mem ((mem_normalizer_iff.mp (hRO ht) _).mp (O.inv_mem ho)) (O.inv_mem ho)
      have h2' : t ^ 2 ∈ O ⊓ R := ⟨h1, R.pow_mem ht 2⟩
      rwa [hOdef, oddCoreIn_inf_eq_bot hR.isPGroup, mem_bot] at h2'
    change (MulAut.conj w) u ∈ _
    rw [MulAut.conj_apply, ← hot']
    exact mul_mem (mem_sup_left ho) (mem_sup_right (mem_omegaOne ht ht2))

theorem exists_twoNilpotent_tightlyEmbedded (h75 : Asc75Theorem4) {P R : Subgroup G}
    (hP : TightlyEmbedded P) (hR : IsSylowOf 2 R P) (hRc : IsMulCommutative R) (hR1 : R ≠ ⊥)
    (hL1 : twoPrimeLayerIn P ≠ oddCoreIn P →
      ¬ NormalIn (twoPrimeLayerIn P) (twoPrimeLayerIn (⊤ : Subgroup G))) :
    ∃ Q : Subgroup G, Q ≤ P ∧ IsSylowOf 2 (omegaOne R) Q ∧ IsTwoNilpotent Q ∧
      TightlyEmbedded Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUR : omegaOne R ≤ R := omegaOne_le R
  have hUp : IsPGroup 2 (omegaOne R) := hR.isPGroup.to_le hUR
  have hU1 : omegaOne R ≠ ⊥ := by
    have h2R : 2 ∣ Nat.card R := (even_card_of_isPGroup hR.isPGroup hR1).two_dvd
    obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2R
    rw [Subgroup.orderOf_mk] at hx2
    intro hbot
    have hxU : x ∈ omegaOne R := mem_omegaOne hx (by rw [← hx2]; exact pow_orderOf_eq_one x)
    rw [hbot, mem_bot] at hxU
    rw [hxU, orderOf_one] at hx2
    norm_num at hx2
  have hTE : ∀ Q : Subgroup G, Q ≤ P → omegaOne R ≤ Q →
      normalizer (P : Set G) ≤ normalizer (Q : Set G) → TightlyEmbedded Q := by
    intro Q hQP hUQ hN
    refine ⟨even_iff_two_dvd.mpr ((even_card_of_isPGroup hUp hU1).two_dvd.trans
      (card_dvd_of_le hUQ)), fun x hx => ?_⟩
    have hxP : x ∉ normalizer (P : Set G) := fun h => hx (hN h)
    exact (hP.2 x hxP).of_dvd_nat
      (card_dvd_of_le (inf_le_inf hQP (rightConjugate_le_rightConjugate hQP x)))
  by_cases hL : twoPrimeLayerIn P = oddCoreIn P
  · have hlayer := (twoPrimeLayerIn_eq_oddCoreIn_iff P).mp hL
    have h2 := twoElements_le_of_layer_eq_bot' hR hRc hlayer
    obtain ⟨hsyl, hnil⟩ := isSylowOf_and_isTwoNilpotent_oddCoreIn_sup (hUR.trans hR.le) hUp
    have hQP : oddCoreIn P ⊔ omegaOne R ≤ P := sup_le (oddCoreIn_le P) (hUR.trans hR.le)
    exact ⟨_, hQP, hsyl, hnil, hTE _ hQP le_sup_right
      (normalizer_le_normalizer_oddCoreIn_sup_omegaOne hR hRc h2)⟩
  · rcases h75 G P hP hL with h1 | ⟨h1, -⟩ | ⟨g, hg, T, hT, hTN, n, hn, φ, hφ, hker⟩
    · exact absurd h1 (hL1 hL)
    · exact (false_of_pRank_twoPrimeLayerIn_eq_one' hR hRc hL h1).elim
    · have hRe := isElemAbelian_of_caseD hP hR hRc hg hT hTN rfl hn φ hφ hker
      have hUeq : omegaOne R = R := le_antisymm hUR (le_omegaOne hRe.2)
      obtain ⟨hTE', -⟩ := lemma21_caseD hP hR hRe hg hT hTN rfl hn φ hφ hker
      obtain ⟨hsyl, hnil⟩ := isSylowOf_and_isTwoNilpotent_oddCoreIn_sup hR.le hR.isPGroup
      exact ⟨oddCoreIn P ⊔ R, sup_le (oddCoreIn_le P) hR.le, by rw [hUeq]; exact hsyl, hnil, hTE'⟩

end CFSG.ComponentClassification.Asc76.Sec5
