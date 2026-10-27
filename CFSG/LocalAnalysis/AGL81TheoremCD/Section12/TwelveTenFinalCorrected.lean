module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenFinalReduction
public import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenAssembly

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

@[expose] def TwelveTenFinalA' (M H Q : Subgroup G) (p : ℕ) : Prop :=
  ∃ E D : Subgroup G,
    E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      rankThreeGamma 1 p E ≤ M ∧
      IsThreeOnePlusTwo ↥D ∧ D ≤ Q

@[expose] def TwelveTenFinalB' (M H Q : Subgroup G) (p : ℕ) : Prop :=
  ∀ E D : Subgroup G,
    E ≤ Q → IsElemAbelian p E → Nat.card E = p ^ 2 →
      rankThreeGamma 1 p E ≤ M →
      IsThreeOnePlusTwo ↥D → D ≤ Q →
      ∀ x : G, x ∈ kSub p M H ⊓ Subgroup.normalizer (D : Set G) → x ∉ M →
        IsL3TwoPow 1 (↥(centralizerInJ M H ((E ⊓ D).map (MulAut.conj x).toMonoidHom)) ⧸
          pCore 2 ↥(centralizerInJ M H ((E ⊓ D).map (MulAut.conj x).toMonoidHom)))

theorem inf_ne_bot_of_card_eq_pow_four {p : ℕ} (hp : p.Prime) {Q E D : Subgroup G}
    (hE : Nat.card E = p ^ 2) (hD : Nat.card D = p ^ 3) (hQ : Nat.card Q = p ^ 4)
    (hEQ : E ≤ Q) (hDQ : D ≤ Q) : E ⊓ D ≠ ⊥ := by
  intro hbot
  have hle : Nat.card E * Nat.card D ≤ Nat.card Q :=
    CFSG.card_mul_card_le_of_inf_eq_bot hEQ hDQ hbot
  rw [hE, hD, hQ, ← pow_add] at hle
  exact (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 4 < 5)).not_ge hle

theorem card_inf_eq_of_not_le {p : ℕ} (hp : p.Prime) {Q E D : Subgroup G}
    (hE : Nat.card E = p ^ 2) (hD : Nat.card D = p ^ 3) (hQ : Nat.card Q = p ^ 4)
    (hEQ : E ≤ Q) (hDQ : D ≤ Q) (hEnle : ¬ E ≤ D) : Nat.card (E ⊓ D : Subgroup G) = p := by
  have hBdvd : Nat.card (E ⊓ D : Subgroup G) ∣ p ^ 2 := by
    rw [← hE]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp).1 hBdvd
  have hk0 : k ≠ 0 := by
    intro hk0
    have hcard1 : Nat.card (E ⊓ D : Subgroup G) = 1 := by rw [hk, hk0]; simp
    have hbot : E ⊓ D = ⊥ := (Subgroup.card_eq_one).1 hcard1
    have hle : Nat.card E * Nat.card D ≤ Nat.card Q :=
      CFSG.card_mul_card_le_of_inf_eq_bot hEQ hDQ hbot
    rw [hE, hD, hQ, ← pow_add] at hle
    exact (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 4 < 5)).not_ge hle
  have hk2 : k ≠ 2 := by
    intro hk2
    have hcard : Nat.card (E ⊓ D : Subgroup G) = Nat.card E := by rw [hk, hk2, hE]
    have hEq : E ⊓ D = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard])
    exact hEnle (by rw [← hEq]; exact inf_le_right)
  have hk1 : k = 1 := by omega
  rw [hk, hk1, pow_one]

theorem map_conj_ne_of_gamma_normalizer {M E B : Subgroup G} {p : ℕ} {x : G}
    (hBE : B ≤ E) (hrank : 1 ≤ CFSG.Open.pRank p B)
    (hΓ : rankThreeGamma 1 p E ≤ M) (hxM : x ∉ M) :
    B.map (MulAut.conj x).toMonoidHom ≠ B := by
  intro hfix
  have hxN : x ∈ Subgroup.normalizer (B : Set G) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mpr (by simpa using hfix)
  exact hxM ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 p E B hBE hrank).trans
    hΓ hxN)

theorem twelveTenFinalStep_of_p_eq_three {M H Q : Subgroup G} {p : ℕ} (hp3 : p = 3)
    (hQcard : Nat.card Q = p ^ 4) (hA : TwelveTenFinalA' M H Q p)
    (hB : TwelveTenFinalB' M H Q p) : TwelveTenFinalStep M H Q p := by
  subst hp3
  obtain ⟨E, D, hEQ, hE, hEcard, hΓ, hD, hDQ⟩ := hA
  let B : Subgroup G := E ⊓ D
  have hBleE : B ≤ E := inf_le_left
  have hDcard : Nat.card D = 3 ^ 3 := by
    rw [hD.2.1]
    norm_num
  have hBne : B ≠ ⊥ :=
    inf_ne_bot_of_card_eq_pow_four (p := 3) (by norm_num) hEcard hDcard hQcard hEQ hDQ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hBp : IsPGroup 3 B := (hE.mono hBleE).isPGroup
  have hBdvd : 3 ∣ Nat.card B := by
    rcases hBp.card_eq_or_dvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hBne
    · exact h3
  have hBrank : 1 ≤ CFSG.Open.pRank 3 B := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup B]
    exact CFSG.one_le_pRank_of_dvd_card (by norm_num) hBdvd
  have hN : Subgroup.normalizer (B : Set G) ≤ M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 3 E B hBleE hBrank).trans hΓ
  refine ⟨D, hD, hDQ, ?_⟩
  intro x hx hxM
  have h7C : 7 ∣ Nat.card (centralizerInJ M H (B.map (MulAut.conj x).toMonoidHom)) :=
    seven_dvd_card_of_quotient_isL3TwoPow_one
      (pCore 2 ↥(centralizerInJ M H (B.map (MulAut.conj x).toMonoidHom)))
      (hB E D hEQ hE hEcard hΓ hD hDQ x hx hxM)
  exact dvd_card_inf_map_conj_of_dvd_centralizer (jSub_le M H) hN h7C

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
