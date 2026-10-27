module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NAs2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWe

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t g : G} {Lam P S U P1 : Subgroup G}

namespace NtAbs

theorem card_U (h : NtAbs t g Lam P S U P1) : Nat.card ↥U = 2 ^ 6 := by
  have h1 : Nat.card ↥U = Nat.card ↥(centEl P t) :=
    Nat.card_congr h.wr.centEquiv.toEquiv
  rw [h1, h.cent, h.card_S]

theorem card_Z1_eq_U0 (h : NtAbs t g Lam P S U P1) :
    Nat.card ↥(centIn P1 Lam) = Nat.card ↥(conjSub t (centIn P1 Lam)) := by
  exact (Subgroup.card_map_of_injective (K := centIn P1 Lam)
    (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective).symm

theorem card_U0_cases (h : NtAbs t g Lam P S U P1) :
    Nat.card ↥(conjSub t (centIn P1 Lam)) = 2 ^ 6 ∨
      Nat.card ↥(conjSub t (centIn P1 Lam)) = 2 ^ 7 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U0 := conjSub t (centIn P1 Lam)
  have hU0P1 : U0 ≤ P1 := (U0_le_P0 h).trans inf_le_left
  have hU0pg : IsPGroup 2 U0 := h.pgroup.to_le hU0P1
  have hU0norm : U0 ≤ normalizer (Lam : Set G) := (U0_le_P0 h).trans inf_le_right
  obtain ⟨k, hk⟩ := hU0pg.exists_card_eq
  have hdvd : 2 ^ 6 ∣ 2 ^ k := by
    have h1 : Nat.card ↥U ∣ Nat.card ↥U0 := Subgroup.card_dvd_of_le (U_le_U0 h)
    rwa [card_U h, hk] at h1
  have h6 : 6 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
  have hU0le : Nat.card ↥U0 ≤ 2 ^ 7 := by
    have h2 := h.aut U0 hU0pg hU0norm
    have hbot : U0 ⊓ centralizer (Lam : Set G) = ⊥ := by
      have hsub : U0 ⊓ centralizer (Lam : Set G) ≤
          centIn P1 Lam ⊓ conjSub t (centIn P1 Lam) := by
        rintro x ⟨hxU0, hxC⟩
        exact ⟨⟨hU0P1 hxU0, hxC⟩, hxU0⟩
      rw [Z1_inf_U0 h] at hsub
      exact le_antisymm hsub bot_le
    rwa [hbot, Subgroup.card_bot, mul_one] at h2
  have h7 : k ≤ 7 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by rwa [hk] at hU0le)
  rw [hk]
  have hk67 : k = 6 ∨ k = 7 := by omega
  rcases hk67 with rfl | rfl <;> simp

theorem card_P0_le (h : NtAbs t g Lam P S U P1) :
    Nat.card ↥(normIn P1 Lam) ≤ 2 ^ 7 * Nat.card ↥(conjSub t (centIn P1 Lam)) := by
  have hP0pg : IsPGroup 2 (normIn P1 Lam) := h.pgroup.to_le inf_le_left
  have hP0norm : normIn P1 Lam ≤ normalizer (Lam : Set G) := inf_le_right
  have h2 := h.aut (normIn P1 Lam) hP0pg hP0norm
  have hcent : normIn P1 Lam ⊓ centralizer (Lam : Set G) = centIn P1 Lam := by
    apply le_antisymm
    · rintro x ⟨⟨hxP1, -⟩, hxC⟩
      exact ⟨hxP1, hxC⟩
    · rintro x ⟨hxP1, hxC⟩
      exact ⟨⟨hxP1, Subgroup.centralizer_le_normalizer _ hxC⟩, hxC⟩
  rw [hcent, card_Z1_eq_U0 h] at h2
  exact h2

end NtAbs

end CFSG.OddStandard.HigherRank.YamadaG23
