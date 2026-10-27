module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankCrit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankLift
import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open Subgroup Matrix
open scoped MatrixGroups

private theorem card_SL_two {K : Type} [Field K] [Finite K] :
    Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem le_pRank_PSL_two {K : Type} [Field K] [Fintype K] {q f : ℕ} (hq : q.Prime)
    (hK : Fintype.card K = q ^ f) : f ≤ CFSG.Open.pRank q (⊤ : Subgroup PSL(2, K)) := by
  have : Fact q.Prime := ⟨hq⟩
  have : CharP K q := charP_of_card_eq_prime_pow hK
  have hinj := CFSG.LocalAnalysis.RankThreeTheoremC.pslUnipotentHom_injective (K := K)
  refine CFSG.SectionRank.le_pRank hq.one_lt le_top
    (E := (CFSG.LocalAnalysis.RankThreeTheoremC.pslUnipotentHom (K := K)).range)
    ⟨inferInstance, ?_⟩ ?_
  · rintro _ ⟨a, rfl⟩
    exact CFSG.LocalAnalysis.RankThreeTheoremC.pslUnipotentHom_pow_prime q a
  · calc Nat.card (CFSG.LocalAnalysis.RankThreeTheoremC.pslUnipotentHom (K := K)).range
        = Nat.card (Multiplicative K) :=
          (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      _ = Nat.card K := Nat.card_congr Multiplicative.toAdd
      _ = q ^ f := by rw [Nat.card_eq_fintype_card, hK]

theorem le_pRank_of_surj_SL2
    {K : Type} [Field K] [Fintype K] {q f r : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hK : Fintype.card K = q ^ f) (hf : 3 ≤ f) (hrf : r ≤ f)
    (hr : r ^ 2 / 4 < 2 * f) {X : Type} [Group X] [Finite X] (φ : X →* SL(2, K))
    (hφ : Function.Surjective φ) : r ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := by
  have : Fact q.Prime := ⟨hq⟩
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hK27 : 27 ≤ Fintype.card K := by
    rw [hK]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
      _ ≤ q ^ f := Nat.pow_le_pow_right hq.pos hf
  have hK4 : 4 ≤ Nat.card K := by rw [Nat.card_eq_fintype_card]; omega
  haveI : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK4
  obtain ⟨hperf, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier (k := K) (by omega)
      (by omega)
  have hnc : ∃ a b : PSL(2, K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hbot : commutator PSL(2, K) = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top, eq_top_iff]
      intro x _
      rw [mem_center_iff]
      intro y
      exact h y x
    rw [hbot] at hperf
    obtain ⟨x, hx⟩ := exists_ne (1 : PSL(2, K))
    have hxb : x ∈ (⊥ : Subgroup PSL(2, K)) := hperf.symm ▸ mem_top x
    exact hx (mem_bot.1 hxb)
  have hM : ¬ q ∣ Nat.card (CFSG.Open.griessHopfMultiplier PSL(2, K)) := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro h
    have := Nat.le_of_dvd two_pos (h.trans (Nat.gcd_dvd_left 2 _))
    omega
  have hcen := pRank_cover_of_multiplier hnc hq hM (hrf.trans (le_pRank_PSL_two hq hK))
  obtain ⟨ℓ, hℓ, hℓd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hq3 (show 3 ≤ 2 * f by omega)
  have hℓq : ℓ ≠ q := by
    rintro rfl
    have h1 : ℓ ∣ ℓ ^ (2 * f) := dvd_pow_self ℓ (by omega)
    have h2 := Nat.dvd_sub h1 hℓd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact hprim 1 one_pos (by omega) (by simpa using (hq.even_sub_one hq2).two_dvd)
  have hℓF : ℓ ∣ Nat.card PSL(2, K) := by
    have hSL : ℓ ∣ Nat.card SL(2, K) := by
      rw [card_SL_two, Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm f 2]
      exact Dvd.dvd.mul_left hℓd _
    have hsplit : Nat.card SL(2, K) = Nat.card PSL(2, K) * Nat.card (center SL(2, K)) :=
      card_eq_card_quotient_mul_card_subgroup _
    have hZ : Nat.card (center SL(2, K)) ≤ 2 := by
      have hroots : rootsOfUnity (max (Fintype.card (Fin 2)) 1) K = rootsOfUnity 2 K := by simp
      rw [Nat.card_congr ((SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2)
        (R := K)).trans (MulEquiv.subgroupCongr hroots)).toEquiv]
      exact card_rootsOfUnity K 2
    rw [hsplit] at hSL
    rcases (Nat.Prime.dvd_mul hℓ).1 hSL with h | h
    · exact h
    · have := Nat.le_of_dvd Nat.card_pos h
      have := hℓ.two_le
      omega
  have hinv := not_dvd_card_GL_of_prime (F := PSL(2, K)) (k := r ^ 2 / 4) hq hℓ hℓq hℓF
    (fun i hi1 hi2 => hprim i (by omega) (by omega))
  exact le_pRank_of_surj_crit hnc hq hq2 hcen hinv
    ((QuotientGroup.mk' (center SL(2, K))).comp φ) ((QuotientGroup.mk'_surjective _).comp hφ)

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank
