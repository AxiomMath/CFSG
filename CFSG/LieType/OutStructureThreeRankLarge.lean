module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHighCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourLin
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourOrth

public section

namespace CFSG.LieType.OutStructure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
  (four_le_pRank_projSL_of_eight_le four_le_pRank_projSU_of_dvd_add
    four_le_pRank_projSU_of_dvd_sub)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (center_dvd_table lieModel_of_classical)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (lieCoverRankHighLin_aux)
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  (exists_noncomm_quotient_center_of_quasisimple pRank_quotient_center_eq_of_not_dvd)

theorem four_le_pRank_three_of_classical_model {G : Type} [Group G] [Finite G]
    {t : StatedLieTag} {n r f : ℕ} (hcl : StatedClassicalModel G t n r f)
    (ht : t = .PSL ∨ t = .PSU) (hn : 8 ≤ n) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  have hr : r.Prime := hcl.1.1
  have hcl' := hcl
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hcl'
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact four_le_pRank_projSL_of_eight_le hn
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl'
    rcases (show r ^ f % 3 = 0 ∨ r ^ f % 3 = 1 ∨ r ^ f % 3 = 2 by omega) with h0 | h1 | h2
    ·
      obtain rfl : r = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
          (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0))).symm
      obtain ⟨-, -, hrk⟩ := CFSG.SectionRank.classical_model_rank (by norm_num) hcl
      rcases hrk with ⟨h, -⟩ | ⟨-, ⟨hn3, -⟩ | h4⟩ | ⟨h, -⟩ | h4
      · exact absurd h (by decide)
      · omega
      · exact h4
      · exact absurd h (by decide)
      · exact h4
    ·
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
      have : Fintype K := Fintype.ofFinite K
      have : Fact r.Prime := ⟨hr⟩
      have : CharP K r := charP_of_card_eq_prime_pow (f := f * 2)
        (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
      exact four_le_pRank_projSU_of_dvd_sub (p := r) (f := f) hK hn h1
    ·
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
      exact four_le_pRank_projSU_of_dvd_add hK (by omega) (by omega)

private theorem isQuasisimple_of_open {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, exists_noncomm_quotient_center_of_quasisimple h⟩

private theorem exceptionalOrders_eq_one_of_seven_le {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) {n r f : ℕ} (hn : 7 ≤ n) :
    exceptionalOrders t n r f = (1, 1) := by
  rcases ht with rfl | rfl <;>
  · unfold exceptionalOrders
    split <;> first | rfl | (exfalso; omega)

private theorem three_dvd_first_generic {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU)
    {n r f : ℕ} (hn : 7 ≤ n)
    (h : 3 ∣ (genericOrders t n r f).1 * (genericOrders t n r f).2 *
      ((exceptionalOrders t n r f).1 * (exceptionalOrders t n r f).2)) :
    3 ∣ (genericOrders t n r f).1 := by
  have hb : (genericOrders t n r f).2 = 1 := by rcases ht with rfl | rfl <;> rfl
  rw [hb, exceptionalOrders_eq_one_of_seven_le ht hn] at h
  simpa using h

theorem four_le_pRank_three_of_classical_large
    (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) {t : StatedLieTag} {n r f : ℕ}
    (hcl : StatedClassicalModel (L ⧸ Subgroup.center L) t n r f) (ht : t = .PSL ∨ t = .PSU)
    (hn : 8 ≤ n) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have h4 := four_le_pRank_three_of_classical_model hcl ht hn
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center L)
  · have hdvd := center_dvd_table hGA (isQuasisimple_of_open hq) (MulEquiv.refl _)
      (lieModel_of_classical hcl)
    have hm : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f :=
      Or.inl ⟨by rcases ht with rfl | rfl <;> decide, hcl⟩
    obtain ⟨-, h2⟩ := lieCoverRankHighLin_aux hGA ⟨hq.1⟩ Nat.prime_three (by norm_num) hZ
      (by omega) hm ht (three_dvd_first_generic ht (by omega) (hZ.trans hdvd))
    omega
  · rwa [← pRank_quotient_center_eq_of_not_dvd Nat.prime_three hZ]

end CFSG.LieType.OutStructure
