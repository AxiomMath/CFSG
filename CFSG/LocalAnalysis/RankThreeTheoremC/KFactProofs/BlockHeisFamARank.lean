module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamARankTorus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamARankCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamARankLarge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

theorem heisAR_three_dvd_of_five_dvd {f : ℕ} (h : 5 ∣ 2 ^ f - 1) : 3 ∣ 2 ^ f - 1 := by
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hsplit : 2 ^ f = 16 ^ (f / 4) * 2 ^ (f % 4) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have h5 : 16 ^ (f / 4) % 5 = 1 := by rw [Nat.pow_mod]; norm_num
  have h3 : 16 ^ (f / 4) % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h2 : 2 ^ f % 5 = 1 := by omega
  rw [hsplit, Nat.mul_mod, h5, one_mul] at h2
  have hr : f % 4 = 0 := by
    have hlt : f % 4 < 4 := Nat.mod_lt _ (by norm_num)
    generalize f % 4 = k at hlt h2 ⊢
    interval_cases k <;> simp_all
  rw [hsplit, hr, pow_zero, mul_one]
  omega

theorem heisARankFacts_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : HeisARankFacts := by
  intro L _ _ hperf hodd hrk hs n f K _ _ hK hn hf eX p hp hp5
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ := heisAR_card_center_dvd hGA hperf hodd hs hK eX
  have hunits : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
  have hi : ¬ p ∣ Nat.gcd n (2 ^ f - 1) := by
    intro hdvd
    have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ 2 ^ f - 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
    have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
    obtain ⟨ρ, hρ⟩ := heisAR_exists_cover hGA hperf hodd hs hK (by omega) eX
    by_cases h6 : 6 ≤ n
    · obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [hunits]; exact hpq)
      exact heisAR_false_of_cover hrk hp (by omega) hn5 (Or.inl h6) hζ ρ hρ
    · have hn5' : n = 5 := by omega
      have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hn5' ▸ hpn)
      rw [hp5'] at hpq
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
        (by rw [hunits]; exact heisAR_three_dvd_of_five_dvd hpq)
      exact heisAR_false_of_cover hrk Nat.prime_three (by norm_num) hn5
        (Or.inr (by rw [hn5']; norm_num)) hζ ρ hρ
  have hiii : ¬ p ∣ Nat.card (Subgroup.center L) := fun h => hi (h.trans hZ)
  refine ⟨hi, ?_, hiii⟩
  have hp2 : p ≠ 2 := by omega
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpK
  have he : 0 < orderOf ((Nat.card K : ℕ) : ZMod p) :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one hq0⟩)
  have hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ orderOf ((Nat.card K : ℕ) : ZMod p) ∣ j :=
    fun j => by
      have hq1 : 1 ≤ Nat.card K ^ j := Nat.one_le_pow _ _ Finite.card_pos
      rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, Nat.cast_pow,
        Nat.cast_one, sub_eq_zero]
  rw [← hK]
  by_contra hge
  push Not at hge
  have hpe' : p * orderOf ((Nat.card K : ℕ) : ZMod p) ≤ n := (Nat.le_div_iff_mul_le he).1 hge
  have h5 : 5 * orderOf ((Nat.card K : ℕ) : ZMod p) ≤ n :=
    le_trans (Nat.mul_le_mul_right _ hp5) hpe'
  have h4 := heisAR_four_le_pRank hpK (by rw [hK]; exact hi) he hpe h5
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eX] at h4
  obtain ⟨A, -, hA, hAcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (L ⧸ Subgroup.center L))
  have h3 := heis_rank_quotient hrk hp hp2 hiii A hA.1 hA.2
  rw [hAcard] at h3
  have h6 : p ^ 4 ≤ p ^ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) :=
    Nat.pow_le_pow_right hp.pos h4
  have h7 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
