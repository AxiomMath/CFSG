module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedACore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

theorem primePower_p_eq_two_of_card_four {q : TauCeti.PrimePower} (hq : q.card = 4) :
    q.p = 2 := by
  have hpd : q.p ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hq, TauCeti.PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hpd)

theorem card_hypSU_two_one_four {K : Type} [Field K] (h : UnitaryFieldData 2 2 K) {r : ℕ}
    (hr : r = 2) : Nat.card (hypSU h r 1) = 267219763200000 := by
  subst hr
  have hS := (card_hypSU h (r := 2) (ε := 1) (by norm_num)).1
  have hI : Finset.Icc 2 (2 * 2 + 1) = {2, 3, 4, 5} := by decide
  rw [hI] at hS
  simp only [Finset.prod_insert (show (2 : ℕ) ∉ ({3, 4, 5} : Finset ℕ) by decide),
    Finset.prod_insert (show (3 : ℕ) ∉ ({4, 5} : Finset ℕ) by decide),
    Finset.prod_insert (show (4 : ℕ) ∉ ({5} : Finset ℕ) by decide), Finset.prod_singleton] at hS
  norm_num at hS
  exact_mod_cast hS

theorem twentyFive_dvd_index_isoStabilizer {K : Type} [Field K] (h : UnitaryFieldData 2 2 K)
    {t s : ℕ} (ht1 : 1 ≤ t) (hts : t + s = 2) (g : hypSU h (t + s) 1) :
    25 ∣ (isoStabilizer h (t + s) 1 (g • hypFlag h (t + s) 1 t)).index := by
  obtain ⟨hiso, hfin, -⟩ := ToralCensus.hypFlag_smul_facts h le_rfl g ht1 (Nat.le_add_right t s)
  obtain ⟨-, hidx, -, -, h1, -, h2⟩ := isotropic_stabilizer_index h _ hiso
  rw [hfin] at hidx
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (t = 1 ∧ s = 1) ∨ (t = 2 ∧ s = 0) := by omega
  · rw [h1] at hidx
    norm_num at hidx
    have : (isoStabilizer h (1 + 1) 1 (g • hypFlag h (1 + 1) 1 1)).index = 17425 := by
      exact_mod_cast hidx
    rw [this]
    norm_num
  · rw [show 2 * (2 + 0) + 1 = 2 * 2 + 1 from rfl, h2 2] at hidx
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)] at hidx
    norm_num at hidx
    have : (isoStabilizer h (2 + 0) 1 (g • hypFlag h (2 + 0) 1 2)).index = 66625 := by
      exact_mod_cast hidx
    rw [this]
    norm_num

theorem psu54ParabolicFive_holds :
    PSU54ParabolicFive := by
  intro Y _ _ L P hCP hZ d q hdq hq e
  have hd : IdxTwistedA d.1 := by
    rw [hdq]
    exact primePower_p_eq_two_of_card_four hq
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hdim, hρ, hZρ, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d hd e
  obtain ⟨hqf, hn⟩ := hdim 4 q hdq
  have hf : f = 2 := by
    have h4 : (2 : ℕ) ^ f = 2 ^ 2 := by
      rw [← hqf, hq]
      norm_num
    exact Nat.pow_right_injective le_rfl h4
  subst hf
  have hε1 : ε = 1 := by omega
  subst hε1
  have hts : t + s = 2 := by omega
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hle : (P.subgroupOf L).comap ρ ≤ isoStabilizer h (t + s) 1 (g • hypFlag h (t + s) 1 t) :=
    fun y hy => mem_isoStabilizer.2 ((hJ y).1 hy t (Finset.mem_coe.2 hI.mem))
  have hidxL : 25 ∣ (P.subgroupOf L).index := by
    rw [← Subgroup.index_comap_of_surjective (P.subgroupOf L) hρ]
    exact (twentyFive_dvd_index_isoStabilizer h ht1 hts g).trans (Subgroup.index_dvd_of_le hle)
  refine ⟨(show 5 ∣ 25 by norm_num).trans hidxL, fun h125 => ?_⟩
  have hker : ρ.ker = hypScalars h (t + s) 1 := by
    ext y
    rw [MonoidHom.mem_ker, ← hZρ y, hZ, Subgroup.mem_bot]
  have hZc : Nat.card (hypScalars h (t + s) 1) = 5 := by
    rw [card_hypScalars h (by omega), hts]
    norm_num
  have hL : Nat.card L * 5 = 267219763200000 := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv, hker,
      hZc] at hcard
    rw [← card_hypSU_two_one_four h hts, hcard]
  have hPL : Nat.card (P.subgroupOf L) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP.parab.1).toEquiv
  have hmul := Subgroup.card_mul_index (P.subgroupOf L)
  rw [hPL] at hmul
  have h5 : 5 ^ 5 ∣ Nat.card L := by
    rw [← hmul, show 5 ^ 5 = 5 ^ 3 * 25 by norm_num]
    exact Nat.mul_dvd_mul h125 hidxL
  obtain ⟨c, hc⟩ := h5
  rw [hc] at hL
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
