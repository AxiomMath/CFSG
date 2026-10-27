module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowUBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverU4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.SLBN CFSG.RankThree.Classical CFSG.RankThree.PartTwo.Census
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

theorem a2l_card_center_su_four_dvd {F : Type} [Field F] [Finite F] [CharP F 3]
    (hF : Nat.card F = 9) : Nat.card (center (StatedSU 4 (3 ^ 1) F)) ∣ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hZ⟩ := LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 3) (f := 1)
    (F := F) (n := 4) (by rw [hF]; norm_num) (by norm_num) (by simp)
  obtain ⟨hcyc, hexp⟩ := LieType.Steinberg.isCyclic_scalars_statedSU (K := F) (p := 3) (f := 1)
    (by rw [hF]; norm_num) (n := 4) (by norm_num)
  rw [hZ]
  obtain ⟨z, hz⟩ := hcyc.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers hz]
  refine orderOf_dvd_of_pow_eq_one ?_
  have := hexp z
  rwa [show Nat.gcd 4 (3 ^ 1 + 1) = 4 by norm_num] at this

theorem a2l_rowPSU_two {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 3 ≤ n) (hf : 2 ≤ f)
    (hm : LieModel X .PSU n 3 f) : a2lDatum X := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have hd : UnitaryFieldData 3 f K :=
    ⟨Nat.prime_three, by omega, by rw [hcard, ← pow_mul, mul_comm]⟩
  haveI := hd.finite
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  have hodd : Odd (3 ^ f) := Odd.pow (by decide)
  have h9 : 9 ≤ 3 ^ f :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_unitaryFieldData hd (by norm_num)
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := nonempty_sl2_mulEquiv_unitarySU_two hd
  haveI := Fintype.ofFinite F
  have hFc : Fintype.card F = 3 ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨s, -, hs⟩ : ∃ s ⊆ (Finset.univ : Finset F), s.card = 4 :=
    Finset.exists_subset_card_eq (by rw [Finset.card_univ, hFc]; omega)
  have hq : CFSG.IsQuasisimple (unitarySU 3 f K 2) :=
    CFSG.IsQuasisimple.of_mulEquiv ψ.symm (isQuasisimple_SL2 ⟨s, hs⟩)
  have hN : HarrisLit.IsSLTwoOver (3 ^ f) ↥(a2lUBlock hd 2 m).range :=
    ⟨F, inferInstance, inferInstance, hFc,
      ⟨(MonoidHom.ofInjective (a2lUBlock_injective hd)).symm.trans ψ.symm⟩⟩
  have hX₀ : (((⟨-1, neg_one_mem_unitarySU hd⟩ : unitarySU 3 f K 2) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = -1 := by simp
  have hdat := a2lDatum_psu_block hd h2 (k := 2) (m := m) (by norm_num) (by omega) hX₀ hodd
    (by omega) le_rfl ⟨_, rfl⟩ hq hN (a2l_typU_of_isSLTwoOver hodd h9 hN)
  exact a2lDatum_of_mulEquiv e.symm hdat

theorem a2l_rowPSU_three (hC : HypA2.ChevOddInChev2) {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 5 ≤ n) (hm : LieModel X .PSU n 3 1) : a2lDatum X := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have hd := a2l_unitaryFieldData_three hcard
  haveI := hd.finite
  haveI := hd.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite K
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  have hF9 : Nat.card K = 9 := by rw [hcard]; norm_num
  have hFc : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card]; exact hF9
  have hk : ringChar K ≠ 2 := a2l_ringChar_ne_two (by rw [hFc]; decide)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk
  obtain ⟨P, hPraw⟩ := exists_evenFrame hd h2 (n := 4) (r := 2) (by norm_num)
  have hP : hadj hd P * P = frameGram 2 (4 - 2 * 2) K := hPraw
  obtain ⟨hq4, hZ4⟩ := LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 3) (f := 1)
    (F := K) (n := 4) hcard (by norm_num) (by simp)
  let J : Subgroup (unitarySU 3 1 K (4 + m)) := (a2lUBlock hd 4 m).range
  let eJ : ↥J ≃* unitarySU 3 1 K 4 := (MonoidHom.ofInjective (a2lUBlock_injective hd)).symm
  have hqJ : CFSG.IsQuasisimple ↥J := CFSG.IsQuasisimple.of_mulEquiv eJ hq4
  have hmap : (center ↥J).map eJ.toMonoidHom = center (StatedSU 4 (3 ^ 1) K) :=
    Subgroup.map_center_eq eJ
  have hcenJ : Nat.card (center ↥J) ∣ 4 := by
    have h1 := Subgroup.card_map_of_injective (K := center ↥J) (f := eJ.toMonoidHom) eJ.injective
    rw [hmap] at h1
    rw [← h1]
    exact a2l_card_center_su_four_dvd hF9
  have h2J : IsPGroup 2 ↥(center ↥J) := by
    have h4 : Nat.card (center ↥J) ∣ 2 ^ 2 := by simpa using hcenJ
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    exact IsPGroup.of_card hi
  let eS : ↥J ⧸ center ↥J ≃* StatedProj (StatedSU 4 (3 ^ 1) K) :=
    QuotientGroup.congr _ _ eJ (hmap.trans hZ4)
  have hmJ : LieModel (↥J ⧸ center ↥J) .PSU 4 3 1 :=
    Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, by norm_num, by simp⟩, K, inferInstance,
      inferInstance, hcard, ⟨eS⟩⟩
  have hTU : TypU ↥J := a2l_typU_of_not_inChev2 hqJ h2J
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmJ)))))))
    (a2l_not_inChev2_psu43 hC hmJ)
  let φ : SL(2, K) →* unitarySU 3 1 K (4 + m) :=
    (a2lUBlock hd 4 m).comp (levSU hd hP (by norm_num))
  have hφ : Function.Injective φ := (a2lUBlock_injective hd).comp (a2l_levSU_injective hd hP _)
  have hN : HarrisLit.IsSLTwoOver 9 ↥φ.range :=
    ⟨K, inferInstance, inferInstance, hFc, ⟨(MonoidHom.ofInjective hφ).symm⟩⟩
  have hX₀ : (((levSU hd hP (by norm_num) (a2lNegOne K) : unitarySU 3 1 K 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = -1 := by
    rw [a2l_levSU_negOne hd hP (by norm_num) (by norm_num), Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_neg, Units.val_one, map_neg, map_one]
  have hdat := a2lDatum_psu_block hd h2 (k := 4) (m := m) (by norm_num) (by omega) hX₀
    (q₀ := 9) (by decide) (by norm_num) (N := φ.range)
    (fun x hx => by obtain ⟨y, rfl⟩ := hx; exact ⟨levSU hd hP (by norm_num) y, rfl⟩)
    ⟨a2lNegOne K, rfl⟩ hq4 hN hTU
  exact a2lDatum_of_mulEquiv e.symm hdat

theorem a2l_rowPSU (hC : HypA2.ChevOddInChev2) : a2lRowPSU := by
  intro X _ _ n f hn hf hm
  have hf1 : 1 ≤ f := hm.admissible.2.1
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · obtain rfl : f = 1 := by omega
    exact a2l_rowPSU_three hC (by omega) hm
  · exact a2l_rowPSU_two hn hge hm

end CFSG.OddStandard.SmallF3.HypA2Leaves
