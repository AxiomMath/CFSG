module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLThreeArith
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAType

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor lieSylowExponent LieOrderFormulasInput)

namespace OLThreeAdic

theorem lieOrderNumerator_PSU_three (q : ℕ) :
    lieOrderNumerator .PSU 3 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h : Finset.Icc 2 3 = {2, 3} := by decide
  simp only [lieOrderNumerator, h]
  rw [Finset.prod_pair (by norm_num)]
  have h2 : Even 2 := by decide
  have h3 : ¬ Even 3 := by decide
  simp only [h2, h3, if_true, if_false]

end OLThreeAdic

theorem overgroupLocalWhen_PSU_three
    (hLie : LieOrderFormulasInput) :
    OvergroupLocalWhen .PSU (fun n f₀ => n = 3 ∧ f₀ = 1) := by
  intro K _ _ hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  obtain ⟨rfl, rfl⟩ := hP
  haveI : IsSimpleGroup K := hs
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcl0 : StatedClassicalModel K .PSU 3 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hfp : f = p := by rw [hf, mul_one]
  have hp6 := OLThreeAdic.prime_mod_six hp hp5
  have hf6 : f % 6 = 1 ∨ f % 6 = 5 := by omega
  have hB := CFSG.Quasithin.GoldMLA.fusionIsBenderGroup_of_isPSU3 (by omega : 2 ≤ f) hcl0
  obtain ⟨-, hform, hexp⟩ := hLie K .PSU 3 2 f hadm hmodel
  refine ⟨3, Nat.prime_three, fun T Y hT hTY hY => ?_⟩
  have hTidx : ¬ 2 ∣ T.index := by
    have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
    rwa [Subgroup.relIndex_top_right] at h2
  let S : Sylow 2 K := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.1.toSylow hTidx
  have hST : (S : Subgroup K) = T := rfl
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hB S
  have hle : Y ≤ Subgroup.normalizer ((S : Subgroup K) : Set K) :=
    hD.le_normalizer_of_le (hST ▸ hTY) hY
  have hse : lieSylowExponent .PSU 3 = 3 := by decide
  have hS : Nat.card (S : Subgroup K) = (2 ^ f) ^ 3 := by
    rw [Sylow.card_eq_multiplicity S, hexp, hse, ← pow_mul, mul_comm]
  have hidx : Nat.card (Sylow 2 K) = (Subgroup.normalizer ((S : Subgroup K) : Set K)).index :=
    Sylow.card_eq_index_normalizer S
  rw [hD.card, hS] at hidx
  have hmul := Subgroup.card_mul_index (Subgroup.normalizer ((S : Subgroup K) : Set K))
  rw [← hidx] at hmul
  have hodd : (f % 2 = 1) := by omega
  have h3q : 3 ∣ 2 ^ f + 1 := by
    have := OLThreeAdic.two_pow_mod_nine_odd hodd
    omega
  have h9q : ¬ 9 ∣ (2 ^ f) ^ 2 - 1 := by
    have h := OLThreeAdic.two_pow_mod_nine_even (n := f * 2) (by omega)
    rw [pow_mul] at h
    omega
  have hg : lieOrderDivisor .PSU 3 (2 ^ f) = 3 := Nat.gcd_eq_left h3q
  rw [hg, OLThreeAdic.lieOrderNumerator_PSU_three] at hform
  have hN3 : Nat.card (Subgroup.normalizer ((S : Subgroup K) : Set K)) * 3 =
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) := by
    have hpos : 0 < (2 ^ f) ^ 3 + 1 := Nat.succ_pos _
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc Nat.card (Subgroup.normalizer ((S : Subgroup K) : Set K)) * 3 * ((2 ^ f) ^ 3 + 1)
        = (Nat.card (Subgroup.normalizer ((S : Subgroup K) : Set K)) * ((2 ^ f) ^ 3 + 1)) * 3 := by
          ring
      _ = Nat.card K * 3 := by rw [hmul]
      _ = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) := by rw [hform]; ring
  have h3N : ¬ 3 ∣ Nat.card (Subgroup.normalizer ((S : Subgroup K) : Set K)) := by
    rintro ⟨m, hm⟩
    have h9 : 9 ∣ (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) := ⟨m, by rw [← hN3, hm]; ring⟩
    have hcop : Nat.Coprime 9 ((2 ^ f) ^ 3) :=
      Nat.Coprime.pow_right 3 (Nat.Coprime.pow_right f (by norm_num))
    exact h9q (hcop.dvd_of_dvd_mul_left h9)
  have h3Y : ¬ 3 ∣ Nat.card Y := fun h => h3N (h.trans (Subgroup.card_dvd_of_le hle))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : lieOrderDivisor .PSU 3 (2 ^ 1) = 3 := by decide
  have hn : lieOrderNumerator .PSU 3 (2 ^ 1) = 216 := by
    rw [OLThreeAdic.lieOrderNumerator_PSU_three]
    norm_num
  have h2v : 2 ≤ padicValNat 3 216 :=
    (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num : 3 ^ 2 ∣ 216)
  rw [padicValNat.eq_zero_of_not_dvd h3Y, hd, hn, padicValNat_self]
  omega

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
