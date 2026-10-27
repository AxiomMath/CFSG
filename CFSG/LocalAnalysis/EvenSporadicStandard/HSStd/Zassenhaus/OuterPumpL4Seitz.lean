module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpKillType
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies
import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpExcludeE

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.HSStd CFSG.Open
  CFSG.Assembly.LowTwoRank

theorem card_psl_four_pow_gt {Y : Type} [Group Y] {i : ℕ} (hi : 1 ≤ i)
    (h : LieModel Y .PSL 4 2 (2 ^ i)) : 65536 < Nat.card Y := by
  rw [card_psl_four Nat.one_le_two_pow h]
  have hf : 2 ≤ 2 ^ i :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  have hq : 4 ≤ 2 ^ (2 ^ i) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 ^ i) := Nat.pow_le_pow_right (by norm_num) hf
  generalize 2 ^ (2 ^ i) = q at hq ⊢
  have h6 : 4096 ≤ q ^ 6 :=
    calc 4096 = 4 ^ 6 := by norm_num
      _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 :=
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have h3 : 63 ≤ q ^ 3 - 1 := by
    have : 64 ≤ q ^ 3 :=
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have h4 : 255 ≤ q ^ 4 - 1 := by
    have : 256 ≤ q ^ 4 :=
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    omega
  calc 65536 < 4096 * (15 * (63 * 255)) := by norm_num
    _ ≤ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) :=
      Nat.mul_le_mul h6 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4))

theorem not_evenStandardException_of_psl_four_pow
    {Y : Type} [Group Y] {i : ℕ} (hi : 1 ≤ i) (h : LieModel Y .PSL 4 2 (2 ^ i)) :
    ¬ Recognition.Exact.EvenStandardException Y := by
  classical
  have hgt := card_psl_four_pow_gt hi h
  rintro (h1 | h1 | h1 | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | h1 | h1 | h1)
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hgt
    exact absurd hgt (by decide)
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hgt
    exact absurd hgt (by decide)
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hgt
    exact absurd hgt (by decide)
  ·
    have hle : Nat.card Y ≤ Fintype.card K ^ 16 := by
      rw [Nat.card_congr e.toEquiv]
      calc Nat.card (commutator (Matrix.symplecticGroup (Fin 2) K))
          ≤ Nat.card (Matrix.symplecticGroup (Fin 2) K) := Subgroup.card_le_card_group _
        _ ≤ Nat.card (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = Fintype.card K ^ 16 := by
            rw [Matrix, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
            simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
            ring
    rw [hK] at hle
    exact absurd hgt (not_lt.2 (by simpa using hle))
  ·
    have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    have hH : Nat.card (Chevalley.adjointGroup .G2 K) = 12096 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK2]
      rfl
    have : Finite (Chevalley.adjointGroup .G2 K) :=
      Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
    have hle : Nat.card Y ≤ 12096 := by
      rw [Nat.card_congr e.toEquiv, ← hH]
      refine Subgroup.card_le_of_le (Subgroup.commutator_le.2 fun a ha c hc => ?_)
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hc) (inv_mem ha)) (inv_mem hc)
    exact absurd hgt (not_lt.2 (hle.trans (by norm_num)))
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hgt
    exact absurd hgt (by decide)
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hgt
    exact absurd hgt (by decide)
  ·
    obtain ⟨e⟩ := h1
    have h12 := two_pow_twelve_dvd_card_psl_four hi h
    rw [Nat.card_congr e.toEquiv] at h12
    change 2 ^ 12 ∣ Nat.card CFSG.Blueprint.NativeSporadic.He at h12
    rw [CFSG.Sporadic.He.card_He] at h12
    exact absurd h12 (by norm_num)

theorem false_of_standard_l4_of_highPSL
    {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hS : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hL4 : L4CentralTwoTrivial) (h : StdHyp G M) {i : ℕ} (hi : 1 ≤ i)
    (e : LieModel (↥M ⧸ center ↥M) .PSL 4 2 (2 ^ i)) : False := by
  have hz : center ↥M = ⊥ := hL4 ↥M (isQuasisimple_of_stdHyp h) h.centerTwo i hi e
  obtain ⟨S, hcyc⟩ := h.cyclicSylow
  have := h.simple
  have hset : CFSG.SeitzReduction.SeitzSetting G M :=
    CFSG.SeitzReduction.seitzSetting_of h.nonabelian h.kProper h.standard h.oddCore S hcyc
      (Or.inl ⟨.PSL, 4, 2 ^ i, e.admissible, e⟩) (not_evenStandardException_of_psl_four_pow hi e) hz
  have hne : ((4 : ℕ), 2 ^ i) ≠ ((4 : ℕ), 1) := fun hp =>
    (Nat.one_lt_two_pow (by omega)).ne' (Prod.mk.inj hp).2
  exact hS G M hset ⟨4, 2 ^ i, le_rfl, hne,
    CFSG.SeitzReduction.lieModel_of_mulEquiv (CFSG.SeitzReduction.quotientCenterMulEquiv hz) e⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
