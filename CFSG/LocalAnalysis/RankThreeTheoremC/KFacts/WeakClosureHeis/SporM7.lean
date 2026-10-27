module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporDispatch
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

namespace M7Spor

open scoped commutatorElement

open CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
  _root_.Timmesfeld.PcReg _root_.Timmesfeld.Mon7

section ClassTwo

variable {G : Type*} [Group G]

theorem class_two_pow_aux (x y : G) (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    y ^ n * x = ⁅y, x⁆ ^ n * (x * y ^ n) := by
  have hc : y * x = ⁅y, x⁆ * (x * y) := by
    rw [commutatorElement_def]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : y * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * y := (hy.symm.pow_right n).eq
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (⁅y, x⁆ ^ n * (x * y ^ n)) := by rw [ih]
      _ = ⁅y, x⁆ ^ n * (y * x) * y ^ n := by rw [← mul_assoc, h1]; group
      _ = ⁅y, x⁆ ^ n * (⁅y, x⁆ * (x * y)) * y ^ n := by rw [hc]
      _ = ⁅y, x⁆ ^ (n + 1) * (x * y ^ (n + 1)) := by rw [pow_succ, pow_succ']; group

theorem class_two_pow (x y : G) (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    (x * y) ^ n = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : x ^ n * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * x ^ n := ((hx.pow_pow n n).symm).eq
    have h2 : (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
    have h3 : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := h2
      _ = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * (y ^ n * x) * y) := by rw [ih]; group
      _ = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * (⁅y, x⁆ ^ n * (x * y ^ n)) * y) := by
        rw [class_two_pow_aux x y hx hy n]
      _ = ⁅y, x⁆ ^ n.choose 2 * (⁅y, x⁆ ^ n * (x ^ n * (x * y ^ n)) * y) := by
        rw [← mul_assoc (x ^ n), h1]; group
      _ = ⁅y, x⁆ ^ (n + 1).choose 2 * (x ^ (n + 1) * y ^ (n + 1)) := by
        rw [h3]; group

theorem class_two_pow_prime {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (x y : G)
    (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (hc : ⁅y, x⁆ ^ p = 1) :
    (x * y) ^ p = x ^ p * y ^ p := by
  rw [class_two_pow x y hx hy p]
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (by norm_num : 2 ≠ 0) hp3
  rw [hk, pow_mul, hc, one_pow, one_mul]

theorem pow_eq_one_closure {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (S : Set G) (z : G)
    (hz : z ^ p = 1) (hS : ∀ s ∈ S, s ^ p = 1) (hzS : ∀ s ∈ S, z * s = s * z)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, ∃ m : ℤ, s * t * s⁻¹ * t⁻¹ = z ^ m) :
    ∀ g ∈ Subgroup.closure S, g ^ p = 1 := by
  have hzc : ∀ g ∈ Subgroup.closure S, z * g = g * z := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hzS x hx
    | one => simp
    | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    | inv x _ hx => exact (Commute.inv_right (show Commute z x from hx)).eq
  have hzc' : ∀ (m : ℤ), ∀ g ∈ Subgroup.closure S, z ^ m * g = g * z ^ m := fun m g hg =>
    ((show Commute z g from hzc g hg).zpow_left m).eq
  have hconj : ∀ (m : ℤ), ∀ g ∈ Subgroup.closure S, g * z ^ m * g⁻¹ = z ^ m := fun m g hg =>
    mul_inv_eq_iff_eq_mul.2 (hzc' m g hg).symm
  have hcc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S,
      ∃ m : ℤ, x * y * x⁻¹ * y⁻¹ = z ^ m := by
    intro x hx y hy
    induction hx, hy using Subgroup.closure_induction₂ with
    | mem x y hx hy => exact hcomm x hx y hy
    | one_left x hx => exact ⟨0, by simp⟩
    | one_right x hx => exact ⟨0, by simp⟩
    | mul_left x y w hx hy hw ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨b + a, ?_⟩
      have key : (x * y) * w * (x * y)⁻¹ * w⁻¹ =
          x * (y * w * y⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹) := by group
      rw [key, hb, ha, hconj b x hx, zpow_add]
    | mul_right y w x hy hw hx ihy ihw =>
      obtain ⟨a, ha⟩ := ihy
      obtain ⟨b, hb⟩ := ihw
      refine ⟨a + b, ?_⟩
      have key : x * (y * w) * x⁻¹ * (y * w)⁻¹ =
          (x * y * x⁻¹ * y⁻¹) * (y * (x * w * x⁻¹ * w⁻¹) * y⁻¹) := by group
      rw [key, ha, hb, hconj b y hy, zpow_add]
    | inv_left x y hx hy ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨-a, ?_⟩
      have key : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x⁻¹⁻¹ := by group
      have hinv : y * x * y⁻¹ * x⁻¹ = z ^ (-a) := by
        rw [zpow_neg, ← ha]; group
      rw [key, hinv]
      exact hconj (-a) x⁻¹ (inv_mem hx)
    | inv_right x y hx hy ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨-a, ?_⟩
      have key : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (y * x * y⁻¹ * x⁻¹) * y⁻¹⁻¹ := by group
      have hinv : y * x * y⁻¹ * x⁻¹ = z ^ (-a) := by
        rw [zpow_neg, ← ha]; group
      rw [key, hinv]
      exact hconj (-a) y⁻¹ (inv_mem hy)
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    obtain ⟨m, hm⟩ := hcc y hy x hx
    have hc : ⁅y, x⁆ = z ^ m := by rw [commutatorElement_def]; exact hm
    have hcx : Commute ⁅y, x⁆ x := by rw [hc]; exact hzc' m x hx
    have hcy : Commute ⁅y, x⁆ y := by rw [hc]; exact hzc' m y hy
    have hcp : ⁅y, x⁆ ^ p = 1 := by
      rw [hc, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
    rw [class_two_pow_prime hp hp3 x y hcx hcy hcp, ihx, ihy, one_mul]
  | inv x _ ihx => rw [inv_pow, ihx, inv_one]

end ClassTwo

section Card


@[expose] noncomputable def qseq : Fin 6 → Gmat := fun j => gq j.val

theorem word_zero_pos :
    ∀ j < 6, 0 < j → ∀ k ∈ wordOfVec 6 cw7[0 * 6 + j]!, 1 ≤ k ∧ k < 6 := by
  decide +kernel

theorem seven_pow_five_le_card [Finite Gmat] : 7 ^ 5 ≤ Nat.card (pcSub qseq 1) := by
  have hle : CFSG.KC.BM.PcFive.PSub (gq 0) qR ≤ pcSub qseq 0 := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨⟨i.val + 1, by have := i.isLt; omega⟩, Nat.zero_le _, rfl⟩
    · exact Subgroup.subset_closure ⟨⟨0, by norm_num⟩, le_rfl, rfl⟩
  have h6 : 7 ^ 6 ≤ Nat.card (pcSub qseq 0) := by
    rw [← card_PSub_gq]
    exact Subgroup.card_le_of_le hle
  have hstep := pcSub_card_step (p := 7) (by norm_num) qseq (⟨0, by norm_num⟩ : Fin 6)
    inferInstance
    (by
      show gq 0 ^ 7 ∈ _
      rw [gq_pow (by norm_num)]
      exact one_mem _)
    (by
      intro j hj
      have hj' : 0 < j.val := hj
      have h := gq_conj (i := 0) (j := j.val) (by norm_num) j.isLt hj'
      show gq 0 * gq j.val * (gq 0)⁻¹ ∈ _
      rw [h]
      refine Subgroup.list_prod_mem _ fun a ha => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
      have hk' := word_zero_pos j.val j.isLt hj' k hk
      exact Subgroup.subset_closure ⟨⟨k, hk'.2⟩, hk'.1, rfl⟩)
  have h7 := hstep.2
  have h1 : (7 : ℕ) ^ 6 ≤ 7 * Nat.card (pcSub qseq 1) := h6.trans h7
  have : 7 * 7 ^ 5 ≤ 7 * Nat.card (pcSub qseq 1) := by
    calc 7 * 7 ^ 5 = 7 ^ 6 := by norm_num
      _ ≤ _ := h1
  exact Nat.le_of_mul_le_mul_left this (by norm_num)

end Card

section Exp


theorem word_form :
    ∀ i < 6, ∀ j < 6, 1 ≤ i → i < j →
      wordOfVec 6 cw7[i * 6 + j]! =
        j :: List.replicate (if j = 5 then 0 else (cw7[i * 6 + j]!)[5]!) 5 := by
  decide +kernel

theorem gq_conj_form {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j < 6) :
    ∃ m : ℕ, gq i * gq j * (gq i)⁻¹ = gq j * gq 5 ^ m ∧ (j = 5 → m = 0) := by
  refine ⟨if j = 5 then 0 else (cw7[i * 6 + j]!)[5]!, ?_, fun h => by simp [h]⟩
  rw [gq_conj (by omega) hj hij, word_form i (by omega) j hj hi hij]
  simp [List.map_replicate, List.prod_replicate]

theorem gq_five_comm {i : ℕ} (hi : 1 ≤ i) (hi6 : i < 6) : gq 5 * gq i = gq i * gq 5 := by
  by_cases h5 : i = 5
  · rw [h5]
  · obtain ⟨m, hm, h0⟩ := gq_conj_form (i := i) (j := 5) hi (by omega) (by norm_num)
    rw [h0 rfl, pow_zero, mul_one, mul_inv_eq_iff_eq_mul] at hm
    exact hm.symm

theorem gq_comm_mem_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj6 : j < 6) :
    ∃ m : ℤ, gq i * gq j * (gq i)⁻¹ * (gq j)⁻¹ = gq 5 ^ m := by
  obtain ⟨m, hm, -⟩ := gq_conj_form hi hij hj6
  refine ⟨m, ?_⟩
  have hc : Commute (gq 5 ^ m) (gq j) :=
    (show Commute (gq 5) (gq j) from gq_five_comm (by omega) hj6).pow_left m
  rw [hm, ← hc.eq, mul_inv_cancel_right, zpow_natCast]

theorem gq_comm_mem {i j : ℕ} (hi : 1 ≤ i) (hi6 : i < 6) (hj : 1 ≤ j) (hj6 : j < 6) :
    ∃ m : ℤ, gq i * gq j * (gq i)⁻¹ * (gq j)⁻¹ = gq 5 ^ m := by
  rcases lt_trichotomy i j with h | h | h
  · exact gq_comm_mem_lt hi h hj6
  · subst h
    exact ⟨0, by simp⟩
  · obtain ⟨m, hm⟩ := gq_comm_mem_lt hj h hi6
    refine ⟨-m, ?_⟩
    rw [zpow_neg, ← hm]
    group

theorem pcSub_pow_seven : ∀ u ∈ pcSub qseq 1, u ^ 7 = 1 := by
  refine pow_eq_one_closure (p := 7) Nat.prime_seven (by norm_num) _ (gq 5)
    (gq_pow (by norm_num)) ?_ ?_ ?_
  · rintro _ ⟨k, hk, rfl⟩
    exact gq_pow k.isLt
  · rintro _ ⟨k, hk, rfl⟩
    exact gq_five_comm hk k.isLt
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact gq_comm_mem hk k.isLt hl l.isLt

end Exp

section Dich


theorem sylowDichotomyAt_gmat_seven [Finite Gmat] : SylowDichotomyAt Gmat 7 := by
  have hexp := pcSub_pow_seven
  refine SylowDichotomyAt.of_exponent (U := pcSub qseq 1) ?_ hexp seven_pow_five_le_card
  intro u
  exact ⟨1, Subtype.ext (by simpa using hexp u.1 u.2)⟩

end Dich

end M7Spor

open CFSG.Blueprint

section Main


theorem sdSpor_M7 : SDSporAt .M 7 := by
  intro K _ _ ⟨e⟩
  haveI : IsSimpleGroup (NativeSporadic.Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := NativeSporadic.Carrier .M) (MulEquiv.refl _)
  have φ : K ≃* CFSG.Monster.Generated.Gmat := e.trans ε
  haveI : Finite CFSG.Monster.Generated.Gmat := Finite.of_equiv K φ.toEquiv
  exact @SylowDichotomyAt.of_mulEquiv K _ _ 7 CFSG.Monster.Generated.Gmat _ _ (by norm_num) φ
    M7Spor.sylowDichotomyAt_gmat_seven

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
