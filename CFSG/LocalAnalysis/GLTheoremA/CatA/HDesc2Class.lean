module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.GLTheoremA.List93 (lie2Tags mem_lie2Tags fact2_two_pow_mul)
open CFSG.SeitzReduction.CrossChar (ordProj_two_eq_of_two)
open scoped Nat

instance decAdm (t : StatedLieTag) (n p f : ℕ) : Decidable (StatedLieAdmissible t n p f) := by
  unfold StatedLieAdmissible
  cases t <;> infer_instance

theorem tri_ge' {n : ℕ} (hn : 2 ≤ n) : n - 1 ≤ n * (n - 1) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

theorem bounds_of_adm {t : StatedLieTag} {n f a : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (h : lieSylowExponent t n * f = a) : n ≤ a + 1 ∧ f ≤ a := by
  have hf : 1 ≤ f := hadm.2.1
  have hN : 1 ≤ lieSylowExponent t n ∧ n ≤ lieSylowExponent t n + 1 := by
    cases t
    case PSL =>
      obtain ⟨-, -, hn, -, -⟩ := hadm
      have := tri_ge' hn
      have h2 : 2 ≤ n * (n - 1) := by
        have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
        omega
      simp only [lieSylowExponent]
      exact ⟨by omega, by omega⟩
    case PSU =>
      obtain ⟨-, -, hn, -⟩ := hadm
      have := tri_ge' (by omega : 2 ≤ n)
      have h2 : 2 ≤ n * (n - 1) := by
        have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      simp only [lieSylowExponent]
      exact ⟨by omega, by omega⟩
    case PSp =>
      obtain ⟨-, -, hn, -⟩ := hadm
      simp only [lieSylowExponent]
      constructor <;> nlinarith
    case POmegaOdd => exact absurd rfl hadm.2.2.2
    case POmegaPlus =>
      obtain ⟨-, -, hn⟩ := hadm
      simp only [lieSylowExponent]
      have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
      constructor <;> nlinarith [Nat.sub_add_cancel (show 1 ≤ n by omega)]
    case POmegaMinus =>
      obtain ⟨-, -, hn⟩ := hadm
      simp only [lieSylowExponent]
      have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
      constructor <;> nlinarith [Nat.sub_add_cancel (show 1 ≤ n by omega)]
    case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
    case G2 => obtain ⟨-, -, rfl, -⟩ := hadm; simp [lieSylowExponent]
    case F4 => obtain ⟨-, -, rfl⟩ := hadm; simp [lieSylowExponent]
    case E6 => obtain ⟨-, -, rfl⟩ := hadm; simp [lieSylowExponent]
    case E7 => obtain ⟨-, -, rfl⟩ := hadm; simp [lieSylowExponent]
    case E8 => obtain ⟨-, -, rfl⟩ := hadm; simp [lieSylowExponent]
    case twistedE6 => obtain ⟨-, -, rfl⟩ := hadm; simp [lieSylowExponent]
    case trialityD4 => obtain ⟨-, -, rfl⟩ := hadm; simp [lieSylowExponent]
    case twistedB2 => obtain ⟨-, -, rfl, -⟩ := hadm; simp [lieSylowExponent]
    case twistedF4 => obtain ⟨-, -, rfl, -⟩ := hadm; simp [lieSylowExponent]
    case Tits => obtain ⟨-, -, rfl, -⟩ := hadm; simp [lieSylowExponent]
  obtain ⟨hN1, hN2⟩ := hN
  have hNf : lieSylowExponent t n ≤ a := by
    rw [← h]; exact Nat.le_mul_of_pos_right _ hf
  have hfa : f ≤ a := by
    rw [← h]; exact Nat.le_mul_of_pos_left _ hN1
  exact ⟨by omega, hfa⟩

theorem rel_of_two {M N D N' D' : ℕ} (h : M * D = N) (h' : M * D' = N') : N * D' = N' * D := by
  rw [← h, ← h']
  ring

theorem cls_of_decide {a : ℕ} {tj : StatedLieTag} {nj fj : ℕ} (hj : StatedLieAdmissible tj nj 2 fj)
    (hja : lieSylowExponent tj nj * fj = a) {P : StatedLieTag → ℕ → ℕ → Prop}
    (hb : ∀ t ∈ lie2Tags, ∀ n ≤ a + 1, ∀ f ≤ a, 1 ≤ f → lieSylowExponent t n * f = a →
      StatedLieAdmissible t n 2 f →
      lieOrderNumerator t n (2 ^ f) * lieOrderDivisor tj nj (2 ^ fj) =
        lieOrderNumerator tj nj (2 ^ fj) * lieOrderDivisor t n (2 ^ f) → P t n f)
    {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor tj nj (2 ^ fj) = lieOrderNumerator tj nj (2 ^ fj)) : P t n f := by
  have hv := v2_eq_of_two hadm hM hj hMj
  rw [hja] at hv
  obtain ⟨hn, hf⟩ := bounds_of_adm hadm hv
  exact hb t (mem_lie2Tags t) n hn f hf hadm.2.1 hv hadm (rel_of_two hM hMj)

section Decide

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 200000
set_option maxRecDepth 100000

theorem cls_L3four {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .PSL 3 (2 ^ 2) = lieOrderNumerator .PSL 3 (2 ^ 2)) :
    (t = .PSL ∧ n = 3 ∧ f = 2) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) :=
  cls_of_decide (a := 6) (by decide) (by decide)
    (P := fun t n f => (t = .PSL ∧ n = 3 ∧ f = 2) ∨ (t = .PSL ∧ n = 4 ∧ f = 1))
    (by decide +kernel) hadm hM hMj

theorem cls_U3eight {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .PSU 3 (2 ^ 3) = lieOrderNumerator .PSU 3 (2 ^ 3)) :
    t = .PSU ∧ n = 3 ∧ f = 3 :=
  cls_of_decide (a := 9) (by decide) (by decide) (P := fun t n f => t = .PSU ∧ n = 3 ∧ f = 3)
    (by decide +kernel) hadm hM hMj

theorem cls_Sp48 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .PSp 2 (2 ^ 3) = lieOrderNumerator .PSp 2 (2 ^ 3)) :
    t = .PSp ∧ n = 2 ∧ f = 3 :=
  cls_of_decide (a := 12) (by decide) (by decide) (P := fun t n f => t = .PSp ∧ n = 2 ∧ f = 3)
    (by decide +kernel) hadm hM hMj

theorem cls_Sp62 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .PSp 3 (2 ^ 1) = lieOrderNumerator .PSp 3 (2 ^ 1)) :
    t = .PSp ∧ n = 3 ∧ f = 1 :=
  cls_of_decide (a := 9) (by decide) (by decide) (P := fun t n f => t = .PSp ∧ n = 3 ∧ f = 1)
    (by decide +kernel) hadm hM hMj

theorem cls_O8p2 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .POmegaPlus 4 (2 ^ 1) = lieOrderNumerator .POmegaPlus 4 (2 ^ 1)) :
    t = .POmegaPlus ∧ n = 4 ∧ f = 1 :=
  cls_of_decide (a := 12) (by decide) (by decide)
    (P := fun t n f => t = .POmegaPlus ∧ n = 4 ∧ f = 1) (by decide +kernel) hadm hM hMj

theorem cls_G28 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .G2 0 (2 ^ 3) = lieOrderNumerator .G2 0 (2 ^ 3)) :
    t = .G2 ∧ n = 0 ∧ f = 3 :=
  cls_of_decide (a := 18) (by decide) (by decide) (P := fun t n f => t = .G2 ∧ n = 0 ∧ f = 3)
    (by decide +kernel) hadm hM hMj

theorem cls_U48 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .PSU 4 (2 ^ 3) = lieOrderNumerator .PSU 4 (2 ^ 3)) :
    t = .PSU ∧ n = 4 ∧ f = 3 :=
  cls_of_decide (a := 18) (by decide) (by decide) (P := fun t n f => t = .PSU ∧ n = 4 ∧ f = 3)
    (by decide +kernel) hadm hM hMj

theorem cls_U42 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .PSU 4 (2 ^ 1) = lieOrderNumerator .PSU 4 (2 ^ 1)) :
    t = .PSU ∧ n = 4 ∧ f = 1 :=
  cls_of_decide (a := 6) (by decide) (by decide) (P := fun t n f => t = .PSU ∧ n = 4 ∧ f = 1)
    (by decide +kernel) hadm hM hMj

theorem cls_U52 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .PSU 5 (2 ^ 1) = lieOrderNumerator .PSU 5 (2 ^ 1)) :
    t = .PSU ∧ n = 5 ∧ f = 1 :=
  cls_of_decide (a := 10) (by decide) (by decide) (P := fun t n f => t = .PSU ∧ n = 5 ∧ f = 1)
    (by decide +kernel) hadm hM hMj

theorem cls_U62 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .PSU 6 (2 ^ 1) = lieOrderNumerator .PSU 6 (2 ^ 1)) :
    t = .PSU ∧ n = 6 ∧ f = 1 :=
  cls_of_decide (a := 15) (by decide) (by decide) (P := fun t n f => t = .PSU ∧ n = 6 ∧ f = 1)
    (by decide +kernel) hadm hM hMj

theorem cls_TD42 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .trialityD4 0 (2 ^ 1) = lieOrderNumerator .trialityD4 0 (2 ^ 1)) :
    t = .trialityD4 ∧ n = 0 ∧ f = 1 :=
  cls_of_decide (a := 12) (by decide) (by decide)
    (P := fun t n f => t = .trialityD4 ∧ n = 0 ∧ f = 1) (by decide +kernel) hadm hM hMj

theorem cls_Tits {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .Tits 0 (2 ^ 1) = lieOrderNumerator .Tits 0 (2 ^ 1)) :
    t = .Tits ∧ n = 0 ∧ f = 1 :=
  cls_of_decide (a := 11) (by decide) (by decide) (P := fun t n f => t = .Tits ∧ n = 0 ∧ f = 1)
    (by decide +kernel) hadm hM hMj

theorem cls_RF48 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .twistedF4 0 (2 ^ 3) = lieOrderNumerator .twistedF4 0 (2 ^ 3)) :
    t = .twistedF4 ∧ n = 0 ∧ f = 3 :=
  cls_of_decide (a := 36) (by decide) (by decide)
    (P := fun t n f => t = .twistedF4 ∧ n = 0 ∧ f = 3) (by decide +kernel) hadm hM hMj

theorem cls_RF432 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .twistedF4 0 (2 ^ 5) = lieOrderNumerator .twistedF4 0 (2 ^ 5)) :
    t = .twistedF4 ∧ n = 0 ∧ f = 5 :=
  cls_of_decide (a := 60) (by decide) (by decide)
    (P := fun t n f => t = .twistedF4 ∧ n = 0 ∧ f = 5) (by decide +kernel) hadm hM hMj

theorem cls_Sz32 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hMj : M * lieOrderDivisor .twistedB2 0 (2 ^ 5) = lieOrderNumerator .twistedB2 0 (2 ^ 5)) :
    t = .twistedB2 ∧ n = 0 ∧ f = 5 :=
  cls_of_decide (a := 10) (by decide) (by decide)
    (P := fun t n f => t = .twistedB2 ∧ n = 0 ∧ f = 5) (by decide +kernel) hadm hM hMj

theorem ordProj_of_mul_odd {a m Mj : ℕ} (hm : Odd m) (h : Mj = 2 ^ a * m) :
    ordProj[2] Mj = 2 ^ a := by
  subst h
  show 2 ^ (2 ^ a * m).factorization 2 = 2 ^ a
  rw [fact2_two_pow_mul hm]

theorem cls_of_card {a Mj : ℕ} (hMa : ordProj[2] Mj = 2 ^ a) {P : StatedLieTag → ℕ → ℕ → Prop}
    (hb : ∀ t ∈ lie2Tags, ∀ n ≤ a + 1, ∀ f ≤ a, 1 ≤ f → lieSylowExponent t n * f = a →
      StatedLieAdmissible t n 2 f →
      Mj * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f) → P t n f)
    {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) (hMj : M = Mj) :
    P t n f := by
  subst hMj
  have h1 := ordProj_two_eq_of_two hadm hM
  rw [hMa] at h1
  have hv : lieSylowExponent t n * f = a := (Nat.pow_right_injective le_rfl h1).symm
  obtain ⟨hn, hf⟩ := bounds_of_adm hadm hv
  exact hb t (mem_lie2Tags t) n hn f hf hadm.2.1 hv hadm hM

theorem cls_alt5 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) (hMj : M = 60) :
    t = .PSL ∧ n = 2 ∧ f = 2 :=
  cls_of_card (a := 2) (Mj := 60)
    (ordProj_of_mul_odd (a := 2) (m := 15) (by decide) (by norm_num))
    (P := fun t n f => t = .PSL ∧ n = 2 ∧ f = 2) (by decide +kernel) hadm hM hMj

theorem cls_alt6 {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) (hMj : M = 360) :
    False :=
  cls_of_card (a := 3) (Mj := 360)
    (ordProj_of_mul_odd (a := 3) (m := 45) (by decide) (by norm_num))
    (P := fun _ _ _ => False) (by decide +kernel) hadm hM hMj

end Decide

end CFSG.LocalAnalysis.GLTheoremA.HDesc
