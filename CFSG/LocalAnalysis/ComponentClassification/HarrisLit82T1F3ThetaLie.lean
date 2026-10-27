module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaOMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaSp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaE6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaTwE6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaE7Main
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Wire
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit CFSG.Assembly.LowTwoRank

theorem lieAdmissible_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem odd_orderOf_of_mem_oddCentralizerCore {X : Type} [Group X] [Finite X] {t y : X}
    (hy : y ∈ oddCentralizerCore t) : Odd (orderOf y) := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 (centralizer ({t} : Set X)))) :=
    pPrimeCore_coprime_card
  have hdvd : orderOf z ∣ Nat.card (pPrimeCore 2 (centralizer ({t} : Set X))) :=
    Subgroup.orderOf_dvd_natCard _ hz
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have := Nat.Coprime.coprime_dvd_right hdvd hcop
  rw [Nat.coprime_two_left] at this
  exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 h2)

theorem exists_ne_commute_of_sq_dvd_card {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ Nat.card G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) p
    (dvd_trans (dvd_pow_self p two_ne_zero) h)
  have hN : (Subgroup.zpowers x).Normal :=
    ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h0 | h1
  · have : x = 1 := by
      have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rw [h0] at this
      exact (Subgroup.mem_bot).1 this
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  · have hc' : Nat.card G = p := by
      rw [← Subgroup.card_top (G := G), ← h1, Nat.card_zpowers, hx]
    rw [hc'] at h
    have := Nat.le_of_dvd hp.pos h
    have h2 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega


theorem eq_one_of_pow_three_of_lieModel_three (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {τ : StatedLieTag} {n f : ℕ}
    (hL : LieModel (GeneralizedFitting.subgroup X) τ n 3 f) (hτ : ¬ (τ = .PSL ∧ n = 2)) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) (hy3 : y ^ 3 = 1) : y = 1 := by
  have hadm := lieAdmissible_of_lieModel hL
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ f := hadm.2.1
  have hexp : y ^ ((3 ^ f) ^ 2 - 1) = 1 → y = 1 := fun h =>
    E2.eq_one_of_pow_eq_one_of_pow_three (by
      rw [← pow_mul]
      exact E2.not_three_dvd_three_pow_sub_one (by omega)) h hy3
  have hE1 : τ ∈ oddExceptionalTags → τ ∉ torusExceptionalTags → y = 1 := fun h1 h2 => by
    rw [CatLeafProof.burgoyneExcOddCoreInput_holds X hsimple hnab τ n 3 f h1 h2 hp2 hL t ht,
      mem_bot] at hy
    exact hy
  cases τ with
  | PSL =>
    have hn : 3 ≤ n := by
      have h2 := hadm.2.2.1
      have hn2 : n ≠ 2 := fun h => hτ ⟨rfl, h⟩
      omega
    exact hexp (PSL.pow_eq_one_of_mem_oddCentralizerCore_PSL X hsimple hnab hp2 hL hn t ht hy)
  | PSU => exact hexp (U.pow_eq_one_of_mem_oddCentralizerCore_PSU X hsimple hnab hp2 hL t ht hy)
  | PSp => exact hexp (Sp.pow_eq_one_of_mem_oddCentralizerCore_PSp X hsimple hnab hp2 hL t ht hy)
  | POmegaOdd =>
    exact hexp (O.pow_eq_one_of_mem_oddCentralizerCore_POmegaOdd X hsimple hnab hp2 hL t ht hy)
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · obtain rfl : n = 4 := by omega
      exact hexp (O.pow_eq_one_of_mem_oddCentralizerCore_POmegaPlus4 X hsimple hnab hp2 hL t ht
        hy)
    · exact hexp (O.pow_eq_one_of_mem_oddCentralizerCore_POmegaPlus X hsimple hnab hp2 h5 hL t
        ht hy)
  | POmegaMinus =>
    exact hexp (O.pow_eq_one_of_mem_oddCentralizerCore_POmegaMinus X hsimple hnab hp2 hL t ht hy)
  | G2 => exact hE1 (by decide) (by decide)
  | F4 => exact hE1 (by decide) (by decide)
  | E6 => exact hexp (E2.pow_eq_one_of_mem_oddCentralizerCore_E6 X hsimple hnab hp2 hL t ht hy)
  | E7 => exact E2.eq_one_of_pow_three_of_mem_oddCentralizerCore_E7 X hsimple hnab hL t ht hy hy3
  | E8 => exact hE1 (by decide) (by decide)
  | twistedE6 =>
    exact hexp (E2.pow_eq_one_of_mem_oddCentralizerCore_twistedE6 X hsimple hnab hp2 hL t ht hy)
  | trialityD4 => exact hE1 (by decide) (by decide)
  | twistedG2 => exact hE1 (by decide) (by decide)
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

theorem oddCentralizerCore_eq_bot_of_lieModel_three_one (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {τ : StatedLieTag} {n : ℕ}
    (hL : LieModel (GeneralizedFitting.subgroup X) τ n 3 1) (t : X) (ht : orderOf t = 2) :
    oddCentralizerCore t = ⊥ := by
  have hadm := lieAdmissible_of_lieModel hL
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hexp : (∀ y ∈ oddCentralizerCore t, y ^ ((3 ^ 1) ^ 2 - 1) = 1) →
      oddCentralizerCore t = ⊥ := by
    intro h
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    have h8 : y ^ 2 ^ 3 = 1 := by
      have := h y hy
      norm_num at this ⊢
      exact this
    have hodd := odd_orderOf_of_mem_oddCentralizerCore hy
    have hco : Nat.Coprime (orderOf y) (2 ^ 3) :=
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hodd)
    exact orderOf_eq_one_iff.1 (hco.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one h8))
  have hE1 : τ ∈ oddExceptionalTags → τ ∉ torusExceptionalTags →
      oddCentralizerCore t = ⊥ := fun h1 h2 =>
    CatLeafProof.burgoyneExcOddCoreInput_holds X hsimple hnab τ n 3 1 h1 h2 hp2 hL t ht
  cases τ with
  | PSL =>
    have hn : 3 ≤ n := by
      obtain ⟨h2, -, h3⟩ := hadm.2.2
      by_contra hlt
      exact h3 (by rw [show n = 2 by omega]; rfl)
    exact hexp fun y hy =>
      PSL.pow_eq_one_of_mem_oddCentralizerCore_PSL X hsimple hnab hp2 hL hn t ht hy
  | PSU => exact hexp fun y hy =>
      U.pow_eq_one_of_mem_oddCentralizerCore_PSU X hsimple hnab hp2 hL t ht hy
  | PSp => exact hexp fun y hy =>
      Sp.pow_eq_one_of_mem_oddCentralizerCore_PSp X hsimple hnab hp2 hL t ht hy
  | POmegaOdd => exact hexp fun y hy =>
      O.pow_eq_one_of_mem_oddCentralizerCore_POmegaOdd X hsimple hnab hp2 hL t ht hy
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · obtain rfl : n = 4 := by omega
      exact hexp fun y hy =>
        O.pow_eq_one_of_mem_oddCentralizerCore_POmegaPlus4 X hsimple hnab hp2 hL t ht hy
    · exact hexp fun y hy =>
        O.pow_eq_one_of_mem_oddCentralizerCore_POmegaPlus X hsimple hnab hp2 h5 hL t ht hy
  | POmegaMinus => exact hexp fun y hy =>
      O.pow_eq_one_of_mem_oddCentralizerCore_POmegaMinus X hsimple hnab hp2 hL t ht hy
  | G2 => exact hE1 (by decide) (by decide)
  | F4 => exact hE1 (by decide) (by decide)
  | E6 => exact hexp fun y hy =>
      E2.pow_eq_one_of_mem_oddCentralizerCore_E6 X hsimple hnab hp2 hL t ht hy
  | E7 => exact E2.oddCentralizerCore_eq_bot_E7_three X hsimple hnab hL t ht
  | E8 => exact hE1 (by decide) (by decide)
  | twistedE6 => exact hexp fun y hy =>
      E2.pow_eq_one_of_mem_oddCentralizerCore_twistedE6 X hsimple hnab hp2 hL t ht hy
  | trialityD4 => exact hE1 (by decide) (by decide)
  | twistedG2 => exact hE1 (by decide) (by decide)
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

theorem exists_ne_commute_of_lieModel_three
    {X : Type} [Group X]
    [IsSimpleGroup X] {τ : StatedLieTag} {n f : ℕ} (hL : LieModel X τ n 3 f)
    (hτ : ¬ (τ = .PSL ∧ n = 2)) : ∃ a b : X, a * b ≠ b * a := by
  have hadm := lieAdmissible_of_lieModel hL
  obtain ⟨hfin, -, hfac⟩ := CatLeafProof.lieOrderFormulasInput X τ n 3 f hadm hL
  have : Finite X := hfin
  have hf : 1 ≤ f := hadm.2.1
  have hN : 2 ≤ CatLeaf.lieSylowExponent τ n := by
    cases τ with
    | PSL =>
      have h2 := hadm.2.2.1
      have hn2 : n ≠ 2 := fun h => hτ ⟨rfl, h⟩
      have h6 : 2 * 2 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      show 2 ≤ n * (n - 1) / 2
      exact (Nat.le_div_iff_mul_le (by norm_num)).2 h6
    | PSU =>
      have h3 := hadm.2.2.1
      have h6 : 2 * 2 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      show 2 ≤ n * (n - 1) / 2
      exact (Nat.le_div_iff_mul_le (by norm_num)).2 h6
    | PSp =>
      have h2 := hadm.2.2.1
      change 2 ≤ n ^ 2
      nlinarith
    | POmegaOdd =>
      have h3 := hadm.2.2.1
      change 2 ≤ n ^ 2
      nlinarith
    | POmegaPlus =>
      have h4 : 4 ≤ n := hadm.2.2
      show 2 ≤ n * (n - 1)
      exact le_trans (by omega) (Nat.mul_le_mul h4 (show 3 ≤ n - 1 by omega))
    | POmegaMinus =>
      have h4 : 4 ≤ n := hadm.2.2
      show 2 ≤ n * (n - 1)
      exact le_trans (by omega) (Nat.mul_le_mul h4 (show 3 ≤ n - 1 by omega))
    | twistedB2 => exact absurd hadm.2.2.2.1 (by norm_num)
    | twistedF4 => exact absurd hadm.2.2.2.1 (by norm_num)
    | Tits => exact absurd hadm.2.2.2.1 (by norm_num)
    | _ => simp [CatLeaf.lieSylowExponent]
  have hpos : Nat.card X ≠ 0 := Nat.card_pos.ne'
  refine exists_ne_commute_of_sq_dvd_card Nat.prime_three
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).2 ?_)
  rw [hfac]
  nlinarith

end CFSG.ComponentClassification.Burgoyne
