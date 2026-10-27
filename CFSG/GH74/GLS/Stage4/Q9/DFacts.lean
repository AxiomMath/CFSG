module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public meta import Mathlib
public import CFSG.GH74.GLS.Stage4.Q9.DFactsInputs
public meta import CFSG.GH74.GLS.Stage4.Q9.DFactsInputs
public import Certificates.Certificate5099
public import Certificates.Certificate5100

public section

namespace CFSG.GH74.GLS.Stage4.Q9

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9

namespace DFacts

theorem mem_f9List (x : F9) : x ∈ f9List := by
  rcases x with ⟨a, b⟩
  revert a b
  decide

theorem mem_sl2List (M : SL2) : M ∈ sl2List := by
  have h := M.det_coe
  rw [Matrix.det_fin_two] at h
  simp only [sl2List, List.mem_flatMap, List.mem_filterMap]
  refine ⟨(M : 𝕄) 0 0, mem_f9List _, (M : 𝕄) 0 1, mem_f9List _, (M : 𝕄) 1 0, mem_f9List _,
    (M : 𝕄) 1 1, mem_f9List _, ?_⟩
  split
  · exact congrArg some (Subtype.ext (Matrix.eta_fin_two _).symm)
  · rename_i hne
    exact absurd h hne

theorem impB_eq_true {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> simp [impB]

theorem invSL_eq (g : SL2) : invSL g = g⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  rfl

theorem orderOf_SL2_eq (M : SL2) : orderOf M = ordL (innerL M) := by
  rw [← orderOf_injective innerL innerL_injective M, orderOf_Lg]

theorem mem_cent {M N : SL2} : N ∈ cent M ↔ M * N = N * M := by
  simp [cent, mem_sl2List]

theorem chkSqOne_true : chkSqOne = true :=
  Certificates.certificate5099.1

theorem chkSqOne_spec :
    ∀ M ∈ sl2List, M * M = 1 → M = 1 ∨ M = minusOne := by
  simpa only [chkSqOne, List.all_eq_true, impB_eq_true, Bool.or_eq_true, beq_iff_eq]
    using chkSqOne_true

theorem chkQ8_true : chkQ8 = true :=
  Certificates.certificate5099.2.2.1

theorem chkQ8_spec :
    ∀ p ∈ sl2List, p * p = minusOne → ∀ q ∈ sl2List, q * q = minusOne →
    q * p = p * minusOne * q → ∃ r ∈ sl2List,
      (r * p = q * r ∨ r * p = q * minusOne * r) ∧
        (r * q = p * q * r ∨ r * q = p * q * minusOne * r) := by
  simpa only [chkQ8, List.all_eq_true, List.any_eq_true, impB_eq_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq] using chkQ8_true

theorem chkConjFixed5_true : chkConjFixed5 = true :=
  Certificates.certificate5099.2.2.2.1

theorem chkConjFixed5_spec : ∀ M ∈ sl2List, ordL (innerL M) = 5 →
    ∃ k ∈ sl2List, sigmaAut (k * M * invSL k) = k * M * invSL k := by
  simpa only [chkConjFixed5, List.all_eq_true, List.any_eq_true, impB_eq_true, beq_iff_eq]
    using chkConjFixed5_true

theorem chkCent5_true : chkCent5 = true :=
  Certificates.certificate5099.2.2.2.2.1

theorem chkCent5_spec :
    ∀ M ∈ sl2List, ordL (innerL M) = 5 → (cent M).toFinset.card = 10 := by
  simpa only [chkCent5, List.all_eq_true, impB_eq_true, beq_iff_eq] using chkCent5_true

theorem chkCent3_true : chkCent3 = true :=
  Certificates.certificate5099.2.2.2.2.2.1

theorem chkCent3_spec :
    ∀ M ∈ sl2List, ordL (innerL M) = 3 → (cent M).toFinset.card = 18 := by
  simpa only [chkCent3, List.all_eq_true, impB_eq_true, beq_iff_eq] using chkCent3_true

theorem chkCentOdd5_true : chkCentOdd5 = true :=
  Certificates.certificate5099.2.2.2.2.2.2.1

theorem chkCentOdd5_spec :
    ∀ M ∈ sl2List, ordL (innerL M) = 5 → ∀ N ∈ cent M,
    ordL (innerL N) % 2 = 0 ∨ N = 1 ∨ N = M ∨ N = M * M ∨ N = M * M * M ∨ N = M * M * M * M := by
  simpa only [chkCentOdd5, List.all_eq_true, impB_eq_true, Bool.or_eq_true, beq_iff_eq,
    or_assoc] using chkCentOdd5_true

theorem chkCentOdd3_true : chkCentOdd3 = true :=
  Certificates.certificate5099.2.2.2.2.2.2.2.1

theorem chkCentOdd3_spec :
    ∀ M ∈ sl2List, ordL (innerL M) = 3 → ∀ N ∈ cent M,
    ordL (innerL N) % 2 = 0 ∨ ordL (innerL N) = 1 ∨ ordL (innerL N) = 3 := by
  simpa only [chkCentOdd3, List.all_eq_true, impB_eq_true, Bool.or_eq_true, beq_iff_eq,
    or_assoc] using chkCentOdd3_true

theorem chkSigmaNotConj_true :
    chkSigmaNotConj = true :=
  Certificates.certificate5099.2.2.2.2.2.2.2.2.1

theorem chkSigmaNotConj_spec : ∀ M ∈ sl2List, ordL (innerL M) = 3 →
    ∀ k ∈ sl2List, k * sigmaAut M ≠ M * k := by
  simpa only [chkSigmaNotConj, List.all_eq_true, impB_eq_true, bne_iff_ne, beq_iff_eq]
    using chkSigmaNotConj_true

theorem chkInvert3_true : chkInvert3 = true :=
  Certificates.certificate5099.2.2.2.2.2.2.2.2.2.1

theorem chkInvert3_spec : ∀ M ∈ sl2List, ordL (innerL M) = 3 →
    ∃ k ∈ sl2List, k * k = minusOne ∧ k * M = invSL M * k := by
  simpa only [chkInvert3, List.all_eq_true, List.any_eq_true, impB_eq_true, Bool.and_eq_true,
    beq_iff_eq] using chkInvert3_true

theorem chkQ16_true : chkQ16 = true :=
  Certificates.certificate5099.2.2.2.2.2.2.2.2.2.2.2.1

theorem chkQ16_spec : ∀ s ∈ sl2List, inQ16b s = true →
    (∀ w ∈ sl2List, inQ16b w = true → s * w = w * s) → s = 1 ∨ s = minusOne := by
  simpa only [chkQ16, List.all_eq_true, impB_eq_true, Bool.or_eq_true, beq_iff_eq]
    using chkQ16_true

theorem chkQ16card_true : chkQ16card = true :=
  Certificates.certificate5099.2.2.2.2.2.2.2.2.2.2.2.2

@[expose] def jSL : SL2 := ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; decide⟩

theorem jSL_sq : jSL * jSL = minusOne := by decide

@[expose] def fixed5 : SL2 :=
  ⟨!![(⟨2, 1⟩ : F9), (⟨1, 0⟩ : F9); (⟨2, 1⟩ : F9), (⟨2, 1⟩ : F9)], by
    rw [Matrix.det_fin_two_of]; decide⟩

theorem sigma_fixed5 : sigmaAut fixed5 = fixed5 := by decide

theorem fixed5_pow : fixed5 ^ 5 = 1 := by decide

theorem fixed5_ne_one : fixed5 ≠ 1 := by decide

theorem orderOf_fixed5 : orderOf fixed5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime fixed5_pow fixed5_ne_one

@[expose] def h16Wit : Lg := ⟨jSL, Multiplicative.ofAdd 1⟩

theorem h16_parity : parityL h16Wit ≠ 1 := by decide

theorem h16_ord : ordL h16Wit = 16 := by decide

theorem h16_conj : tauL * h16Wit = h16Wit ^ 7 * tauL := by decide

theorem h16_pow8 : h16Wit ^ 8 = innerL minusOne := by decide

theorem inQ16b_eq_true {g : SL2} : inQ16b g = true ↔
    (((g : 𝕄) 0 1 = 0 ∧ (g : 𝕄) 1 0 = 0) ∨ ((g : 𝕄) 0 0 = 0 ∧ (g : 𝕄) 1 1 = 0)) := by
  simp [inQ16b]

theorem inQ16_mul {g h : SL2} (hg : inQ16b g = true) (hh : inQ16b h = true) :
    inQ16b (g * h) = true := by
  rw [inQ16b_eq_true] at hg hh ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rcases hg with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hh with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    simp [a1, a2, b1, b2]

theorem inQ16_inv {g : SL2} (hg : inQ16b g = true) : inQ16b g⁻¹ = true := by
  rw [inQ16b_eq_true] at hg ⊢
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  rcases hg with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · left; simp [a1, a2]
  · right; simp [a1, a2]

theorem inQ16_one : inQ16b (1 : SL2) = true := by
  rw [inQ16b_eq_true]
  left
  simp

@[expose] def monomialSL2 : Subgroup SL2 where
  carrier := {g | inQ16b g = true}
  mul_mem' := inQ16_mul
  one_mem' := inQ16_one
  inv_mem' := inQ16_inv

theorem mem_monomialSL2 {g : SL2} : g ∈ monomialSL2 ↔ inQ16b g = true := Iff.rfl

instance : DecidablePred (· ∈ monomialSL2) := fun _ => decidable_of_iff _ mem_monomialSL2.symm

theorem minusOne_mem_monomialSL2 : minusOne ∈ monomialSL2 := by
  rw [mem_monomialSL2]
  decide

theorem natCard_monomialSL2 : Nat.card monomialSL2 = 16 := by
  have h : Nat.card monomialSL2 = (Finset.univ.filter fun g : SL2 => g ∈ monomialSL2).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e3 : (Finset.univ.filter fun g : SL2 => g ∈ monomialSL2) =
      (sl2List.filter inQ16b).toFinset := by
    ext g
    simp [mem_sl2List, mem_monomialSL2]
  rw [h, e3]
  simpa only [chkQ16card, beq_iff_eq] using chkQ16card_true

theorem natCard_centralizer_singleton (M : SL2) :
    Nat.card (Subgroup.centralizer ({M} : Set SL2)) = (cent M).toFinset.card := by
  have h : ∀ N : SL2, N ∈ Subgroup.centralizer ({M} : Set SL2) ↔ M * N = N * M := by
    intro N
    rw [Subgroup.mem_centralizer_iff]
    simp
  have e1 : Nat.card (Subgroup.centralizer ({M} : Set SL2)) =
      Nat.card {N : SL2 // M * N = N * M} := Nat.card_congr (Equiv.subtypeEquivRight h)
  have e2 : Nat.card {N : SL2 // M * N = N * M} =
      (Finset.univ.filter fun N : SL2 => M * N = N * M).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e3 : (Finset.univ.filter fun N : SL2 => M * N = N * M) = (cent M).toFinset := by
    ext N
    simp [mem_cent]
  rw [e1, e2, e3]

theorem mem_cent_of_mem_centralizer {M N : SL2}
    (hN : N ∈ Subgroup.centralizer ({M} : Set SL2)) : N ∈ cent M := by
  rw [mem_cent]
  rw [Subgroup.mem_centralizer_iff] at hN
  simpa using hN

end DFacts

theorem sl2_sq_eq_one_F9 :
    ∀ M : SL2, M * M = 1 → M = 1 ∨ M = minusOne :=
  fun M => DFacts.chkSqOne_spec M (DFacts.mem_sl2List M)

theorem q8cycle_sl2 :
    ∀ p q : SL2, p * p = minusOne → q * q = minusOne →
    q * p * q⁻¹ = p * minusOne → ∃ r : SL2,
      (r * p * r⁻¹ = q ∨ r * p * r⁻¹ = q * minusOne) ∧
        (r * q * r⁻¹ = p * q ∨ r * q * r⁻¹ = p * q * minusOne) := by
  intro p q hp hq hpq
  rw [mul_inv_eq_iff_eq_mul] at hpq
  obtain ⟨r, -, h1, h2⟩ :=
    DFacts.chkQ8_spec p (DFacts.mem_sl2List p) hp q (DFacts.mem_sl2List q) hq hpq
  exact ⟨r, by simpa only [mul_inv_eq_iff_eq_mul] using h1,
    by simpa only [mul_inv_eq_iff_eq_mul] using h2⟩

theorem exists_h16 : ∃ l : Lg, parityL l ≠ 1 ∧ orderOf l = 16 ∧
    tauL * l * tauL⁻¹ = l ^ 7 ∧ l ^ 8 = innerL minusOne :=
  ⟨DFacts.h16Wit, DFacts.h16_parity, by rw [orderOf_Lg, DFacts.h16_ord],
    by rw [mul_inv_eq_iff_eq_mul]; exact DFacts.h16_conj, DFacts.h16_pow8⟩

theorem exists_fixed5 : ∃ M : SL2, sigmaAut M = M ∧ orderOf M = 5 :=
  ⟨DFacts.fixed5, DFacts.sigma_fixed5, DFacts.orderOf_fixed5⟩

theorem conj_fixed5 :
    ∀ M : SL2, orderOf M = 5 →
    ∃ k : SL2, sigmaAut (k * M * k⁻¹) = k * M * k⁻¹ := by
  intro M hM
  obtain ⟨k, -, hk⟩ := DFacts.chkConjFixed5_spec M (DFacts.mem_sl2List M)
    (by rw [← DFacts.orderOf_SL2_eq, hM])
  exact ⟨k, by simpa only [DFacts.invSL_eq] using hk⟩

theorem card_centralizer_order5 :
    ∀ M : SL2, orderOf M = 5 →
    Nat.card (Subgroup.centralizer ({M} : Set SL2)) = 10 := by
  intro M hM
  rw [DFacts.natCard_centralizer_singleton]
  exact DFacts.chkCent5_spec M (DFacts.mem_sl2List M) (by rw [← DFacts.orderOf_SL2_eq, hM])

theorem card_centralizer_order3 :
    ∀ M : SL2, orderOf M = 3 →
    Nat.card (Subgroup.centralizer ({M} : Set SL2)) = 18 := by
  intro M hM
  rw [DFacts.natCard_centralizer_singleton]
  exact DFacts.chkCent3_spec M (DFacts.mem_sl2List M) (by rw [← DFacts.orderOf_SL2_eq, hM])

theorem centralizer_order5_odd :
    ∀ M : SL2, orderOf M = 5 →
    ∀ N ∈ Subgroup.centralizer ({M} : Set SL2), Odd (orderOf N) → N ∈ Subgroup.zpowers M := by
  intro M hM N hN hodd
  have h := DFacts.chkCentOdd5_spec M (DFacts.mem_sl2List M)
    (by rw [← DFacts.orderOf_SL2_eq, hM]) N (DFacts.mem_cent_of_mem_centralizer hN)
  have hodd' : ordL (innerL N) % 2 = 1 := by
    rw [← DFacts.orderOf_SL2_eq]
    exact Nat.odd_iff.mp hodd
  have hM' : M ∈ Subgroup.zpowers M := Subgroup.mem_zpowers M
  have hmul : ∀ {a b : SL2}, a ∈ Subgroup.zpowers M → b ∈ Subgroup.zpowers M →
      a * b ∈ Subgroup.zpowers M := fun ha hb => Subgroup.mul_mem _ ha hb
  rcases h with h | h | h | h | h | h
  · omega
  · rw [h]; exact Subgroup.one_mem _
  · rw [h]; exact hM'
  · rw [h]; exact hmul hM' hM'
  · rw [h]; exact hmul (hmul hM' hM') hM'
  · rw [h]; exact hmul (hmul (hmul hM' hM') hM') hM'

theorem centralizer_order3_odd :
    ∀ M : SL2, orderOf M = 3 →
    ∀ N ∈ Subgroup.centralizer ({M} : Set SL2), Odd (orderOf N) → ∃ n : ℕ, orderOf N = 3 ^ n := by
  intro M hM N hN hodd
  have h := DFacts.chkCentOdd3_spec M (DFacts.mem_sl2List M)
    (by rw [← DFacts.orderOf_SL2_eq, hM]) N (DFacts.mem_cent_of_mem_centralizer hN)
  have hodd' : ordL (innerL N) % 2 = 1 := by
    rw [← DFacts.orderOf_SL2_eq]
    exact Nat.odd_iff.mp hodd
  rcases h with h | h | h
  · omega
  · exact ⟨0, by rw [DFacts.orderOf_SL2_eq, h]; norm_num⟩
  · exact ⟨1, by rw [DFacts.orderOf_SL2_eq, h]; norm_num⟩

theorem sigma_not_conj_order3 :
    ∀ M : SL2, orderOf M = 3 →
    ∀ k : SL2, k * sigmaAut M * k⁻¹ ≠ M := by
  intro M hM k h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact DFacts.chkSigmaNotConj_spec M (DFacts.mem_sl2List M)
    (by rw [← DFacts.orderOf_SL2_eq, hM]) k (DFacts.mem_sl2List k) h

theorem exists_sq_minusOne : ∃ k : SL2, k * k = minusOne :=
  ⟨DFacts.jSL, DFacts.jSL_sq⟩

theorem exists_inverting_order3 :
    ∀ M : SL2, orderOf M = 3 →
    ∃ k : SL2, k * k = minusOne ∧ k * M * k⁻¹ = M⁻¹ := by
  intro M hM
  obtain ⟨k, -, hk1, hk2⟩ := DFacts.chkInvert3_spec M (DFacts.mem_sl2List M)
    (by rw [← DFacts.orderOf_SL2_eq, hM])
  exact ⟨k, hk1, by rw [mul_inv_eq_iff_eq_mul, hk2, DFacts.invSL_eq]⟩

theorem exists_Q16 :
    ∃ S : Subgroup SL2, Nat.card S = 16 ∧ minusOne ∈ S ∧
    (∀ s ∈ S, (∀ w ∈ S, s * w = w * s) → s = 1 ∨ s = minusOne) ∧
    (∀ s ∈ S, s * s = 1 → s = 1 ∨ s = minusOne) := by
  refine ⟨DFacts.monomialSL2, DFacts.natCard_monomialSL2, DFacts.minusOne_mem_monomialSL2, ?_,
    fun s _ hs => sl2_sq_eq_one_F9 s hs⟩
  intro s hs hc
  exact DFacts.chkQ16_spec s (DFacts.mem_sl2List s) (DFacts.mem_monomialSL2.mp hs)
    (fun w _ hw => hc w (DFacts.mem_monomialSL2.mpr hw))

end CFSG.GH74.GLS.Stage4.Q9
