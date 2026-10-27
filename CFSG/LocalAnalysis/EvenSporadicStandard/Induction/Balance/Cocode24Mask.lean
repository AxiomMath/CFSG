module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Fix
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Tab
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

@[expose] def synOfMask (m : ℕ) : Syn := fun j => if m.testBit j then 1 else 0

theorem synOfMask_zero : synOfMask 0 = 0 := by
  funext j
  simp [synOfMask]

theorem synOfMask_xor (a b : ℕ) : synOfMask (a ^^^ b) = synOfMask a + synOfMask b := by
  funext j
  simp only [synOfMask, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit j <;> cases b.testBit j <;> decide

theorem synOfMask_injOn {m₁ m₂ : ℕ} (h₁ : m₁ < 4096) (h₂ : m₂ < 4096)
    (h : synOfMask m₁ = synOfMask m₂) : m₁ = m₂ := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have := congrFun h ⟨i, hi⟩
    simp only [synOfMask] at this
    by_cases h1 : m₁.testBit i = true <;> by_cases h2 : m₂.testBit i = true
    · rw [h1, h2]
    · simp [h1, h2] at this
    · simp [h1, h2] at this
    · simp only [Bool.not_eq_true] at h1 h2
      rw [h1, h2]
  · have hi' : 12 ≤ i := Nat.not_lt.1 hi
    have key : ∀ m : ℕ, m < 4096 → m.testBit i = false := fun m hm =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hm (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hi')))
    rw [key _ h₁, key _ h₂]

theorem synOfMask_surj (s : Syn) : ∃ m < 4096, synOfMask m = s := by
  have hinj : Function.Injective (fun m : Fin 4096 => synOfMask m.val) := fun a b h =>
    Fin.ext (synOfMask_injOn a.2 b.2 h)
  have hcard : Nat.card Syn ≤ Nat.card (Fin 4096) := by
    rw [card_syn, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  obtain ⟨m, hm⟩ := (hinj.bijective_of_nat_card_le hcard).2 s
  exact ⟨m.val, m.2, hm⟩

@[expose] def colMaskList : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 463, 512, 1024, 2048, 3824, 3491, 2908, 1397, 950, 2237, 3726,
    3163, 2663, 1945, 1898]

@[expose] def colMask (i : ℕ) : ℕ := colMaskList.getD i 0

theorem synOfMask_colMask (i : Fin 24) : synOfMask (colMask i) = col i := by
  revert i
  decide

theorem colMask_lt (i : ℕ) : colMask i < 4096 := by
  by_cases h : i < 24
  · have : ∀ j : Fin 24, colMask j < 4096 := by decide
    exact this ⟨i, h⟩
  · rw [colMask, List.getD_eq_default _ _ (by simp [colMaskList]; omega)]
    norm_num

@[expose] def pivotList : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12]

@[expose] def colsOfTab (t : Tab) : List ℕ := pivotList.map fun p => colMask (t.getD p 0)

@[expose] def xorImg : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, m => (if m % 2 = 1 then c else 0) ^^^ xorImg cs (m / 2)

theorem synOfMask_xorImg (cs : List ℕ) (m : ℕ) :
    synOfMask (xorImg cs m) =
      ∑ i ∈ Finset.range cs.length, if m.testBit i then synOfMask (cs.getD i 0) else 0 := by
  induction cs generalizing m with
  | nil => simp [xorImg, synOfMask_zero]
  | cons c cs ih =>
    rw [xorImg, synOfMask_xor, ih, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.testBit_succ, List.getD_cons_succ, Nat.testBit_zero, List.getD_cons_zero]
    rw [add_comm]
    congr 1
    by_cases h : m % 2 = 1 <;> simp [h, synOfMask_zero]

theorem colsOfTab_getD (t : Tab) (j : Fin 12) :
    (colsOfTab t).getD j 0 = colMask (t.getD (pivot j) 0) := by
  fin_cases j <;> rfl

theorem length_colsOfTab (t : Tab) : (colsOfTab t).length = 12 := rfl

theorem synOfMask_colsOfTab (σ : Perm (Fin 24)) (m : ℕ) :
    synOfMask (xorImg (colsOfTab (tabP σ)) m) = act σ (synOfMask m) := by
  rw [synOfMask_xorImg, act_apply, length_colsOfTab,
    ← Fin.sum_univ_eq_sum_range (fun i => if m.testBit i then
      synOfMask ((colsOfTab (tabP σ)).getD i 0) else 0) 12]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [colsOfTab_getD, getD_tabP, synOfMask_colMask]
  by_cases h : m.testBit j
  · have h1 : synOfMask m j = 1 := by simp [synOfMask, h]
    simp [h, h1]
  · have h1 : synOfMask m j = 0 := by simp [synOfMask, h]
    simp [h, h1]

theorem xorImg_lt (cs : List ℕ) (hcs : ∀ c ∈ cs, c < 4096) (m : ℕ) : xorImg cs m < 4096 := by
  have h2 : (4096 : ℕ) = 2 ^ 12 := by norm_num
  induction cs generalizing m with
  | nil => simp [xorImg]
  | cons c cs ih =>
    rw [xorImg, h2]
    refine Nat.xor_lt_two_pow ?_ ?_
    · split_ifs
      · rw [← h2]
        exact hcs c List.mem_cons_self
      · positivity
    · rw [← h2]
      exact ih (fun d hd => hcs d (List.mem_cons_of_mem _ hd)) _

theorem colsOfTab_lt (t : Tab) : ∀ c ∈ colsOfTab t, c < 4096 := by
  intro c hc
  simp only [colsOfTab, List.mem_map] at hc
  obtain ⟨p, -, rfl⟩ := hc
  exact colMask_lt _

theorem xorImg_eq_of_fixed {σ : Perm (Fin 24)} {m : ℕ} (hm : m < 4096)
    (h : act σ (synOfMask m) = synOfMask m) : xorImg (colsOfTab (tabP σ)) m = m := by
  refine synOfMask_injOn (xorImg_lt _ (colsOfTab_lt _) _) hm ?_
  rw [synOfMask_colsOfTab, h]

theorem synd_permW (σ : Perm (Fin 24)) (hσ : ∀ i, act σ (col i) = col (σ i)) (v : Word) :
    synd (permW σ v) = act σ (synd v) := by
  rw [synd_apply, synd_apply, map_sum]
  simp only [map_smul, hσ, permW_apply]
  refine (Equiv.sum_comp σ (fun i => v (σ⁻¹ i) • col i)).symm.trans ?_
  simp

theorem mem_aut_of_act_col {σ : Perm (Fin 24)} (hσ : ∀ i, act σ (col i) = col (σ i)) :
    σ ∈ aut := by
  have hmap : ∀ v ∈ golay, permW σ v ∈ golay := by
    intro v hv
    rw [golay, LinearMap.mem_ker] at hv ⊢
    rw [synd_permW σ hσ, hv, map_zero]
  intro v
  refine ⟨?_, hmap v⟩
  intro hv
  let φ : golay →ₗ[ZMod 2] golay := (permW σ).toLinearMap.restrict hmap
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    exact (permW σ).injective (congrArg Subtype.val hab)
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨permW σ v, hv⟩
  have : (w : Word) = v := (permW σ).injective (congrArg Subtype.val hw)
  rw [← this]
  exact w.2

@[expose] def autOK (t : Tab) : Bool :=
  (List.range 24).all fun i => xorImg (colsOfTab t) (colMask i) == colMask (t.getD i 0)

theorem mem_aut_of_autOK {σ : Perm (Fin 24)} (h : autOK (tabP σ) = true) : σ ∈ aut := by
  apply mem_aut_of_act_col
  intro i
  simp only [autOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h1 := h i i.2
  have h2 := congrArg synOfMask h1
  rw [synOfMask_colsOfTab, show (colMask i) = colMask i.val from rfl,
    synOfMask_colMask i, getD_tabP σ i, synOfMask_colMask (σ i)] at h2
  exact h2

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
