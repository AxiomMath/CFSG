module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type*} [Field F]

@[expose] def AgreeBelowFive (m : ℕ) (a b : Matrix (Fin 5) (Fin 5) F) : Prop :=
  ∀ i j : Fin 5, i < j → (j : ℕ) < i + m → a i j = b i j

theorem mul_single_apply_five (a b i j : Fin 5) (c : F) (M : Matrix (Fin 5) (Fin 5) F) :
    (M * single a b c) i j = if j = b then M i a * c else 0 := by
  split_ifs with h
  · subst h
    rw [mul_single_apply_same]
  · exact mul_single_apply_of_ne _ _ _ _ _ h M

theorem single_mul_apply_five (a b i j : Fin 5) (c : F) (M : Matrix (Fin 5) (Fin 5) F) :
    (single a b c * M) i j = if i = a then c * M b j else 0 := by
  split_ifs with h
  · subst h
    rw [single_mul_apply_same]
  · exact single_mul_apply_of_ne _ _ _ _ _ h M

theorem ypsMat_mul_apply_of_row (u v : unitriangular 5 F) {i j : Fin 5} (hij : i < j)
    (hrow : ∀ l : Fin 5, i < l → l < j → ypsMat u i l = 0) :
    (ypsMat u * ypsMat v) i j = ypsMat u i j + ypsMat v i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _)
    hij.ne, ypsMat_apply_self, ypsMat_apply_self, one_mul, mul_one, add_comm]
  intro l _ ⟨hli, hlj⟩
  rcases lt_or_gt_of_ne hli with h | h
  · rw [ypsMat_apply_of_lt u h, zero_mul]
  · rcases lt_or_gt_of_ne hlj with h' | h'
    · rw [hrow l h h', zero_mul]
    · rw [ypsMat_apply_of_lt v h', mul_zero]

theorem ypsMat_mul_apply_of_col (u v : unitriangular 5 F) {i j : Fin 5} (hij : i < j)
    (hcol : ∀ l : Fin 5, i < l → l < j → ypsMat v l j = 0) :
    (ypsMat u * ypsMat v) i j = ypsMat u i j + ypsMat v i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _)
    hij.ne, ypsMat_apply_self, ypsMat_apply_self, one_mul, mul_one, add_comm]
  intro l _ ⟨hli, hlj⟩
  rcases lt_or_gt_of_ne hli with h | h
  · rw [ypsMat_apply_of_lt u h, zero_mul]
  · rcases lt_or_gt_of_ne hlj with h' | h'
    · rw [hcol l h h', mul_zero]
    · rw [ypsMat_apply_of_lt v h', mul_zero]

section Finite

variable [Finite F]

@[expose] def uFiveHeight (m : ℕ) : Subgroup (unitriangular 5 F) :=
  uFiveSubgroupOfMulClosed {u | ∀ i j : Fin 5, i < j → (j : ℕ) < i + m → ypsMat u i j = 0}
    (fun i j hij _ => by rw [ypsMat_one, Matrix.one_apply_ne hij.ne])
    (fun u hu v hv i j hij hm => by
      rw [ypsMat_mul, ypsMat_mul_apply_of_row u v hij (fun l hil hlj => hu i l hil (by
        have : (l : ℕ) < j := hlj
        omega)), hu i j hij hm, hv i j hij hm, add_zero])

theorem uFiveHeight_one : uFiveHeight 1 = (⊤ : Subgroup (unitriangular 5 F)) := by
  refine eq_top_iff.2 fun u _ => ?_
  intro i j hij hm
  have : (i : ℕ) < j := hij
  omega

theorem uFiveHeight_five : uFiveHeight 5 = (⊥ : Subgroup (unitriangular 5 F)) := by
  refine eq_bot_iff.2 fun u hu => ?_
  rw [Subgroup.mem_bot]
  apply ypsMat_injective
  ext i j
  rw [ypsMat_one]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hu i j h (by omega), Matrix.one_apply_ne h.ne]
  · rw [ypsMat_apply_self, Matrix.one_apply_eq]
  · rw [ypsMat_apply_of_lt u h, Matrix.one_apply_ne h.ne']

theorem mul_inv_mem_uFiveHeight_iff {m : ℕ} (a b : unitriangular 5 F) :
    a * b⁻¹ ∈ uFiveHeight m ↔ AgreeBelowFive m (ypsMat a) (ypsMat b) := by
  set c := a * b⁻¹ with hc
  have hab : ypsMat a = ypsMat c * ypsMat b := by rw [← ypsMat_mul, hc, inv_mul_cancel_right]
  constructor
  · intro hcm i j hij hm
    rw [hab, ypsMat_mul_apply_of_row c b hij (fun l hil hlj => hcm i l hil (by
      have : (l : ℕ) < j := hlj
      omega)), hcm i j hij hm, zero_add]
  · intro hag
    suffices h : ∀ d : ℕ, ∀ i j : Fin 5, i < j → (j : ℕ) = i + d → d < m → ypsMat c i j = 0 from
      fun i j hij hm => h ((j : ℕ) - i) i j hij (by
        have : (i : ℕ) < j := hij
        omega) (by
        have : (i : ℕ) < j := hij
        omega)
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i j hij hd hdm
      have h1 := hag i j hij (by omega)
      rw [hab, ypsMat_mul_apply_of_row c b hij (fun l hil hlj => ih ((l : ℕ) - i) (by
        have : (l : ℕ) < j := hlj
        have : (i : ℕ) < l := hil
        omega) i l hil (by
        have : (i : ℕ) < l := hil
        omega) (by
        have : (l : ℕ) < j := hlj
        have : (i : ℕ) < l := hil
        omega))] at h1
      linear_combination h1

theorem agreeBelowFive_mul_of_mem {m : ℕ} {u : unitriangular 5 F} (hu : u ∈ uFiveHeight (m - 1))
    (v : unitriangular 5 F) : AgreeBelowFive m (ypsMat (u * v)) (ypsMat (v * u)) := by
  intro i j hij hm
  rw [ypsMat_mul, ypsMat_mul, ypsMat_mul_apply_of_row u v hij (fun l hil hlj => hu i l hil (by
      have : (l : ℕ) < j := hlj
      omega)),
    ypsMat_mul_apply_of_col v u hij (fun l hil hlj => hu l j hlj (by
      have : (i : ℕ) < l := hil
      omega)), add_comm]

omit [Finite F] in
theorem ypsMat_mul_uFiveRoot_succ_apply (u : unitriangular 5 F) (k : Fin 4) (c : F) (i j : Fin 5) :
    ypsMat (u * uFiveRoot k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)) c) i j =
        ypsMat u i j + if j = k.succ then ypsMat u i k.castSucc * c else 0 := by
  rw [ypsMat_mul, ypsMat_uFiveRoot, mul_add, mul_one, Matrix.add_apply, mul_single_apply_five]

omit [Finite F] in
theorem ypsMat_uFiveRoot_succ_mul_apply (u : unitriangular 5 F) (k : Fin 4) (c : F) (i j : Fin 5) :
    ypsMat (uFiveRoot k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)) c * u) i j =
        ypsMat u i j + if i = k.castSucc then c * ypsMat u k.succ j else 0 := by
  rw [ypsMat_mul, ypsMat_uFiveRoot, add_mul, one_mul, Matrix.add_apply, single_mul_apply_five]

theorem mem_uFiveHeight_of_agreeBelowFive {m : ℕ} (hm5 : m ≤ 5) {c : F} (hc : c ≠ 0)
    {u : unitriangular 5 F}
    (h : ∀ k : Fin 4, AgreeBelowFive m
      (ypsMat (u * uFiveRoot k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)) c))
      (ypsMat (uFiveRoot k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)) c * u))) :
    u ∈ uFiveHeight (m - 1) := by
  intro p q hpq hq
  have hpq' : (p : ℕ) < q := hpq
  by_cases hq3 : (q : ℕ) ≤ 3
  · let k : Fin 4 := ⟨q, by omega⟩
    have hk1 : k.castSucc = q := Fin.ext rfl
    have h1 := h k p k.succ (by
      change (p : ℕ) < (q : ℕ) + 1
      omega) (by
      change (q : ℕ) + 1 < p + m
      omega)
    rw [ypsMat_mul_uFiveRoot_succ_apply, ypsMat_uFiveRoot_succ_mul_apply, ite_eq_left rfl,
      ite_eq_right (by rw [hk1]; exact hpq.ne), add_zero, add_eq_left, hk1] at h1
    exact (mul_eq_zero.1 h1).resolve_right hc
  · have hq4 : (q : ℕ) = 4 := by omega
    have hp1 : 1 ≤ (p : ℕ) := by omega
    let k : Fin 4 := ⟨(p : ℕ) - 1, by omega⟩
    have hk2 : k.succ = p := Fin.ext (by
      change (p : ℕ) - 1 + 1 = p
      omega)
    have h1 := h k k.castSucc q (by
      change (p : ℕ) - 1 < q
      omega) (by
      change (q : ℕ) < (p : ℕ) - 1 + m
      omega)
    rw [ypsMat_mul_uFiveRoot_succ_apply, ypsMat_uFiveRoot_succ_mul_apply,
      ite_eq_right (by rw [hk2]; exact hpq.ne'), ite_eq_left rfl, add_zero, left_eq_add, hk2] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc

end Finite

end CFSG.SeitzReduction.LinearPilot
