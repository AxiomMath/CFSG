module

public import CFSG.LieType.SeitzGeneration.OutdiagHeisGen
public import CFSG.LieType.SeitzGeneration.HeisTorusCaseB
public import CFSG.LieType.SeitzGeneration.HeisLinearRoot

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Fin.NatCast Fin.CommRing

variable {F : Type} [Field F] {p : ℕ}

theorem companionMat_apply [NeZero p] (c : F) (i j : Fin p) :
    companionMat p c i j = if i = finRotate p j then (if (j : ℕ) = p - 1 then c else 1) else 0 := by
  have h := congrFun (companionMat_mulVec_single p c j) i
  rw [Matrix.mulVec_single_one] at h
  simp only [Matrix.col_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul] at h
  rw [h]
  by_cases h1 : i = finRotate p j <;> simp [h1]

theorem val_finRotate_eq [NeZero p] (j : Fin p) :
    ((finRotate p j : Fin p) : ℕ) = if (j : ℕ) + 1 < p then (j : ℕ) + 1 else 0 := by
  rw [val_finRotate_mod' (Nat.pos_of_ne_zero (NeZero.ne p)) j]
  have hj := j.isLt
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show (j : ℕ) + 1 = p by omega, Nat.mod_self]

theorem companionMat_apply_lt [NeZero p] (c : F) (i j : Fin p) (hj : (j : ℕ) + 1 < p) :
    companionMat p c i j = if (i : ℕ) = (j : ℕ) + 1 then 1 else 0 := by
  have hv : ((finRotate p j : Fin p) : ℕ) = (j : ℕ) + 1 := by
    rw [val_finRotate_eq, if_pos hj]
  have hne : (j : ℕ) ≠ p - 1 := by omega
  rw [companionMat_apply, if_neg hne]
  by_cases h : i = finRotate p j
  · have h' : (i : ℕ) = (j : ℕ) + 1 := by rw [h, hv]
    rw [if_pos h, if_pos h']
  · have h' : ¬ (i : ℕ) = (j : ℕ) + 1 := fun e => h (Fin.ext (by rw [hv]; exact e))
    rw [if_neg h, if_neg h']

theorem companionMat_apply_last [NeZero p] (c : F) (i j : Fin p) (hj : (j : ℕ) + 1 = p) :
    companionMat p c i j = if (i : ℕ) = 0 then c else 0 := by
  have hnl : ¬ ((j : ℕ) + 1 < p) := by omega
  have hv : ((finRotate p j : Fin p) : ℕ) = 0 := by
    rw [val_finRotate_eq, if_neg hnl]
  have hγ : (j : ℕ) = p - 1 := by omega
  rw [companionMat_apply, if_pos hγ]
  by_cases h : i = finRotate p j
  · have h' : (i : ℕ) = 0 := by rw [h, hv]
    rw [if_pos h, if_pos h']
  · have h' : ¬ (i : ℕ) = 0 := fun e => h (Fin.ext (by rw [hv]; exact e))
    rw [if_neg h, if_neg h']

theorem companionMat_succ_self [NeZero p] (c : F) (b : Fin p) :
    companionMat p c (b + 1) b = if (b : ℕ) = p - 1 then c else 1 := by
  rw [companionMat_apply, finRotate_apply, if_pos rfl]

theorem companionMat_pow_apply [NeZero p] (c : F) (m j : Fin p) :
    ∀ k : ℕ, k ≤ p → (companionMat p c ^ k) m j =
      if (j : ℕ) + k = (m : ℕ) then 1 else if (j : ℕ) + k = (m : ℕ) + p then c else 0 := by
  intro k
  induction k generalizing m j with
  | zero =>
    intro _
    rw [pow_zero, Matrix.one_apply, add_zero]
    by_cases h : m = j
    · subst h
      simp
    · have hm := m.isLt
      have hj := j.isLt
      rw [if_neg h, if_neg (show ¬ ((j : ℕ) = (m : ℕ)) from fun e => h (Fin.ext e.symm)),
        if_neg (show ¬ ((j : ℕ) = (m : ℕ) + p) by omega)]
  | succ k ih =>
    intro hk
    have hkp : k ≤ p := by omega
    have hsum : (companionMat p c ^ (k + 1)) m j =
        (companionMat p c ^ k) m (finRotate p j) * (if (j : ℕ) = p - 1 then c else 1) := by
      rw [pow_succ, Matrix.mul_apply]
      simp only [companionMat_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
    rw [hsum, ih m (finRotate p j) hkp, val_finRotate_eq]
    have hj := j.isLt
    have hm := m.isLt
    by_cases hj1 : (j : ℕ) + 1 < p
    · rw [if_pos hj1, if_neg (show ¬ ((j : ℕ) = p - 1) by omega), mul_one,
        show (j : ℕ) + 1 + k = (j : ℕ) + (k + 1) by omega]
    · have hjp : (j : ℕ) + 1 = p := by omega
      rw [if_neg hj1, if_pos (show (j : ℕ) = p - 1 by omega)]
      by_cases hkm : k = (m : ℕ)
      · rw [if_pos (show 0 + k = (m : ℕ) by omega),
          if_neg (show ¬ ((j : ℕ) + (k + 1) = (m : ℕ)) by omega),
          if_pos (show (j : ℕ) + (k + 1) = (m : ℕ) + p by omega), one_mul]
      · rw [if_neg (show ¬ (0 + k = (m : ℕ)) by omega),
          if_neg (show ¬ (0 + k = (m : ℕ) + p) by omega),
          if_neg (show ¬ ((j : ℕ) + (k + 1) = (m : ℕ)) by omega),
          if_neg (show ¬ ((j : ℕ) + (k + 1) = (m : ℕ) + p) by omega), zero_mul]

theorem companionMat_pow_self [NeZero p] (c : F) :
    companionMat p c ^ p = c • (1 : Matrix (Fin p) (Fin p) F) := by
  ext m j
  rw [companionMat_pow_apply c m j p le_rfl, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  have hm := m.isLt
  have hj := j.isLt
  by_cases h : m = j
  · subst h
    simp [NeZero.ne p]
  · rw [if_neg h, if_neg (show ¬ ((j : ℕ) + p = (m : ℕ)) by omega),
      if_neg (show ¬ ((j : ℕ) + p = (m : ℕ) + p) from fun e => h (Fin.ext (by omega)))]

theorem companionMat_sub_one_mul_geom [NeZero p] (c : F) :
    (companionMat p c - 1) * ∑ i ∈ Finset.range p, companionMat p c ^ i =
      (c - 1) • (1 : Matrix (Fin p) (Fin p) F) := by
  have key : ∀ n : ℕ, (companionMat p c - 1) * ∑ i ∈ Finset.range n, companionMat p c ^ i =
      companionMat p c ^ n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, sub_mul, one_mul, ← pow_succ']
      abel
  rw [key p, companionMat_pow_self, sub_smul, one_smul]

theorem geom_companionMat_apply [NeZero p] (c : F) (m j : Fin p) :
    (∑ i ∈ Finset.range p, companionMat p c ^ i) m j = if j ≤ m then 1 else c := by
  rw [Matrix.sum_apply]
  have hterm : ∀ i ∈ Finset.range p, (companionMat p c ^ i) m j =
      if (j : ℕ) + i = (m : ℕ) then 1 else if (j : ℕ) + i = (m : ℕ) + p then c else 0 :=
    fun i hi => companionMat_pow_apply c m j i (Finset.mem_range.1 hi).le
  rw [Finset.sum_congr rfl hterm]
  have hm := m.isLt
  have hj := j.isLt
  by_cases hjm : j ≤ m
  · have hjm' : (j : ℕ) ≤ (m : ℕ) := hjm
    rw [if_pos hjm]
    have hlt : (m : ℕ) - (j : ℕ) < p := by omega
    have e1 : (j : ℕ) + ((m : ℕ) - (j : ℕ)) = (m : ℕ) := by omega
    rw [Finset.sum_eq_single ((m : ℕ) - (j : ℕ))]
    · rw [if_pos e1]
    · intro i hi hne
      have hi' := Finset.mem_range.1 hi
      split_ifs with h1 h2
      · exfalso
        omega
      · exfalso
        omega
      · rfl
    · intro h
      exact absurd (Finset.mem_range.2 hlt) h
  · have hmj : (m : ℕ) < (j : ℕ) := by
      have : ¬ (j : ℕ) ≤ (m : ℕ) := fun h => hjm h
      omega
    rw [if_neg hjm]
    have hlt : (m : ℕ) + p - (j : ℕ) < p := by omega
    have e2 : (j : ℕ) + ((m : ℕ) + p - (j : ℕ)) = (m : ℕ) + p := by omega
    have e3 : ¬ ((j : ℕ) + ((m : ℕ) + p - (j : ℕ)) = (m : ℕ)) := by omega
    rw [Finset.sum_eq_single ((m : ℕ) + p - (j : ℕ))]
    · rw [if_neg e3, if_pos e2]
    · intro i hi hne
      have hi' := Finset.mem_range.1 hi
      split_ifs with h1 h2
      · exfalso
        omega
      · exfalso
        omega
      · rfl
    · intro h
      exact absurd (Finset.mem_range.2 hlt) h

theorem companionMat_mul_diagonal [NeZero p] (c : F) (t : Fin p → F) :
    companionMat p c * diagonal t = diagonal (fun i => t (i - 1)) * companionMat p c := by
  ext m j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, companionMat_apply]
  by_cases h : m = finRotate p j
  · have hj : m - 1 = j := by rw [h, finRotate_apply, add_sub_cancel_right]
    rw [if_pos h, hj, mul_comm]
  · rw [if_neg h, zero_mul, mul_zero]

theorem companionMat_pow_mul_diagonal [NeZero p] (c : F) (t : Fin p → F) (k : ℕ) :
    companionMat p c ^ k * diagonal t =
      diagonal (fun i => t (i - (k : Fin p))) * companionMat p c ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc companionMat p c ^ (k + 1) * diagonal t
        = companionMat p c * (companionMat p c ^ k * diagonal t) := by
          rw [pow_succ', mul_assoc]
      _ = companionMat p c * (diagonal (fun i => t (i - (k : Fin p))) * companionMat p c ^ k) := by
          rw [ih]
      _ = (companionMat p c * diagonal (fun i => t (i - (k : Fin p)))) * companionMat p c ^ k := by
          rw [mul_assoc]
      _ = (diagonal (fun i => t (i - 1 - (k : Fin p))) * companionMat p c) * companionMat p c ^ k := by
          rw [companionMat_mul_diagonal]
      _ = diagonal (fun i => t (i - ((k + 1 : ℕ) : Fin p))) * companionMat p c ^ (k + 1) := by
          rw [mul_assoc, ← pow_succ']
          congr 2
          funext i
          congr 1
          push_cast
          ring

theorem det_companionMat_sub_one (hp : Odd p) (c : F) : (companionMat p c - 1).det = c - 1 := by
  rcases Nat.lt_or_ge p 2 with hp2 | hp2
  · obtain rfl : p = 1 := by have := hp.pos; omega
    rw [Matrix.det_fin_one, Matrix.sub_apply, companionMat_apply, Matrix.one_apply_eq,
      if_pos (Subsingleton.elim (0 : Fin 1) (finRotate 1 0))]
    simp
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hn : Even n := by
    obtain ⟨r, hr⟩ := hp
    exact ⟨r, by omega⟩
  have hn1 : 1 ≤ n := by omega
  have h01 : (0 : Fin (n + 1)) ≠ Fin.last n := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  have hz : ((0 : Fin (n + 1)) : ℕ) + 1 < n + 1 := by
    rw [Fin.val_zero]
    omega
  have hA00 : (companionMat (n + 1) c - 1) 0 0 = -1 := by
    rw [Matrix.sub_apply, companionMat_apply_lt c 0 0 hz, Matrix.one_apply_eq]
    have hne : ¬ (((0 : Fin (n + 1)) : ℕ) = ((0 : Fin (n + 1)) : ℕ) + 1) := by omega
    rw [if_neg hne, zero_sub]
  have hA0l : (companionMat (n + 1) c - 1) 0 (Fin.last n) = c := by
    rw [Matrix.sub_apply, companionMat_apply_last c 0 (Fin.last n) (by rw [Fin.val_last]),
      Matrix.one_apply_ne h01]
    simp
  have hA0x : ∀ x : Fin (n + 1), x ≠ 0 → x ≠ Fin.last n →
      (companionMat (n + 1) c - 1) 0 x = 0 := by
    intro x hx0 hxl
    have hxn : (x : ℕ) ≠ n := fun h => hxl (Fin.ext (by rw [Fin.val_last]; exact h))
    have hx1 : (x : ℕ) + 1 < n + 1 := by
      have := x.isLt
      omega
    rw [Matrix.sub_apply, companionMat_apply_lt c 0 x hx1, Matrix.one_apply_ne (fun h => hx0 h.symm)]
    have hne : ¬ (((0 : Fin (n + 1)) : ℕ) = (x : ℕ) + 1) := by
      rw [Fin.val_zero]
      omega
    rw [if_neg hne, sub_zero]
  have hF4 : ∀ i j : Fin n, i < j → (companionMat (n + 1) c - 1) (Fin.succ i) (Fin.succ j) = 0 := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have hj := j.isLt
    have hne : (Fin.succ i : Fin (n + 1)) ≠ Fin.succ j := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_succ] at this
      omega
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    by_cases hl : (j : ℕ) + 1 < n
    · have hv : ((Fin.succ j : Fin (n + 1)) : ℕ) + 1 < n + 1 := by
        rw [Fin.val_succ]
        omega
      have hne2 : ¬ (((Fin.succ i : Fin (n + 1)) : ℕ) = ((Fin.succ j : Fin (n + 1)) : ℕ) + 1) := by
        rw [Fin.val_succ, Fin.val_succ]
        omega
      rw [companionMat_apply_lt c (Fin.succ i) (Fin.succ j) hv, if_neg hne2]
    · have hv : ((Fin.succ j : Fin (n + 1)) : ℕ) + 1 = n + 1 := by
        rw [Fin.val_succ]
        omega
      have hne2 : ¬ (((Fin.succ i : Fin (n + 1)) : ℕ) = 0) := by
        rw [Fin.val_succ]
        omega
      rw [companionMat_apply_last c (Fin.succ i) (Fin.succ j) hv, if_neg hne2]
  have hF5 : ∀ i : Fin n, (companionMat (n + 1) c - 1) (Fin.succ i) (Fin.succ i) = -1 := by
    intro i
    have hi := i.isLt
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    by_cases hl : (i : ℕ) + 1 < n
    · have hv : ((Fin.succ i : Fin (n + 1)) : ℕ) + 1 < n + 1 := by
        rw [Fin.val_succ]
        omega
      have hne2 : ¬ (((Fin.succ i : Fin (n + 1)) : ℕ) = ((Fin.succ i : Fin (n + 1)) : ℕ) + 1) := by
        omega
      rw [companionMat_apply_lt c (Fin.succ i) (Fin.succ i) hv, if_neg hne2, zero_sub]
    · have hv : ((Fin.succ i : Fin (n + 1)) : ℕ) + 1 = n + 1 := by
        rw [Fin.val_succ]
        omega
      have hne2 : ¬ (((Fin.succ i : Fin (n + 1)) : ℕ) = 0) := by
        rw [Fin.val_succ]
        omega
      rw [companionMat_apply_last c (Fin.succ i) (Fin.succ i) hv, if_neg hne2, zero_sub]
  have hF6 : ∀ i j : Fin n, j < i →
      (companionMat (n + 1) c - 1) (Fin.succ i) (Fin.castSucc j) = 0 := by
    intro i j hji
    have hji' : (j : ℕ) < (i : ℕ) := hji
    have hi := i.isLt
    have hj := j.isLt
    have hv : ((Fin.castSucc j : Fin (n + 1)) : ℕ) + 1 < n + 1 := by
      rw [Fin.coe_castSucc]
      omega
    have hne : (Fin.succ i : Fin (n + 1)) ≠ Fin.castSucc j := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.coe_castSucc] at this
      omega
    have hne2 : ¬ (((Fin.succ i : Fin (n + 1)) : ℕ) = ((Fin.castSucc j : Fin (n + 1)) : ℕ) + 1) := by
      rw [Fin.val_succ, Fin.coe_castSucc]
      omega
    rw [Matrix.sub_apply, companionMat_apply_lt c (Fin.succ i) (Fin.castSucc j) hv, if_neg hne2,
      Matrix.one_apply_ne hne, sub_zero]
  have hF7 : ∀ i : Fin n, (companionMat (n + 1) c - 1) (Fin.succ i) (Fin.castSucc i) = 1 := by
    intro i
    have hi := i.isLt
    have hv : ((Fin.castSucc i : Fin (n + 1)) : ℕ) + 1 < n + 1 := by
      rw [Fin.coe_castSucc]
      omega
    have hne : (Fin.succ i : Fin (n + 1)) ≠ Fin.castSucc i := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.coe_castSucc] at this
      omega
    have hval : ((Fin.succ i : Fin (n + 1)) : ℕ) = ((Fin.castSucc i : Fin (n + 1)) : ℕ) + 1 := by
      rw [Fin.val_succ, Fin.coe_castSucc]
    rw [Matrix.sub_apply, companionMat_apply_lt c (Fin.succ i) (Fin.castSucc i) hv,
      if_pos hval, Matrix.one_apply_ne hne, sub_zero]
  have hLow : ((companionMat (n + 1) c - 1).submatrix Fin.succ Fin.succ).IsLowerTriangular := by
    intro i j hij
    exact hF4 i j hij
  have hUp : ((companionMat (n + 1) c - 1).submatrix Fin.succ Fin.castSucc).IsUpperTriangular := by
    intro i j hij
    exact hF6 i j hij
  have hdet0 : ((companionMat (n + 1) c - 1).submatrix Fin.succ Fin.succ).det = (-1) ^ n := by
    rw [Matrix.det_of_isLowerTriangular _ hLow]
    simp [hF5]
  have hdetl : ((companionMat (n + 1) c - 1).submatrix Fin.succ Fin.castSucc).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hUp]
    simp [hF7]
  rw [Matrix.det_succ_row_zero, Fintype.sum_eq_add (0 : Fin (n + 1)) (Fin.last n) h01 ?_]
  · simp only [Fin.succAbove_zero, Fin.succAbove_last, Fin.val_zero, Fin.val_last, pow_zero,
      one_mul]
    rw [hdet0, hdetl, hA00, hA0l, Even.neg_one_pow hn]
    ring
  · rintro x ⟨hx0, hxl⟩
    rw [hA0x x hx0 hxl]
    simp

theorem exists_pow_mul_eq_pow_of_not_pow [Finite F] (hp : p.Prime) {c : Fˣ}
    (hc : ¬ ∃ μ : Fˣ, μ ^ p = c) (y : Fˣ) : ∃ m < p, ∃ μ : Fˣ, c ^ m * y = μ ^ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (hg c)
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 (hg y)
  have hpa : ¬ ((p : ℤ) ∣ a) := by
    rintro ⟨t, rfl⟩
    apply hc
    refine ⟨g ^ t, ?_⟩
    rw [← ha, ← _root_.zpow_natCast, ← _root_.zpow_mul]
    congr 1
    ring
  have hA : ((a : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hpa
  set m0 : ZMod p := -((b : ℤ) : ZMod p) * ((a : ℤ) : ZMod p)⁻¹ with hm0
  have hdiv : (p : ℤ) ∣ b + ((m0.val : ℕ) : ℤ) * a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, hm0, mul_assoc, inv_mul_cancel₀ hA, mul_one]
    exact add_neg_cancel _
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨m0.val, ZMod.val_lt m0, g ^ t, ?_⟩
  rw [← ha, ← hb, ← _root_.zpow_natCast (g ^ a) m0.val, ← _root_.zpow_mul, ← _root_.zpow_add,
    ← _root_.zpow_natCast (g ^ t) (p : ℕ), ← _root_.zpow_mul]
  congr 1
  linear_combination ht

@[expose] def singerT (l : F) : Fin p → F :=
  fun i => if (i : ℕ) = 0 then l else if (i : ℕ) = 1 then l⁻¹ else 1

@[expose] noncomputable def singerX (c l : F) : Matrix (Fin p) (Fin p) F :=
  (companionMat p c - 1) * diagonal (singerT l) * (companionMat p c - 1)⁻¹

theorem companionMat_sub_one_inv [NeZero p] {c : F} (hc : c - 1 ≠ 0) :
    (companionMat p c - 1)⁻¹ = (c - 1)⁻¹ • ∑ i ∈ Finset.range p, companionMat p c ^ i := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, companionMat_sub_one_mul_geom, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem singerX_sub_one_eq [NeZero p] {c : F} (hc : c - 1 ≠ 0) (l : F) :
    singerX c l - 1 = (c - 1)⁻¹ • ((companionMat p c - 1) *
      diagonal (fun i : Fin p => singerT l i - 1) * ∑ i ∈ Finset.range p, companionMat p c ^ i) := by
  have hE : diagonal (fun i : Fin p => singerT l i - 1) = diagonal (singerT l) - 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  have h1 : (c - 1)⁻¹ • ((companionMat p c - 1) * ∑ i ∈ Finset.range p, companionMat p c ^ i) =
      1 := by
    rw [companionMat_sub_one_mul_geom, smul_smul, inv_mul_cancel₀ hc, one_smul]
  unfold singerX
  have e : (companionMat p c - 1) * (diagonal (singerT l) - 1) *
      (∑ i ∈ Finset.range p, companionMat p c ^ i) =
        (companionMat p c - 1) * diagonal (singerT l) * (∑ i ∈ Finset.range p, companionMat p c ^ i) -
          (companionMat p c - 1) * (∑ i ∈ Finset.range p, companionMat p c ^ i) := by
    noncomm_ring
  rw [companionMat_sub_one_inv hc, Matrix.mul_smul, hE, e, smul_sub, h1]

theorem singerX_sub_one_apply [NeZero p] {c : F} (hc : c - 1 ≠ 0) (l : F) (a b : Fin p) :
    (singerX c l - 1) a b = (c - 1)⁻¹ * ∑ k : Fin p,
      (companionMat p c - 1) a k * (singerT l k - 1) *
        (∑ i ∈ Finset.range p, companionMat p c ^ i) k b := by
  rw [singerX_sub_one_eq hc, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]

theorem singerX_sub_one_apply_of_three_le [NeZero p] (hp : 3 ≤ p) {c : F} (hc1 : c ≠ 1) (l : F)
    {a : Fin p} (ha : 3 ≤ (a : ℕ)) (b : Fin p) : (singerX c l - 1) a b = 0 := by
  have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  rw [singerX_sub_one_apply hc]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ?_)
  by_cases hk : (k : ℕ) < 2
  · have hk1 : (k : ℕ) + 1 < p := by omega
    have hC : (companionMat p c - 1) a k = 0 := by
      have h1 : a ≠ k := fun h => by
        rw [h] at ha
        omega
      rw [Matrix.sub_apply, companionMat_apply_lt c a k hk1, Matrix.one_apply, if_neg h1,
        if_neg (show ¬ ((a : ℕ) = (k : ℕ) + 1) by omega), sub_zero]
    rw [hC, zero_mul, zero_mul]
  · have hk1 : singerT l k - 1 = 0 := by
      unfold singerT
      rw [if_neg (show ¬ ((k : ℕ) = 0) by omega), if_neg (show ¬ ((k : ℕ) = 1) by omega), sub_self]
    rw [hk1, mul_zero, zero_mul]

theorem singerX_sub_one_zero_apply [NeZero p] (hp : 3 ≤ p) {c : F} (hc1 : c ≠ 1) (l : F)
    {j : Fin p} (hj : 3 ≤ (j : ℕ)) :
    (singerX c l - 1) 0 j = -(l - 1) * c / (c - 1) := by
  have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  have h01 : ((0 : Fin p) : ℕ) + 1 < p := by
    rw [Fin.val_zero]
    omega
  rw [singerX_sub_one_apply hc, Finset.sum_eq_single (0 : Fin p)]
  · have hC0 : (companionMat p c - 1) 0 0 = -1 := by
      rw [Matrix.sub_apply, companionMat_apply_lt c 0 0 h01, Matrix.one_apply_eq]
      have hne : ¬ (((0 : Fin p) : ℕ) = ((0 : Fin p) : ℕ) + 1) := by omega
      rw [if_neg hne, zero_sub]
    have hs0 : singerT l (0 : Fin p) = l := by
      unfold singerT
      rw [if_pos (Fin.val_zero _)]
    have hN : (∑ i ∈ Finset.range p, companionMat p c ^ i) 0 j = c := by
      have hnle : ¬ (j ≤ 0) := fun h => by
        have := Fin.le_iff_val_le_val.1 h
        rw [Fin.val_zero] at this
        omega
      rw [geom_companionMat_apply, if_neg hnle]
    rw [hC0, hs0, hN, div_eq_mul_inv]
    ring
  · intro k _ hk
    have hk0 : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    by_cases hk1 : (k : ℕ) = 1
    · have h0k : (0 : Fin p) ≠ k := fun h => by
        have := congrArg Fin.val h
        rw [Fin.val_zero] at this
        omega
      have hC : (companionMat p c - 1) 0 k = 0 := by
        have hkp : (k : ℕ) + 1 < p := by omega
        rw [Matrix.sub_apply, companionMat_apply_lt c 0 k hkp, Matrix.one_apply, if_neg h0k,
          if_neg (show ¬ (((0 : Fin p) : ℕ) = (k : ℕ) + 1) by rw [Fin.val_zero]; omega), sub_zero]
      rw [hC, zero_mul, zero_mul]
    · have hk2 : singerT l k - 1 = 0 := by
        unfold singerT
        rw [if_neg hk0, if_neg hk1, sub_self]
      rw [hk2, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem single_mul_companion_eq [NeZero p] (c : F) {a b : Fin p} {d e : F}
    (h : e * (if (b : ℕ) = p - 1 then c else 1) = (if (a : ℕ) = p - 1 then c else 1) * d) :
    Matrix.single (a + 1) (b + 1) e * companionMat p c = companionMat p c * Matrix.single a b d := by
  ext x y
  by_cases hx : x = a + 1
  · rw [hx]
    by_cases hy : y = b
    · rw [hy, Matrix.single_mul_apply_same, Matrix.mul_single_apply_same, companionMat_succ_self,
        companionMat_succ_self, h]
    · have hne : b + 1 ≠ finRotate p y := by
        rw [finRotate_apply]
        intro hh
        exact hy (add_right_cancel hh).symm
      rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne (hbj := hy),
        companionMat_apply, if_neg hne, mul_zero]
  · rw [Matrix.single_mul_apply_of_ne (h := hx)]
    by_cases hy : y = b
    · have hne : x ≠ finRotate p a := by
        rw [finRotate_apply]
        exact hx
      rw [hy, Matrix.mul_single_apply_same, companionMat_apply, if_neg hne, zero_mul]
    · rw [Matrix.mul_single_apply_of_ne (hbj := hy)]

theorem eq_top_of_torus_companion_root [Fact p.Prime] (hp3 : 3 ≤ p) {c : F} (hc : c ≠ 0)
    {K : Subgroup (SpecialLinearGroup (Fin p) F)} (hT : ContainsDiagTorus K)
    (hC : ∀ g ∈ K, ∀ g' : SpecialLinearGroup (Fin p) F,
      (g' : Matrix (Fin p) (Fin p) F) * companionMat p c = companionMat p c * g → g' ∈ K)
    {i j : Fin p} (hij : i ≠ j) {d : F} (hd : d ≠ 0)
    (hx : Matrix.SpecialLinearGroup.transvection hij d ∈ K) : K = ⊤ := by
  haveI : NeZero p := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have hall : ∀ e : F, Matrix.SpecialLinearGroup.transvection hij e ∈ K := fun e =>
    transvection_mem_all_of_torus hT hp3 hij hd hx e
  have hstep : ∀ (a b : Fin p) (hab : a ≠ b),
      (∀ e : F, Matrix.SpecialLinearGroup.transvection hab e ∈ K) →
        ∀ e : F, Matrix.SpecialLinearGroup.transvection (shift_ne hab) e ∈ K := by
    intro a b hab h e
    have hga : (if (a : ℕ) = p - 1 then c else 1) ≠ 0 := by
      split_ifs <;> simp [hc]
    obtain ⟨dd, hdd⟩ : ∃ dd : F, e * (if (b : ℕ) = p - 1 then c else 1) =
        (if (a : ℕ) = p - 1 then c else 1) * dd :=
      ⟨e * (if (b : ℕ) = p - 1 then c else 1) * (if (a : ℕ) = p - 1 then c else 1)⁻¹, by
        rw [show (if (a : ℕ) = p - 1 then c else 1) * (e * (if (b : ℕ) = p - 1 then c else 1) *
            (if (a : ℕ) = p - 1 then c else 1)⁻¹) =
            e * (if (b : ℕ) = p - 1 then c else 1) * ((if (a : ℕ) = p - 1 then c else 1) *
            (if (a : ℕ) = p - 1 then c else 1)⁻¹) by ring, mul_inv_cancel₀ hga, mul_one]⟩
    apply hC _ (h dd)
    rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    congr 1
    exact single_mul_companion_eq c hdd
  have hshift : ∀ (n : ℕ) (a b : Fin p) (hab : a ≠ b), a = i + (n : Fin p) →
      b = j + (n : Fin p) → ∀ e : F, Matrix.SpecialLinearGroup.transvection hab e ∈ K := by
    intro n
    induction n with
    | zero =>
      intro a b hab ha hb e
      simp only [Nat.cast_zero, add_zero] at ha hb
      subst ha
      subst hb
      exact hall e
    | succ n ih =>
      intro a b hab ha hb e
      have hab' : i + (n : Fin p) ≠ j + (n : Fin p) := fun h => hij (add_right_cancel h)
      have h1 := hstep _ _ hab' (ih _ _ hab' rfl rfl) e
      have ea : a = i + (n : Fin p) + 1 := by
        rw [ha, Nat.cast_succ]
        ring
      have eb : b = j + (n : Fin p) + 1 := by
        rw [hb, Nat.cast_succ]
        ring
      rw [transvection_congr ea eb hab (shift_ne hab') e]
      exact h1
  have hδ0 : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
  have hprog : ∀ (a b : Fin p) (hab : a ≠ b), b = a + (j - i) →
      ∀ e : F, Matrix.SpecialLinearGroup.transvection hab e ∈ K := by
    intro a b hab hb e
    have hn : (((a - i).val : ℕ) : Fin p) = a - i := Fin.cast_val_eq_self _
    exact hshift (a - i).val a b hab (by rw [hn]; ring) (by rw [hb, hn]; ring) e
  have hprog' := transvection_mem_of_progression hp hδ0 hprog
  have htop : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup
      (ι := Fin p) (F := F))) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact hprog' t.i t.j t.hij t.c

theorem singerX_mem [Finite F] (hp : p.Prime) (hp5 : 5 ≤ p) {c : Fˣ}
    (hc : ¬ ∃ μ : Fˣ, μ ^ p = c) {l : F} (hl0 : l ≠ 0)
    {K : Subgroup (SpecialLinearGroup (Fin p) F)} (hT : ContainsDiagTorus K)
    (hL : ∀ g : SpecialLinearGroup (Fin p) F,
      (g : Matrix (Fin p) (Fin p) F) * companionMat p (c : F) =
        companionMat p (c : F) * (g : Matrix (Fin p) (Fin p) F) → g ∈ K) :
    ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) = singerX (c : F) l := by
  haveI : NeZero p := ⟨by omega⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hc1 : (c : F) - 1 ≠ 0 := by
    intro h
    apply hc
    refine ⟨1, Units.ext ?_⟩
    simp only [Units.val_pow_eq_pow_val, Units.val_one, one_pow]
    linear_combination -h
  obtain ⟨m, -, μ, hμ⟩ := exists_pow_mul_eq_pow_of_not_pow hp hc (Units.mk0 ((c : F) - 1) hc1)
  have hμF : (c : F) ^ m * ((c : F) - 1) = (μ : F) ^ p := by
    have h := congrArg Units.val hμ
    simpa [Units.val_pow_eq_pow_val] using h
  have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
  set C : Matrix (Fin p) (Fin p) F := companionMat p (c : F) with hCdef
  set M : Matrix (Fin p) (Fin p) F := C - 1 with hMdef
  have hdetC : C.det = (c : F) := det_companionMat hodd _
  have hdetM : M.det = (c : F) - 1 := det_companionMat_sub_one hodd _
  have hunitM : IsUnit M.det := by
    rw [hdetM]
    exact isUnit_iff_ne_zero.2 hc1
  have hCpow : Commute C (C ^ m) := Commute.self_pow C m
  have hMC : Commute M C := Commute.sub_left (Commute.refl C) (Commute.one_left C)
  have hMpow : Commute M (C ^ m) := Commute.sub_left hCpow (Commute.one_left _)
  have hCmM : Commute (C ^ m) M := hMpow.symm
  set b : Matrix (Fin p) (Fin p) F := (μ : F)⁻¹ • (C ^ m * M) with hbdef
  have hdetb : b.det = 1 := by
    rw [hbdef, Matrix.det_smul, Matrix.det_mul, Matrix.det_pow, hdetC, hdetM, Fintype.card_fin,
      hμF, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow]
  have hunitb : IsUnit b.det := by
    rw [hdetb]
    exact isUnit_one
  have hbC : b * C = C * b := by
    have hX : Commute (C ^ m * M) C := hCpow.symm.mul_left hMC
    rw [hbdef, Matrix.smul_mul, Matrix.mul_smul, hX.eq]
  let B : SpecialLinearGroup (Fin p) F := ⟨b, hdetb⟩
  have hBK : B ∈ K := hL B hbC
  have hne : -(m : Fin p) ≠ 1 - (m : Fin p) := by
    intro h
    have h1 : (1 : Fin p) = 0 := by linear_combination -h
    have h2 := congrArg Fin.val h1
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (show 1 < p by omega)] at h2
    exact absurd h2 one_ne_zero
  set T : SpecialLinearGroup (Fin p) F := diagAt hne l hl0 with hTdef
  have hTK : T ∈ K := hT T ⟨rootDiagT (-(m : Fin p)) (1 - (m : Fin p)) l, rfl⟩
  have hfun : (fun i : Fin p => rootDiagT (-(m : Fin p)) (1 - (m : Fin p)) l (i - (m : Fin p))) =
      singerT l := by
    funext i
    have e0 : i - (m : Fin p) = -(m : Fin p) ↔ (i : ℕ) = 0 := by
      rw [sub_eq_neg_self, Fin.ext_iff, Fin.val_zero]
    have e1 : i - (m : Fin p) = 1 - (m : Fin p) ↔ (i : ℕ) = 1 := by
      rw [sub_left_inj, Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt (show 1 < p by omega)]
    simp only [rootDiagT, singerT, e0, e1]
  have hDC : diagonal (singerT l) * C ^ m =
      C ^ m * diagonal (rootDiagT (-(m : Fin p)) (1 - (m : Fin p)) l) := by
    rw [hCdef, companionMat_pow_mul_diagonal, hfun]
  have hkey : singerX (c : F) l * b = b * diagonal (rootDiagT (-(m : Fin p)) (1 - (m : Fin p)) l) := by
    have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunitM
    have h3 : M * diagonal (singerT l) * M⁻¹ * (C ^ m * M) =
        C ^ m * M * diagonal (rootDiagT (-(m : Fin p)) (1 - (m : Fin p)) l) := by
      rw [hCmM.eq, Matrix.mul_assoc (M * diagonal (singerT l)) M⁻¹ (M * C ^ m),
        ← Matrix.mul_assoc M⁻¹ M (C ^ m), hinv, Matrix.one_mul,
        Matrix.mul_assoc M (diagonal (singerT l)) (C ^ m), hDC, Matrix.mul_assoc M (C ^ m)]
    show M * diagonal (singerT l) * M⁻¹ * b = b * diagonal (rootDiagT (-(m : Fin p)) (1 - (m : Fin p)) l)
    rw [hbdef, Matrix.mul_smul, Matrix.smul_mul, h3]
  refine ⟨B * T * B⁻¹, K.mul_mem (K.mul_mem hBK hTK) (K.inv_mem hBK), ?_⟩
  have hBinv : ((B⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) = b⁻¹ :=
    isolate_coe_inv_eq_of_mul_eq_one B (Matrix.mul_nonsing_inv b hunitb)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hBinv]
  show b * diagonal (rootDiagT (-(m : Fin p)) (1 - (m : Fin p)) l) * b⁻¹ = singerX (c : F) l
  calc b * diagonal (rootDiagT (-(m : Fin p)) (1 - (m : Fin p)) l) * b⁻¹
      = singerX (c : F) l * b * b⁻¹ := by rw [hkey]
    _ = singerX (c : F) l := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv b hunitb, Matrix.mul_one]

@[expose] noncomputable def companionConj (hodd : Odd p) {c : F} (hc : c ≠ 0) :
    SpecialLinearGroup (Fin p) F →* SpecialLinearGroup (Fin p) F :=
  MonoidHom.mk'
    (fun g => ⟨companionMat p c * (g : Matrix (Fin p) (Fin p) F) * (companionMat p c)⁻¹, by
      have hu : IsUnit (companionMat p c).det := by
        rw [det_companionMat hodd]
        exact isUnit_iff_ne_zero.2 hc
      have h1 := det_nonsing_inv_mul_det _ hu
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe]
      linear_combination h1⟩)
    (fun g h => by
      have hu : IsUnit (companionMat p c).det := by
        rw [det_companionMat hodd]
        exact isUnit_iff_ne_zero.2 hc
      have hinv : (companionMat p c)⁻¹ * companionMat p c = 1 := Matrix.nonsing_inv_mul _ hu
      apply Subtype.ext
      show companionMat p c * ((g : Matrix (Fin p) (Fin p) F) * (h : Matrix (Fin p) (Fin p) F)) *
          (companionMat p c)⁻¹ =
        (companionMat p c * (g : Matrix (Fin p) (Fin p) F) * (companionMat p c)⁻¹) *
          (companionMat p c * (h : Matrix (Fin p) (Fin p) F) * (companionMat p c)⁻¹)
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (companionMat p c)⁻¹ (companionMat p c), hinv, Matrix.one_mul])

theorem companionConj_coe (hodd : Odd p) {c : F} (hc : c ≠ 0)
    (g : SpecialLinearGroup (Fin p) F) :
    ((companionConj hodd hc g : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      companionMat p c * (g : Matrix (Fin p) (Fin p) F) * (companionMat p c)⁻¹ := rfl

theorem singerTorusGen_of_prime [Finite F] [Fact p.Prime] (hp : 5 ≤ p)
    (hpq : p ∣ Nat.card F - 1) : SingerTorusGen F p := by
  intro c hc K hT hL
  haveI : NeZero p := ⟨by omega⟩
  have hprime : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by omega
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hc1 : (c : F) ≠ 1 := by
    intro h
    exact hc ⟨1, Units.ext (by simp [h])⟩
  have hu : IsUnit (companionMat p (c : F)).det := by
    rw [det_companionMat hodd]
    exact isUnit_iff_ne_zero.2 hc0
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (SpecialLinearGroup (Fin p) F), H = Subgroup.closure
      ({g : SpecialLinearGroup (Fin p) F | ∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) = diagonal t} ∪
        {g : SpecialLinearGroup (Fin p) F | (g : Matrix (Fin p) (Fin p) F) * companionMat p (c : F) =
          companionMat p (c : F) * (g : Matrix (Fin p) (Fin p) F)}) := ⟨_, rfl⟩
  have hHK : H ≤ K := by
    rw [hH, Subgroup.closure_le]
    rintro g (⟨t, ht⟩ | hg)
    · exact hT g ⟨t, ht⟩
    · exact hL g hg
  have hTH : ContainsDiagTorus H := by
    intro g hg
    obtain ⟨t, ht⟩ := hg
    rw [hH]
    exact Subgroup.subset_closure (Set.mem_union_left _ ⟨t, ht⟩)
  have hLH : ∀ g : SpecialLinearGroup (Fin p) F,
      (g : Matrix (Fin p) (Fin p) F) * companionMat p (c : F) =
        companionMat p (c : F) * (g : Matrix (Fin p) (Fin p) F) → g ∈ H := by
    intro g hg
    rw [hH]
    exact Subgroup.subset_closure (Set.mem_union_right _ hg)
  have hstab : H ≤ H.comap (companionConj hodd hc0) := by
    rw [hH, Subgroup.closure_le]
    rintro g (⟨t, ht⟩ | hg)
    · show companionConj hodd hc0 g ∈ Subgroup.closure _
      apply Subgroup.subset_closure
      refine Set.mem_union_left _ ⟨fun i => t (i - 1), ?_⟩
      rw [companionConj_coe, ht, companionMat_mul_diagonal, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    · show companionConj hodd hc0 g ∈ Subgroup.closure _
      have hgeq : companionConj hodd hc0 g = g := Subtype.ext (by
        rw [companionConj_coe, ← hg, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one])
      rw [hgeq]
      exact Subgroup.subset_closure (Set.mem_union_right _ hg)
  have hCH : ∀ g ∈ H, ∀ g' : SpecialLinearGroup (Fin p) F,
      (g' : Matrix (Fin p) (Fin p) F) * companionMat p (c : F) =
        companionMat p (c : F) * (g : Matrix (Fin p) (Fin p) F) → g' ∈ H := by
    intro g hg g' hg'
    have hgeq : g' = companionConj hodd hc0 g := Subtype.ext (by
      rw [companionConj_coe]
      calc (g' : Matrix (Fin p) (Fin p) F)
          = ((g' : Matrix (Fin p) (Fin p) F) * companionMat p (c : F)) * (companionMat p (c : F))⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
        _ = companionMat p (c : F) * (g : Matrix (Fin p) (Fin p) F) * (companionMat p (c : F))⁻¹ := by
            rw [hg'])
    rw [hgeq]
    exact hstab hg
  obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
    classical
    by_contra hcon
    have hcon' : ∀ l : F, l ≠ 0 → l = 1 := fun l hl => by
      by_contra h1
      exact hcon ⟨l, hl, h1⟩
    haveI := Fintype.ofFinite F
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro l _
      by_cases h : l = 0
      · simp [h]
      · simp [hcon' l h]
    have h1 : Fintype.card F ≤ 2 :=
      calc Fintype.card F = (Finset.univ : Finset F).card := (Finset.card_univ).symm
        _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have h2 : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
    have h3 : 1 < Nat.card F := Finite.one_lt_card
    have hle : p ≤ Nat.card F - 1 := Nat.le_of_dvd (by omega) hpq
    omega
  obtain ⟨x, hxH, hxeq⟩ := singerX_mem hprime hp hc hl0 hTH hLH
  set I : Finset (Fin p) := Finset.univ.filter (fun a : Fin p => (a : ℕ) < 3) with hI
  have hY : ∀ a b : Fin p, a ∉ I → ((x : Matrix (Fin p) (Fin p) F) - 1) a b = 0 := by
    intro a b ha
    have h3 : 3 ≤ (a : ℕ) := by
      by_contra h
      exact ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩)
    rw [hxeq]
    exact singerX_sub_one_apply_of_three_le hp3 hc1 l h3 b
  have hjI : (⟨3, by omega⟩ : Fin p) ∉ I := fun h => lt_irrefl 3 (Finset.mem_filter.1 h).2
  have hj'I : (⟨4, by omega⟩ : Fin p) ∉ I := fun h => absurd (Finset.mem_filter.1 h).2 (by
    show ¬ ((4 : ℕ) < 3)
    omega)
  have hjj' : (⟨3, by omega⟩ : Fin p) ≠ ⟨4, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
  have hjne : ((x : Matrix (Fin p) (Fin p) F) - 1) *ᵥ
      Pi.single (⟨3, by omega⟩ : Fin p) 1 ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply, hxeq] at h0
    have hval := singerX_sub_one_zero_apply hp3 hc1 l (j := ⟨3, by omega⟩) (le_refl 3)
    rw [hval] at h0
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.2 (sub_ne_zero.2 hl1)) hc0)
      (sub_ne_zero.2 hc1) h0
  obtain ⟨a, b, hab, c', hc', g, hgH, hg⟩ :=
    caseB_isolate_of_range hp hl0 hl1 hTH hxH hY hjI hj'I hjj' hjne
  have htr : Matrix.SpecialLinearGroup.transvection hab c' ∈ H := by
    have hgt : g = Matrix.SpecialLinearGroup.transvection hab c' :=
      Subtype.ext (by rw [hg, Matrix.SpecialLinearGroup.transvection_coe])
    rw [← hgt]
    exact hgH
  have htop : H = ⊤ := eq_top_of_torus_companion_root hp3 hc0 hTH hCH hab hc' htr
  rw [htop, top_le_iff] at hHK
  exact hHK

theorem outdiagHeisenbergPlanes_holds : OutdiagHeisenbergPlanes :=
  outdiagHeisenbergPlanes_of_singer fun _ _ _ _ hp hp5 hpq =>
    haveI := Fact.mk hp; singerTorusGen_of_prime hp5 hpq

end CFSG.LieType.SeitzGeneration

end
