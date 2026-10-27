module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag3

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L52

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

@[expose] noncomputable def slEquivOfRingEquiv {K K' : Type*} [Field K] [Field K'] (e : K ≃+* K')
    (n : ℕ) : SpecialLinearGroup (Fin n) K ≃* SpecialLinearGroup (Fin n) K' := by
  refine MonoidHom.toMulEquiv (SpecialLinearGroup.map e.toRingHom)
    (SpecialLinearGroup.map e.symm.toRingHom) ?_ ?_
  · ext x i j
    simp
  · ext x i j
    simp

section Blocks

variable {K : Type*} [Field K] [Finite K]

theorem det_eq_one_of_monoidHom (hK : Nat.card K = 2) {Γ : Type*} [Group Γ] {m : ℕ}
    (f : Γ →* Matrix (Fin m) (Fin m) K) (g : Γ) : (f g).det = 1 := by
  have h1 : (f g).det * (f g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one]
  rcases eq_zero_or_eq_one_of_card_two hK (f g).det with h | h
  · rw [h, zero_mul] at h1
    exact absurd h1 zero_ne_one
  · exact h

variable {n : ℕ}

@[expose] noncomputable def blkSLTwo (hK : Nat.card K = 2)
    (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ) (h : a + m ≤ n)
    (hL : BlockLeft H a m) (hR : BlockRight H a m) : ↥H →* SpecialLinearGroup (Fin m) K where
  toFun g := ⟨blkMon H a m h hL hR g, det_eq_one_of_monoidHom hK (blkMon H a m h hL hR) g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem blkSLTwo_coe (hK : Nat.card K = 2) (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ)
    (h : a + m ≤ n) (hL : BlockLeft H a m) (hR : BlockRight H a m) (g : ↥H) :
    ((blkSLTwo hK H a m h hL hR g : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      blkAt a m h (g.1 : Matrix (Fin n) (Fin n) K) := rfl

theorem blkAt_one_eq_one (hK : Nat.card K = 2) (H : Subgroup (SpecialLinearGroup (Fin n) K))
    (a : ℕ) (h : a + 1 ≤ n) (hL : BlockLeft H a 1) (hR : BlockRight H a 1) (g : ↥H) :
    blkAt a 1 h (g.1 : Matrix (Fin n) (Fin n) K) = 1 := by
  have hd := det_eq_one_of_monoidHom hK (blkMon H a 1 h hL hR) g
  rw [Matrix.det_unique] at hd
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact hd

end Blocks

section Transvection

variable {K : Type*} [Field K] {n : ℕ}

theorem transvection_mem_upperTriangular {i j : Fin n} (hij : i < j) (c : K) :
    SpecialLinearGroup.transvection hij.ne c ∈ upperTriangular n K := by
  intro k l hlk
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hlk),
    Matrix.single_apply, zero_add]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    exact absurd (hij.trans hlk) (lt_irrefl _)
  · rfl

theorem transvection_mem_flagStabilizer {i j : Fin n} (hij : i < j) (c : K) (I : Set ℕ) :
    SpecialLinearGroup.transvection hij.ne c ∈ flagStabilizer n K I :=
  upperTriangular_le_flagStabilizer I (transvection_mem_upperTriangular hij c)

theorem blkAt_transvection {i j : Fin n} (hij : i ≠ j) (c : K) (a m : ℕ) (h : a + m ≤ n)
    (hnot : ¬ (a ≤ (i : ℕ) ∧ (i : ℕ) < a + m ∧ a ≤ (j : ℕ) ∧ (j : ℕ) < a + m)) :
    blkAt a m h ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
  ext p q
  have hc : ¬ (i = ⟨a + p, by have := p.isLt; omega⟩ ∧ j = ⟨a + q, by have := q.isLt; omega⟩) := by
    rintro ⟨h1, h2⟩
    apply hnot
    have hp := p.isLt
    have hq := q.isLt
    have e1 := congrArg Fin.val h1
    have e2 := congrArg Fin.val h2
    simp only at e1 e2
    omega
  rw [blkAt_apply, SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply]
  simp only [hc, Matrix.one_apply, Fin.mk.injEq, Nat.add_left_cancel_iff, Fin.val_inj, add_zero,
    ite_false]

theorem mul_single_apply' (x : Matrix (Fin n) (Fin n) K) (i j : Fin n) (c : K) (a b : Fin n) :
    (x * single i j c) a b = x a i * (if j = b then c else 0) := by
  by_cases hb : j = b
  · subst hb
    simp [Matrix.mul_single_apply_same]
  · simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hb), hb]

theorem single_mul_apply' (x : Matrix (Fin n) (Fin n) K) (i j : Fin n) (c : K) (a b : Fin n) :
    (single i j c * x) a b = (if i = a then c else 0) * x j b := by
  by_cases ha : i = a
  · subst ha
    simp [Matrix.single_mul_apply_same]
  · simp [Matrix.single_mul_apply_of_ne _ _ _ _ _ (Ne.symm ha), ha]

theorem transvection_commute_entry {x : SpecialLinearGroup (Fin n) K} {i j : Fin n} (hij : i ≠ j)
    (c : K)
    (h : x * SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection hij c * x)
    (a b : Fin n) :
    (x : Matrix (Fin n) (Fin n) K) a i * (if j = b then c else 0) =
      (if i = a then c else 0) * (x : Matrix (Fin n) (Fin n) K) j b := by
  have h1 : ((x * SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) a b =
      ((SpecialLinearGroup.transvection hij c * x : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) a b := by rw [h]
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    mul_single_apply', single_mul_apply'] at h1
  linear_combination h1

end Transvection

end CFSG.QuasithinUnique.Vol2Native.L239.L52
