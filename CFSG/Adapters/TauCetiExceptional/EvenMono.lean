module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.TauCetiBridge.Even

structure MonoRoots (L : Type) [Field L] (n r : ℕ) where
  E : Fin r → Matrix (Fin n) (Fin n) L
  F : Fin r → Matrix (Fin n) (Fin n) L
  wt : Fin n → Fin r → ℤ
  refl : Fin r → Fin n → Fin n
  E_apply : ∀ i a b, E i a b = if wt b i = -1 ∧ a = refl i b then 1 else 0
  F_apply : ∀ i a b, F i a b = if wt b i = 1 ∧ a = refl i b then 1 else 0
  refl_refl : ∀ i b, refl i (refl i b) = b
  wt_refl : ∀ i b, wt (refl i b) i = -wt b i

namespace MonoRoots

variable {L : Type} [Field L] {n r : ℕ} (M : MonoRoots L n r)

theorem refl_eq_iff (i : Fin r) (a b : Fin n) : a = M.refl i b ↔ M.refl i a = b :=
  ⟨fun h => by rw [h, M.refl_refl], fun h => by rw [← h, M.refl_refl]⟩

theorem mul_E_apply (A : Matrix (Fin n) (Fin n) L) (i : Fin r) (a b : Fin n) :
    (A * M.E i) a b = if M.wt b i = -1 then A a (M.refl i b) else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (M.refl i b)]
  · rw [M.E_apply]
    by_cases h : M.wt b i = -1 <;> simp [h]
  · intro c _ hc
    rw [M.E_apply, ite_eq_right fun h => hc h.2, mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem mul_F_apply (A : Matrix (Fin n) (Fin n) L) (i : Fin r) (a b : Fin n) :
    (A * M.F i) a b = if M.wt b i = 1 then A a (M.refl i b) else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (M.refl i b)]
  · rw [M.F_apply]
    by_cases h : M.wt b i = 1 <;> simp [h]
  · intro c _ hc
    rw [M.F_apply, ite_eq_right fun h => hc h.2, mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem E_mul_apply (A : Matrix (Fin n) (Fin n) L) (i : Fin r) (a b : Fin n) :
    (M.E i * A) a b = if M.wt (M.refl i a) i = -1 then A (M.refl i a) b else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (M.refl i a)]
  · rw [M.E_apply]
    by_cases h : M.wt (M.refl i a) i = -1 <;> simp [h, M.refl_refl]
  · intro c _ hc
    rw [M.E_apply, ite_eq_right fun h => hc ((M.refl_eq_iff i a c).1 h.2).symm, zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem F_mul_apply (A : Matrix (Fin n) (Fin n) L) (i : Fin r) (a b : Fin n) :
    (M.F i * A) a b = if M.wt (M.refl i a) i = 1 then A (M.refl i a) b else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (M.refl i a)]
  · rw [M.F_apply]
    by_cases h : M.wt (M.refl i a) i = 1 <;> simp [h, M.refl_refl]
  · intro c _ hc
    rw [M.F_apply, ite_eq_right fun h => hc ((M.refl_eq_iff i a c).1 h.2).symm, zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem E_mul_F (i : Fin r) :
    M.E i * M.F i = Matrix.diagonal fun b => if M.wt b i = 1 then 1 else 0 := by
  ext a b
  rw [E_mul_apply, M.F_apply, M.wt_refl, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    by_cases h : M.wt a i = 1 <;> simp [h]
  · have hne : ¬M.refl i a = M.refl i b := fun h =>
      hab (by rw [← M.refl_refl i a, h, M.refl_refl])
    simp [hab, hne]

theorem F_mul_E (i : Fin r) :
    M.F i * M.E i = Matrix.diagonal fun b => if M.wt b i = -1 then 1 else 0 := by
  ext a b
  rw [F_mul_apply, M.E_apply, M.wt_refl, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    by_cases h : M.wt a i = -1
    · simp [h]
    · have h' : ¬-M.wt a i = 1 := fun e => h (by omega)
      simp [h, h']
  · have hne : ¬M.refl i a = M.refl i b := fun h =>
      hab (by rw [← M.refl_refl i a, h, M.refl_refl])
    simp [hab, hne]

theorem eq_zero_of_commute_diagonal {z : Matrix (Fin n) (Fin n) L} {d : Fin n → L}
    (h : z * Matrix.diagonal d = Matrix.diagonal d * z) {a b : Fin n} (hd : d a ≠ d b) :
    z a b = 0 := by
  have e := congrFun (congrFun h a) b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have e' : z a b * (d b - d a) = 0 := by rw [mul_sub, e, mul_comm, sub_self]
  exact (mul_eq_zero.1 e').resolve_right (sub_ne_zero.2 hd.symm)

theorem isDiag_of_commute (hinj : Function.Injective M.wt)
    (hwt : ∀ a i, M.wt a i = -1 ∨ M.wt a i = 0 ∨ M.wt a i = 1) {z : Matrix (Fin n) (Fin n) L}
    (hE : ∀ i, z * M.E i = M.E i * z) (hF : ∀ i, z * M.F i = M.F i * z) {a b : Fin n}
    (hab : a ≠ b) : z a b = 0 := by
  by_contra hz
  have hP : ∀ i, z * (M.E i * M.F i) = M.E i * M.F i * z := fun i => by
    rw [← Matrix.mul_assoc, hE i, Matrix.mul_assoc, hF i, Matrix.mul_assoc]
  have hQ : ∀ i, z * (M.F i * M.E i) = M.F i * M.E i * z := fun i => by
    rw [← Matrix.mul_assoc, hF i, Matrix.mul_assoc, hE i, Matrix.mul_assoc]
  apply hab
  refine hinj (funext fun i => ?_)
  have h1 : (M.wt a i = 1) ↔ (M.wt b i = 1) := by
    by_contra hne
    refine hz (eq_zero_of_commute_diagonal (d := fun c => if M.wt c i = 1 then (1 : L) else 0)
      (by rw [← M.E_mul_F]; exact hP i) ?_)
    by_cases ha : M.wt a i = 1 <;> by_cases hb : M.wt b i = 1 <;> simp_all
  have h2 : (M.wt a i = -1) ↔ (M.wt b i = -1) := by
    by_contra hne
    refine hz (eq_zero_of_commute_diagonal (d := fun c => if M.wt c i = -1 then (1 : L) else 0)
      (by rw [← M.F_mul_E]; exact hQ i) ?_)
    by_cases ha : M.wt a i = -1 <;> by_cases hb : M.wt b i = -1 <;> simp_all
  rcases hwt a i with ha | ha | ha <;> rcases hwt b i with hb | hb | hb <;> simp_all

theorem exists_ne_zero_of_mul_eq_one {z zi : Matrix (Fin n) (Fin n) L} (hzi : zi * z = 1)
    (b : Fin n) : ∃ a, z a b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have e := congrFun (congrFun hzi b) b
  simp only [Matrix.mul_apply, hcon, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at e
  exact zero_ne_one e

theorem wt_eq_one_iff_of_conj {m : ℕ} (blk : Fin n → Fin m) {z zi : Matrix (Fin n) (Fin n) L}
    (hzi : zi * z = 1) (hblk : ∀ a b, blk a ≠ blk b → z a b = 0) (π : Equiv.Perm (Fin r))
    {c : Fin r → L} (hc : ∀ j, c j ≠ 0) (hE : ∀ j, z * M.E j * zi = c j • M.E (π j))
    (hF : ∀ j, z * M.F j * zi = (c j)⁻¹ • M.F (π j)) {h : Fin n}
    (hh : ∀ i, M.wt h i ≠ -1) (hblock : ∀ b, blk b = blk h → b ≠ h → ∃ i, M.wt b i = -1)
    (j : Fin r) : M.wt h j = 1 ↔ M.wt h (π j) = 1 := by
  have hE' : ∀ j, z * M.E j = c j • (M.E (π j) * z) := fun j => by
    have e := congrArg (· * z) (hE j)
    simp only [Matrix.mul_assoc, hzi, Matrix.mul_one, Matrix.smul_mul] at e
    exact e
  have hF' : ∀ j, z * M.F j = (c j)⁻¹ • (M.F (π j) * z) := fun j => by
    have e := congrArg (· * z) (hF j)
    simp only [Matrix.mul_assoc, hzi, Matrix.mul_one, Matrix.smul_mul] at e
    exact e
  have hcol : ∀ b, b ≠ h → z b h = 0 := by
    intro b hb
    by_cases hbl : blk b = blk h
    · obtain ⟨i, hi⟩ := hblock b hbl hb
      have e := congrFun (congrFun (hE' (π.symm i)) (M.refl i b)) h
      rw [Equiv.apply_symm_apply, M.mul_E_apply, ite_eq_right (hh _), Matrix.smul_apply,
        M.E_mul_apply, M.refl_refl, ite_eq_left hi, smul_eq_mul] at e
      exact (mul_eq_zero.1 e.symm).resolve_left (hc _)
    · exact hblk b h hbl
  have hzh : z h h ≠ 0 := by
    obtain ⟨a, ha⟩ := exists_ne_zero_of_mul_eq_one hzi h
    by_cases hah : a = h
    · rwa [hah] at ha
    · exact absurd (hcol a hah) ha
  have key : ∀ a, (if M.wt h j = 1 then z a (M.refl j h) else 0) =
      (c j)⁻¹ * (if M.wt (M.refl (π j) a) (π j) = 1 then z (M.refl (π j) a) h else 0) := by
    intro a
    have e := congrFun (congrFun (hF' j) a) h
    rwa [M.mul_F_apply, Matrix.smul_apply, M.F_mul_apply, smul_eq_mul] at e
  constructor
  · intro hj
    by_contra hπ
    obtain ⟨a, ha⟩ := exists_ne_zero_of_mul_eq_one hzi (M.refl j h)
    apply ha
    have e := key a
    rw [ite_eq_left hj] at e
    rw [e]
    by_cases har : M.refl (π j) a = h
    · rw [har, ite_eq_right hπ, mul_zero]
    · rw [hcol _ har, ite_self, mul_zero]
  · intro hπ
    have e := key (M.refl (π j) h)
    rw [M.refl_refl, ite_eq_left hπ] at e
    by_contra hj
    rw [ite_eq_right hj] at e
    exact mul_ne_zero (inv_ne_zero (hc j)) hzh e.symm

end MonoRoots

end CFSG.TauCetiBridge.Even
