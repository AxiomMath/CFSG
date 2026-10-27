module

public import CFSG.ClassicalInvolution.Q3.AE.Models
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Matrix

@[expose] def fanoVec : Fin 7 → (Fin 3 → ZMod 2) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![0, 1, 1], ![1, 1, 1], ![1, 0, 1]]

@[expose] def fanoIdx (v : Fin 3 → ZMod 2) : Fin 7 :=
  if v = fanoVec 0 then 0 else if v = fanoVec 1 then 1 else if v = fanoVec 2 then 2 else
    if v = fanoVec 3 then 3 else if v = fanoVec 4 then 4 else if v = fanoVec 5 then 5 else 6

theorem fanoIdx_fanoVec : ∀ i, fanoIdx (fanoVec i) = i := by decide

theorem fanoVec_fanoIdx : ∀ v : Fin 3 → ZMod 2, v ≠ 0 → fanoVec (fanoIdx v) = v := by decide

theorem fanoVec_ne_zero : ∀ i, fanoVec i ≠ 0 := by decide

theorem fanoVec_injective : Function.Injective fanoVec := fun i j h => by
  rw [← fanoIdx_fanoVec i, h, fanoIdx_fanoVec]

theorem mem_fanoLines_iff : ∀ a b c : Fin 7,
    ({a, b, c} : Finset (Fin 7)) ∈ fanoLines ↔ a ≠ b ∧ fanoVec a + fanoVec b = fanoVec c := by
  decide

theorem exists_of_mem_fanoLines {s : Finset (Fin 7)} (hs : s ∈ fanoLines) :
    ∃ a b c : Fin 7, s = {a, b, c} ∧ a ≠ b ∧ fanoVec a + fanoVec b = fanoVec c := by
  simp only [fanoLines, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, 3, rfl, by decide, by decide⟩
  · exact ⟨1, 2, 4, rfl, by decide, by decide⟩
  · exact ⟨2, 3, 5, rfl, by decide, by decide⟩
  · exact ⟨3, 4, 6, rfl, by decide, by decide⟩
  · exact ⟨4, 5, 0, rfl, by decide, by decide⟩
  · exact ⟨5, 6, 1, rfl, by decide, by decide⟩
  · exact ⟨6, 0, 2, rfl, by decide, by decide⟩

theorem mulVec_ne_zero (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) {v : Fin 3 → ZMod 2}
    (hv : v ≠ 0) : A.1 *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have hinv : (A⁻¹).1 * A.1 = 1 := congrArg Subtype.val (inv_mul_cancel A)
  have : (A⁻¹).1 *ᵥ (A.1 *ᵥ v) = v := by
    rw [mulVec_mulVec, hinv, one_mulVec]
  rw [← this, h, mulVec_zero]

@[expose] def lapply (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (i : Fin 7) : Fin 7 :=
  fanoIdx (A.1 *ᵥ fanoVec i)

theorem fanoVec_lapply (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (i : Fin 7) :
    fanoVec (lapply A i) = A.1 *ᵥ fanoVec i :=
  fanoVec_fanoIdx _ (mulVec_ne_zero A (fanoVec_ne_zero i))

theorem lapply_mul (A B : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (i : Fin 7) :
    lapply (A * B) i = lapply A (lapply B i) := by
  unfold lapply
  rw [fanoVec_fanoIdx _ (mulVec_ne_zero B (fanoVec_ne_zero i)), mulVec_mulVec]
  rfl

theorem lapply_one (i : Fin 7) : lapply 1 i = i := by
  unfold lapply
  rw [show (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)).1 = 1 from rfl, one_mulVec,
    fanoIdx_fanoVec]

@[expose] def lperm (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Equiv.Perm (Fin 7) where
  toFun := lapply A
  invFun := lapply A⁻¹
  left_inv i := by rw [← lapply_mul, inv_mul_cancel, lapply_one]
  right_inv i := by rw [← lapply_mul, mul_inv_cancel, lapply_one]

theorem lperm_apply (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (i : Fin 7) :
    lperm A i = lapply A i := rfl

theorem lperm_one : lperm 1 = 1 := by
  refine Equiv.ext fun i => ?_
  rw [lperm_apply, lapply_one]
  rfl

theorem lperm_mul (A B : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    lperm (A * B) = lperm A * lperm B := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.mul_apply, lperm_apply, lperm_apply, lperm_apply, lapply_mul]

@[expose] def lpermHom : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* Equiv.Perm (Fin 7) where
  toFun := lperm
  map_one' := lperm_one
  map_mul' := lperm_mul

theorem lpermHom_apply (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (i : Fin 7) :
    lpermHom A i = lapply A i := rfl

theorem map_mem_fanoLines (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) {s : Finset (Fin 7)}
    (hs : s ∈ fanoLines) : s.map (lpermHom A).toEmbedding ∈ fanoLines := by
  obtain ⟨a, b, c, rfl, hab, habc⟩ := exists_of_mem_fanoLines hs
  simp only [Finset.map_insert, Finset.map_singleton]
  rw [mem_fanoLines_iff]
  refine ⟨fun h => hab ((lpermHom A).injective h), ?_⟩
  show fanoVec (lapply A a) + fanoVec (lapply A b) = fanoVec (lapply A c)
  rw [fanoVec_lapply, fanoVec_lapply, fanoVec_lapply, ← mulVec_add, habc]

theorem lpermHom_mem_l32 (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : lpermHom A ∈ l32 :=
  fun s hs => ⟨map_mem_fanoLines A hs, by
    rw [← map_inv]
    exact map_mem_fanoLines A⁻¹ hs⟩

end CFSG.ClassicalInvolution.Q3.TL4
