module

public import CFSG.LieType.Steinberg.Minuscule.E6Parity
public import CFSG.Adapters.TauCetiExceptional.MinusculeMatch

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule.E6BC

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.Minuscule
open CFSG.TauCetiBridge.Minuscule

local instance : NeZero Tag.E6.rank := ⟨by decide +kernel⟩
local instance : NeZero e6Data.d := ⟨by decide +kernel⟩

@[expose] def y1Word : List (Fin Tag.E6.rank) := [0, 2, 4, 5]

@[expose] def y2Word : List (Fin Tag.E6.rank) :=
  [0, 1, 2, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4]

@[expose] def wordPerm (w : List (Fin Tag.E6.rank)) : Equiv.Perm (Fin e6Data.d) :=
  (w.map e6ReflectionPerm).prod

private def wordValue (w : List (Fin Tag.E6.rank)) (a : ℕ) : ℕ :=
  w.foldr (fun i b => e6Data.weyl b i) a

private theorem wordPerm_val (w : List (Fin Tag.E6.rank)) (a : Fin e6Data.d) :
    (wordPerm w a : ℕ) = wordValue w a := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (e6ReflectionPerm i (wordPerm w a) : ℕ) = _
    rw [e6ReflectionPerm_val, ih]
    rfl

private theorem wordPerm_pow_val (w : List (Fin Tag.E6.rank)) (k : ℕ)
    (a : Fin e6Data.d) :
    ((wordPerm w ^ k) a : ℕ) = (wordValue w)^[k] a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, wordPerm_val, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

@[expose] def y1Perm : Equiv.Perm (Fin e6Data.d) := wordPerm y1Word
@[expose] def y2Perm : Equiv.Perm (Fin e6Data.d) := wordPerm y2Word

@[expose] def baseIndex : Fin 3 → Fin e6Data.d := ![12, 0, 4]

@[expose] def index (i : Fin 3 × Fin 3 × Fin 3) : Fin e6Data.d :=
  (y1Perm ^ i.2.1.val) ((y2Perm ^ i.2.2.val) (baseIndex i.1))

private def indexValue (i : Fin 3 × Fin 3 × Fin 3) : ℕ :=
  (wordValue y1Word)^[i.2.1.val]
    ((wordValue y2Word)^[i.2.2.val] (baseIndex i.1 : ℕ))

private theorem index_val (i : Fin 3 × Fin 3 × Fin 3) :
    (index i : ℕ) = indexValue i := by
  dsimp only [index, y1Perm, y2Perm, indexValue]
  rw [wordPerm_pow_val, wordPerm_pow_val]

theorem index_bijective : Function.Bijective index := by
  constructor
  · have h : Function.Injective indexValue := by decide +kernel
    intro i j hij
    apply h
    simpa only [index_val] using congrArg Fin.val hij
  · have h : ∀ j : Fin e6Data.d, ∃ i : Fin 3 × Fin 3 × Fin 3,
        indexValue i = j.val := by decide +kernel
    intro j
    obtain ⟨i, hi⟩ := h j
    exact ⟨i, Fin.ext (by rw [index_val, hi])⟩

@[expose] def indexEquiv : (Fin 3 × Fin 3 × Fin 3) ≃ Fin e6Data.d :=
  Equiv.ofBijective index index_bijective

section Actors

variable (K : Type*) [Field K]

variable [CharP K 2]

@[expose] def coords : (Fin e6Data.d →₀ K) ≃ₗ[K] ((Fin 3 × Fin 3 × Fin 3) → K) :=
  (Finsupp.linearEquivFunOnFinite K K (Fin e6Data.d)).trans
    (LinearEquiv.funCongrLeft K K indexEquiv)

omit
  [CharP K 2] in
@[simp] theorem coords_apply (v : Fin e6Data.d →₀ K) (i : Fin 3 × Fin 3 × Fin 3) :
    coords K v i = v (index i) := rfl

omit
  [CharP K 2] in
@[simp] theorem coords_symm_apply (v : (Fin 3 × Fin 3 × Fin 3) → K)
    (i : Fin 3 × Fin 3 × Fin 3) :
    (coords K).symm v (index i) = v i :=
  by simpa only [coords_apply] using congrFun ((coords K).apply_symm_apply v) i

end Actors

end CFSG.LieType.Steinberg.Minuscule.E6BC
