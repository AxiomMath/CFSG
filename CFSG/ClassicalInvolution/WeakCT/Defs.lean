module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.ClassicalInvolution.WeakCT

open Matrix
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_mul blockMat_one det_blockMat)
open scoped MatrixGroups

section Blocks

variable (K : Type) [Field K]

@[expose] def blockSL (m k i : ℕ) (h : i + k ≤ m) : SL(k, K) →* SL(m, K) where
  toFun A := ⟨blockMat m i (A : Matrix (Fin k) (Fin k) K), by rw [det_blockMat h, A.2]⟩
  map_one' := Subtype.ext blockMat_one
  map_mul' A B := Subtype.ext (blockMat_mul h (A : Matrix (Fin k) (Fin k) K) B)

variable {K}

theorem coe_blockSL {m k i : ℕ} (h : i + k ≤ m) (A : SL(k, K)) :
    ((blockSL K m k i h A : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      blockMat m i (A : Matrix (Fin k) (Fin k) K) :=
  rfl

variable (K)

@[expose] def blockSL2 (n : ℕ) (i : Fin n) : SL(2, K) →* SL(n + 1, K) :=
  blockSL K (n + 1) 2 i (by omega)

@[expose] def blockSL3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) : SL(3, K) →* SL(n + 1, K) :=
  blockSL K (n + 1) 3 i (by omega)

@[expose] def B12 : Subgroup SL(3, K) :=
  (blockSL K 3 2 0 (by omega)).range

@[expose] def B23 : Subgroup SL(3, K) :=
  (blockSL K 3 2 1 (by omega)).range

end Blocks

section Systems

variable (K : Type) [Field K]

@[expose] def LinearBlockStandardPair {X : Type} [Group X] (W U V : Subgroup X) : Prop :=
  ∃ (θ : SL(3, K) →* X) (c : SL(3, K)), θ.range = W ∧ θ.ker ≤ Subgroup.center SL(3, K) ∧
    ((((B12 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ = U ∧
      ((B23 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ = V) ∨
     (((B12 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ = V ∧
      ((B23 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ = U))

structure WeakCTSystem {X : Type} [Group X] (n : ℕ) (U : Fin n → Subgroup X)
    (W : Fin n → Fin n → Subgroup X) : Prop where
  iso : ∀ i, Nonempty (SL(2, K) ≃* U i)
  join : ∀ i j, i < j → W i j = U i ⊔ U j
  comm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x
  pair : ∀ i j : Fin n, (j : ℕ) = i + 1 → LinearBlockStandardPair K (W i j) (U i) (U j)
  gen : ⨆ i, U i = ⊤

structure CTFamily (Y : Type) [Group Y] (n : ℕ) where
  ι : Fin n → (SL(2, K) →* Y)
  θ : Fin n → (SL(3, K) →* Y)
  left : ∀ i : Fin n, (i : ℕ) + 1 < n → (θ i).comp (blockSL K 3 2 0 (by omega)) = ι i
  right : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
    (θ i).comp (blockSL K 3 2 1 (by omega)) = ι ⟨i + 1, h⟩
  comm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ a b, ι i a * ι j b = ι j b * ι i a

end Systems

end CFSG.ClassicalInvolution.WeakCT
