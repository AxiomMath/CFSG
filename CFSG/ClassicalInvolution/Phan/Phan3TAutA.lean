module

public import CFSG.ClassicalInvolution.Phan.AutSU2
public import CFSG.ClassicalInvolution.Phan.Torus

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem diagConj_blockEmb (hK : Nat.card K = (p ^ f) ^ 2) {m k i : ℕ} (h : i + k ≤ m)
    (d : Fin m → normOne (unitaryInvolution K p f)) (A : Su K p f k) :
    diagConj p f hK d (blockEmb K p f m k i h A) =
      blockEmb K p f m k i h (diagConj p f hK (fun x => d (blockIdx i h x)) A) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_diagConj, Units.val_mul, Units.val_mul, coe_diagGL, coe_diagGL_inv, coe_coe_blockEmb]
  refine (diagonal_mul_blockMat_mul_diagonal h _ _ (fun a => ?_) _).trans ?_
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rfl

open scoped Matrix in
theorem autA_map_blockMat {F : Type*} [Field F] (φ : F ≃+* F) {m k i : ℕ}
    (A : Matrix (Fin k) (Fin k) F) : (blockMat m i A).map φ = blockMat m i (A.map φ) := by
  have hL : (blockSel F m k i).map φ = blockSel F m k i := by
    ext a j
    simp only [Matrix.map_apply, blockSel_apply]
    split_ifs <;> simp
  have hLt : ((blockSel F m k i)ᵀ).map φ = (blockSel F m k i)ᵀ := by
    rw [Matrix.transpose_map, hL]
  have hN : (A - 1).map φ = A.map φ - 1 := by
    rw [Matrix.map_sub _ (map_sub φ), Matrix.map_one _ (map_zero φ) (map_one φ)]
  unfold blockMat
  rw [Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_mul,
    Matrix.map_mul, hL, hLt, hN]

theorem fieldAutSU_blockEmb (φ : K ≃+* K) {m k i : ℕ} (h : i + k ≤ m) (A : Su K p f k) :
    fieldAutSU p f φ m (blockEmb K p f m k i h A) =
      blockEmb K p f m k i h (fieldAutSU p f φ k A) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_coe_fieldAutSU, coe_coe_blockEmb, coe_coe_blockEmb, coe_coe_fieldAutSU]
  exact autA_map_blockMat φ _

theorem diagConj_two (hK : Nat.card K = (p ^ f) ^ 2) (a b a' b' : normOne (unitaryInvolution K p f))
    (h : a * b⁻¹ = a' * b'⁻¹) : diagConj p f hK ![a, b] = diagConj p f hK ![a', b'] := by
  have key : ∀ (e : Fin 2 → normOne (unitaryInvolution K p f)) (A : Su K p f 2),
      diagConj p f hK e A = conjDiag hK e A := fun e A => rfl
  refine MulEquiv.ext fun A => ?_
  rw [key, key, conjDiag_two hK a b, conjDiag_two hK a' b', h]

theorem blockAut4_blockEmb2 (hK : Nat.card K = (p ^ f) ^ 2)
    (x : Fin 4 → normOne (unitaryInvolution K p f)) (φ : K ≃+* K) (k : Fin 3) (A : Su K p f 2) :
    (diagConj p f hK x * fieldAutSU p f φ 4) (blockEmb2 K p f 3 k A) =
      blockEmb2 K p f 3 k
        ((diagConj p f hK ![x k.castSucc, x k.succ] * fieldAutSU p f φ 2) A) := by
  have h2 : (fun y : Fin 2 => x (blockIdx (k : ℕ) (by omega : (k : ℕ) + 2 ≤ 3 + 1) y)) =
      ![x k.castSucc, x k.succ] := by
    funext y
    fin_cases y
    · rfl
    · rfl
  show diagConj p f hK x (fieldAutSU p f φ 4 (blockEmb K p f (3 + 1) 2 k _ A)) =
    blockEmb K p f (3 + 1) 2 k _ (diagConj p f hK ![x k.castSucc, x k.succ]
      (fieldAutSU p f φ 2 A))
  rw [fieldAutSU_blockEmb, diagConj_blockEmb, h2]

theorem exists_diag_of_ratios (r : Fin 3 → normOne (unitaryInvolution K p f)) :
    ∃ x : Fin 4 → normOne (unitaryInvolution K p f),
      ∀ k : Fin 3, x k.castSucc * (x k.succ)⁻¹ = r k := by
  refine ⟨![r 0 * r 1 * r 2, r 1 * r 2, r 2, 1], fun k => ?_⟩
  fin_cases k
  · show r 0 * r 1 * r 2 * (r 1 * r 2)⁻¹ = r 0
    group
  · show r 1 * r 2 * (r 2)⁻¹ = r 1
    group
  · show r 2 * (1 : normOne (unitaryInvolution K p f))⁻¹ = r 2
    group

end CFSG.ClassicalInvolution.Phan.Q3G
