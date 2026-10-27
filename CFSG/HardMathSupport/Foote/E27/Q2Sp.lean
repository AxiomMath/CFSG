module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.HardMathSupport.Foote.E27.Q2

open CFSG.Assembly.LowTwoRank Matrix

abbrev Jm (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 (-1) 0

abbrev mat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] (A : GL ι K) :
    Matrix ι ι K := A

def spSub (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n ⊕ Fin n) K) where
  carrier := {A | (mat A)ᵀ * Jm n K * mat A = Jm n K}
  mul_mem' := by
    intro A B hA hB
    change (mat A)ᵀ * Jm n K * mat A = Jm n K at hA
    change (mat B)ᵀ * Jm n K * mat B = Jm n K at hB
    change (mat (A * B))ᵀ * Jm n K * mat (A * B) = Jm n K
    have e : mat (A * B) = mat A * mat B := rfl
    rw [e, Matrix.transpose_mul]
    calc (mat B)ᵀ * (mat A)ᵀ * Jm n K * (mat A * mat B)
        = (mat B)ᵀ * ((mat A)ᵀ * Jm n K * mat A) * mat B := by simp only [Matrix.mul_assoc]
      _ = Jm n K := by rw [hA, hB]
  one_mem' := by
    change (mat 1)ᵀ * Jm n K * mat 1 = Jm n K
    have e : mat (1 : GL (Fin n ⊕ Fin n) K) = 1 := rfl
    rw [e]; simp
  inv_mem' := by
    intro A hA
    change (mat A)ᵀ * Jm n K * mat A = Jm n K at hA
    change (mat A⁻¹)ᵀ * Jm n K * mat A⁻¹ = Jm n K
    have h2 : mat A * mat A⁻¹ = 1 := by
      have := A.mul_inv
      exact_mod_cast this
    calc (mat A⁻¹)ᵀ * Jm n K * mat A⁻¹
        = (mat A⁻¹)ᵀ * ((mat A)ᵀ * Jm n K * mat A) * mat A⁻¹ := by rw [hA]
      _ = (mat A * mat A⁻¹)ᵀ * Jm n K * (mat A * mat A⁻¹) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Jm n K := by rw [h2]; simp

theorem mem_spSub {n : ℕ} {K : Type} [Field K] (A : GL (Fin n ⊕ Fin n) K) :
    A ∈ spSub n K ↔ (mat A)ᵀ * Jm n K * mat A = Jm n K := Iff.rfl

theorem statedSp_eq (n : ℕ) (K : Type) [Field K] : StatedSp n K = spSub n K := by
  unfold StatedSp
  exact Subgroup.closure_eq (spSub n K)

theorem mem_statedSp {n : ℕ} {K : Type} [Field K] (A : GL (Fin n ⊕ Fin n) K) :
    A ∈ StatedSp n K ↔
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Jm n K *
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Jm n K :=
  CFSG.Open.StatedAPI.mem_statedSp_iff


section Transport

variable {F L : Type} [Field F] [Field L]

@[expose] def glMap {ι : Type} [Fintype ι] [DecidableEq ι] (σ : F ≃+* L) : GL ι F ≃* GL ι L :=
  Units.mapEquiv (σ.mapMatrix : Matrix ι ι F ≃+* Matrix ι ι L).toMulEquiv

theorem mat_glMap {ι : Type} [Fintype ι] [DecidableEq ι] (σ : F ≃+* L) (A : GL ι F) :
    mat (glMap σ A) = (mat A).map σ := rfl

theorem glMap_mem_spSub {n : ℕ} (σ : F ≃+* L) (A : GL (Fin n ⊕ Fin n) F) :
    glMap σ A ∈ spSub n L ↔ A ∈ spSub n F := by
  change (mat (glMap σ A))ᵀ * Jm n L * mat (glMap σ A) = Jm n L ↔
    (mat A)ᵀ * Jm n F * mat A = Jm n F
  rw [mat_glMap]
  have hJ : Jm n L = (Jm n F).map σ := by
    ext (i | i) (j | j) <;> simp [Jm, Matrix.one_apply]
  have key : (((mat A).map σ)ᵀ * Jm n L * (mat A).map σ) =
      ((mat A)ᵀ * Jm n F * mat A).map σ := by
    rw [hJ, ← Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul]
  rw [key, hJ]
  exact ⟨fun h => Matrix.map_injective σ.injective h, fun h => by rw [h]⟩

def spSubEquiv (n : ℕ) (σ : F ≃+* L) : ↥(spSub n F) ≃* ↥(spSub n L) :=
  (MulEquiv.subgroupMap (glMap σ) (spSub n F)).trans
    (MulEquiv.subgroupCongr (by
      ext B
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨A, hA, rfl⟩
        exact (glMap_mem_spSub σ A).mpr hA
      · intro hB
        refine ⟨(glMap σ).symm B, (glMap_mem_spSub σ _).mp (by simpa using hB), by simp⟩))

end Transport

theorem statedScalars_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2) : StatedScalars ι F = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, rfl⟩
  have hc : c = 1 := by
    have h1 : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
    exact (Nat.card_eq_one_iff_unique.mp h1).1.elim c 1
  subst hc
  exact Subgroup.one_mem _

noncomputable def statedProjSpEquiv (n : ℕ) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : StatedProj (StatedSp n F) ≃* ↥(spSub n (ZMod 2)) := by
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rw [Fintype.card_eq_nat_card]; exact hF
  have hbot : (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F) = ⊥ := by
    rw [statedScalars_eq_bot hF]; simp
  refine (QuotientGroup.quotientMulEquivOfEq hbot).trans
    ((QuotientGroup.quotientBot).trans
      ((MulEquiv.subgroupCongr (statedSp_eq n F)).trans
        (spSubEquiv n (ZMod.ringEquivOfPrime F Nat.prime_two hF').symm)))

end CFSG.HardMathSupport.Foote.E27.Q2

end
