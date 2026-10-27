module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix

section CentreGroup

variable {K : Type*} [Field K]

theorem sl3_det_one_add_vecMulVec (v φ : Fin 3 → K) :
    (1 + vecMulVec v φ : Matrix (Fin 3) (Fin 3) K).det = 1 + φ ⬝ᵥ v := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

theorem sl3_one_add_vecMulVec_mul (v φ ψ : Fin 3 → K) (hφ : φ ⬝ᵥ v = 0) :
    (1 + vecMulVec v φ : Matrix (Fin 3) (Fin 3) K) * (1 + vecMulVec v ψ) =
      1 + vecMulVec v (φ + ψ) := by
  rw [vecMulVec_add]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    vecMulVec_mul_vecMulVec, hφ, zero_smul, vecMulVec_zero, add_zero]
  abel

theorem sl3_pow_one_add_vecMulVec (v φ : Fin 3 → K) (hφ : φ ⬝ᵥ v = 0) (n : ℕ) :
    (1 + vecMulVec v φ : Matrix (Fin 3) (Fin 3) K) ^ n = 1 + vecMulVec v (n • φ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, sl3_one_add_vecMulVec_mul v (n • φ) φ
      (by rw [smul_dotProduct, hφ, smul_zero]), succ_nsmul]

def sl3CentreGroup (v : Fin 3 → K) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∃ φ : Fin 3 → K, φ ⬝ᵥ v = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec v φ}
  one_mem' := ⟨0, by simp, by simp⟩
  mul_mem' := by
    rintro g h ⟨φ, hφ, hg⟩ ⟨ψ, hψ, hh⟩
    refine ⟨φ + ψ, by rw [add_dotProduct, hφ, hψ, add_zero], ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hg, hh, sl3_one_add_vecMulVec_mul v φ ψ hφ]
  inv_mem' := by
    rintro g ⟨φ, hφ, hg⟩
    refine ⟨-φ, by rw [neg_dotProduct, hφ, neg_zero], ?_⟩
    have h1 : (g : Matrix (Fin 3) (Fin 3) K) * (1 + vecMulVec v (-φ)) = 1 := by
      rw [hg, sl3_one_add_vecMulVec_mul v φ (-φ) hφ, add_neg_cancel, vecMulVec_zero, add_zero]
    have h2 : adjugate (g : Matrix (Fin 3) (Fin 3) K) * g = 1 := by
      rw [adjugate_mul, Matrix.SpecialLinearGroup.det_coe, one_smul]
    rw [Matrix.SpecialLinearGroup.coe_inv]
    calc adjugate (g : Matrix (Fin 3) (Fin 3) K)
        = adjugate (g : Matrix (Fin 3) (Fin 3) K) * (g * (1 + vecMulVec v (-φ))) := by
          rw [h1, Matrix.mul_one]
      _ = 1 + vecMulVec v (-φ) := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem isPGroup_sl3CentreGroup (r : ℕ) [Fact r.Prime] [CharP K r] (v : Fin 3 → K) :
    IsPGroup r (sl3CentreGroup v) := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨φ, hφ, hg⟩ := g.2
  apply Subtype.ext
  apply Subtype.ext
  have hr : r • φ = 0 := by rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  simp only [pow_one, Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow, hg,
    sl3_pow_one_add_vecMulVec v φ hφ, hr, vecMulVec_zero, add_zero, Subgroup.coe_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem sl3CentreGroup_ne_bot (v : Fin 3 → K) (hv : v ≠ 0) : sl3CentreGroup v ≠ ⊥ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun k => by simpa using not_exists.mp h k)
  have hne : ∀ k : Fin 3, k + 1 ≠ k := by decide
  have hij := hne i
  let φ : Fin 3 → K := v (i + 1) • Pi.single i 1 - v i • Pi.single (i + 1) 1
  have hφv : φ ⬝ᵥ v = 0 := by
    simp [φ, sub_dotProduct, smul_dotProduct, mul_comm]
  have hφ0 : φ ≠ 0 := by
    intro h
    have h' := congrFun h (i + 1)
    simp [φ, hij, hi] at h'
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨⟨1 + vecMulVec v φ, ?_⟩, φ, hφv, rfl⟩, ?_⟩
  · rw [sl3_det_one_add_vecMulVec, hφv, add_zero]
  · intro h
    have h' := congrArg (fun g : ↥(sl3CentreGroup v) =>
      ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
    simp only [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one,
      add_eq_left, vecMulVec_eq_zero] at h'
    rcases h' with h' | h'
    · exact hv h'
    · exact hφ0 h'

theorem conj_mem_sl3CentreGroup (v : Fin 3 → K) {x y : Matrix.SpecialLinearGroup (Fin 3) K}
    (hxy : x * y = 1) (hyx : y * x = 1) {c : K}
    (hx : (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v)
    {g : Matrix.SpecialLinearGroup (Fin 3) K} (hg : g ∈ sl3CentreGroup v) :
    x * g * y ∈ sl3CentreGroup v := by
  obtain ⟨φ, hφ, hg⟩ := hg
  have hxy' : (x : Matrix (Fin 3) (Fin 3) K) * y = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hxy, Matrix.SpecialLinearGroup.coe_one]
  have hyx' : (y : Matrix (Fin 3) (Fin 3) K) * x = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hyx, Matrix.SpecialLinearGroup.coe_one]
  have hyv : c • ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
    rw [← mulVec_smul, ← hx, mulVec_mulVec, hyx', one_mulVec]
  refine ⟨c • (φ ᵥ* (y : Matrix (Fin 3) (Fin 3) K)), ?_, ?_⟩
  · rw [smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, ← smul_eq_mul, ← dotProduct_smul,
      hyv, hφ]
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg,
      Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hxy', mul_vecMulVec, vecMulVec_mul, hx,
      smul_vecMulVec, vecMulVec_smul]

end CentreGroup

section Eigen

variable {K : Type*} [Field K]

theorem exists_eigenvector_of_pow_three_eq_one (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (x : Matrix (Fin 3) (Fin 3) K) (hx : x ^ 3 = 1) (W : Submodule K (Fin 3 → K))
    (hW : ∀ w ∈ W, x *ᵥ w ∈ W) {w : Fin 3 → K} (hwW : w ∈ W) (hw : w ≠ 0) :
    ∃ c : K, ∃ u ∈ W, u ≠ 0 ∧ x *ᵥ u = c • u := by
  have hxw : x *ᵥ (x *ᵥ (x *ᵥ w)) = w := by
    rw [mulVec_mulVec, mulVec_mulVec, ← pow_three', hx, one_mulVec]
  have h₁ : x *ᵥ w - ω ^ 2 • w ∈ W := W.sub_mem (hW w hwW) (W.smul_mem _ hwW)
  have h₂ : x *ᵥ (x *ᵥ w - ω ^ 2 • w) - ω • (x *ᵥ w - ω ^ 2 • w) ∈ W :=
    W.sub_mem (hW _ h₁) (W.smul_mem _ h₁)
  have h₃ : x *ᵥ (x *ᵥ (x *ᵥ w - ω ^ 2 • w) - ω • (x *ᵥ w - ω ^ 2 • w)) =
      x *ᵥ (x *ᵥ w - ω ^ 2 • w) - ω • (x *ᵥ w - ω ^ 2 • w) := by
    have key : x *ᵥ (x *ᵥ (x *ᵥ w - ω ^ 2 • w) - ω • (x *ᵥ w - ω ^ 2 • w)) -
        (x *ᵥ (x *ᵥ w - ω ^ 2 • w) - ω • (x *ᵥ w - ω ^ 2 • w)) =
        (ω ^ 2 + ω + 1) • (ω • x *ᵥ w - x *ᵥ (x *ᵥ w) + (1 - ω) • w) := by
      simp only [mulVec_sub, mulVec_smul]
      rw [hxw]
      module
    rw [hω, zero_smul] at key
    exact sub_eq_zero.mp key
  by_cases h₂0 : x *ᵥ (x *ᵥ w - ω ^ 2 • w) - ω • (x *ᵥ w - ω ^ 2 • w) = 0
  · by_cases h₁0 : x *ᵥ w - ω ^ 2 • w = 0
    · exact ⟨ω ^ 2, w, hwW, hw, sub_eq_zero.mp h₁0⟩
    · exact ⟨ω, _, h₁, h₁0, sub_eq_zero.mp h₂0⟩
  · exact ⟨1, _, h₂, h₂0, by rw [h₃, one_smul]⟩

theorem exists_common_eigenvector_of_commuting_cube_one [Finite K] (ω : K)
    (hω : ω ^ 2 + ω + 1 = 0) (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧
      ∀ x ∈ E, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v := by
  let S : Set (Submodule K (Fin 3 → K)) :=
    {W | W ≠ ⊥ ∧ ∀ e ∈ E, ∀ w ∈ W, (e : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W}
  have hS : (⊤ : Submodule K (Fin 3 → K)) ∈ S :=
    ⟨top_ne_bot, fun _ _ _ _ => Submodule.mem_top⟩
  have : Finite (Submodule K (Fin 3 → K)) :=
    Finite.of_injective (fun W : Submodule K (Fin 3 → K) => (W : Set (Fin 3 → K)))
      SetLike.coe_injective
  obtain ⟨W, ⟨hW0, hWE⟩, hWmin⟩ :=
    (wellFounded_lt (α := Submodule K (Fin 3 → K))).has_min S ⟨_, hS⟩
  have hx : ∀ x ∈ E, ∃ c : K, ∀ w ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ w = c • w := by
    intro x hxE
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hx3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hE3 x hxE, Matrix.SpecialLinearGroup.coe_one]
    obtain ⟨c, u, huW, hu0, hxu⟩ :=
      exists_eigenvector_of_pow_three_eq_one ω hω _ hx3 W (hWE x hxE) hwW hw0
    let W' : Submodule K (Fin 3 → K) :=
      { carrier := {w | w ∈ W ∧ (x : Matrix (Fin 3) (Fin 3) K) *ᵥ w = c • w}
        add_mem' := by
          rintro a b ⟨haW, ha⟩ ⟨hbW, hb⟩
          exact ⟨W.add_mem haW hbW, by rw [mulVec_add, ha, hb, smul_add]⟩
        zero_mem' := ⟨W.zero_mem, by simp⟩
        smul_mem' := by
          rintro s a ⟨haW, ha⟩
          exact ⟨W.smul_mem s haW, by rw [mulVec_smul, ha, smul_comm]⟩ }
    have hW'S : W' ∈ S := by
      refine ⟨fun h => hu0 ?_, fun e he w hw => ⟨hWE e he w hw.1, ?_⟩⟩
      · have hu : u ∈ W' := ⟨huW, hxu⟩
        rw [h] at hu
        exact (Submodule.mem_bot K).mp hu
      · have hxe : (x : Matrix (Fin 3) (Fin 3) K) * e = e * x := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
            hcomm x hxE e he]
        rw [mulVec_mulVec, hxe, ← mulVec_mulVec, hw.2, mulVec_smul]
    have hle : W' ≤ W := fun w hw => hw.1
    have hW'W : W' = W := eq_of_le_of_not_lt hle (hWmin W' hW'S)
    exact ⟨c, fun w hw => (hW'W ▸ hw : w ∈ W').2⟩
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  exact ⟨v, hv0, fun x hxE => by
    obtain ⟨c, hc⟩ := hx x hxE
    exact ⟨c, hc v hvW⟩⟩

end Eigen

open scoped MatrixGroups in
theorem exists_pGroup_normalized_of_commuting_cube_one
    {K : Type} [Field K] [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ R : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K),
      IsPGroup r R ∧ R ≠ ⊥ ∧
        E ≤ Subgroup.normalizer (R : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
  obtain ⟨v, hv, hvE⟩ := exists_common_eigenvector_of_commuting_cube_one ω hω E hE3 hcomm
  refine ⟨sl3CentreGroup v, isPGroup_sl3CentreGroup r v, sl3CentreGroup_ne_bot v hv, ?_⟩
  intro x hxE
  rw [Subgroup.mem_normalizer_iff]
  intro h
  obtain ⟨c, hc⟩ := hvE x hxE
  obtain ⟨c', hc'⟩ := hvE x⁻¹ (E.inv_mem hxE)
  constructor
  · intro hh
    exact conj_mem_sl3CentreGroup v (mul_inv_cancel x) (inv_mul_cancel x) hc hh
  · intro hh
    have := conj_mem_sl3CentreGroup v (inv_mul_cancel x) (mul_inv_cancel x) hc' hh
    simpa [mul_assoc] using this

end CFSG.GH74.GLS.Stage2.Bender.Thm1
