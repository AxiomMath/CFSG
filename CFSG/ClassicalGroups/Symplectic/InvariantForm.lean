module

public import CFSG.ClassicalGroups.Symplectic.InvariantPairing
import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open CFSG.ClassicalGroups.Alternating
open Matrix
open LinearMap (BilinForm)

variable {m : ℕ} {K : Type} [Field K]

private theorem statedSp_symm_app (g : Gsp (spForm m K)) (v : Fin m ⊕ Fin m → K) :
    g.app v = (((spEquiv (m := m) (K := K)).symm g : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v := by
  have := spEquiv_app ((spEquiv (m := m) (K := K)).symm g) v
  rw [MulEquiv.apply_symm_apply] at this
  exact this

private theorem statedSp_pair_aux {u u' v v' : Fin m ⊕ Fin m → K}
    (h : spForm m K u u' = 1) (h' : spForm m K v v' = 1) :
    ∃ A ∈ StatedSp m K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = v ∧
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u' = v' := by
  obtain ⟨g, hg, hg'⟩ := exists_gsp_pair spForm_isAlt spForm_nondegenerate h h'
  refine ⟨((spEquiv (m := m) (K := K)).symm g : GL (Fin m ⊕ Fin m) K),
    ((spEquiv (m := m) (K := K)).symm g).2, ?_, ?_⟩
  · rw [← statedSp_symm_app]; exact hg
  · rw [← statedSp_symm_app]; exact hg'

theorem exists_eq_smul_spForm_of_invariant (hm : 1 ≤ m)
    (β : BilinForm K (Fin m ⊕ Fin m → K))
    (hβ : ∀ A ∈ StatedSp m K, ∀ x y : Fin m ⊕ Fin m → K,
      β ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = β x y) :
    ∃ c : K, ∀ x y, β x y = c * spForm m K x y := by
  classical
  let f : (Fin m ⊕ Fin m → K) →+ (Fin m ⊕ Fin m → K) →+ K :=
    { toFun := fun x => (β x).toAddMonoidHom
      map_zero' := by ext y; simp
      map_add' := fun x x' => by ext y; simp }
  have hz : ∀ x y, spForm m K x y = 0 → β x y = 0 := fun x y hxy =>
    biadd_eq_zero_of_spForm_eq_zero f (fun g hg a b => hβ g hg a b) hxy
  let i0 : Fin m := ⟨0, hm⟩
  let x₀ : Fin m ⊕ Fin m → K := Pi.single (Sum.inl i0) 1
  let y₀ : Fin m ⊕ Fin m → K := Pi.single (Sum.inr i0) 1
  have h0 : spForm m K x₀ y₀ = 1 := by rw [spForm_single_inl_inr]; simp
  refine ⟨β x₀ y₀, fun x y => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨y₂, hy₂⟩ : ∃ y₂, spForm m K x y₂ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (spForm_nondegenerate.1 x hcon)
  have hy₁ : spForm m K x ((spForm m K x y₂)⁻¹ • y₂) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy₂]
  obtain ⟨A, hA, hAx, hAy⟩ := statedSp_pair_aux h0 hy₁
  have hβ1 : β x ((spForm m K x y₂)⁻¹ • y₂) = β x₀ y₀ := by
    have := hβ A hA x₀ y₀
    rw [hAx, hAy] at this
    exact this
  have hres : β x (y - spForm m K x y • ((spForm m K x y₂)⁻¹ • y₂)) = 0 := by
    apply hz
    rw [map_sub, map_smul, hy₁, smul_eq_mul, mul_one, sub_self]
  rw [map_sub, map_smul, hβ1, sub_eq_zero, smul_eq_mul] at hres
  rw [hres, mul_comm]

theorem exists_eq_smul_of_commute_statedSp (hm : 1 ≤ m)
    (f : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (hf : ∀ A ∈ StatedSp m K, ∀ x : Fin m ⊕ Fin m → K,
      f ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ f x) :
    ∃ c : K, ∀ x, f x = c • x := by
  let β : BilinForm K (Fin m ⊕ Fin m → K) := (spForm m K).compl₁₂ f LinearMap.id
  have hβ : ∀ A ∈ StatedSp m K, ∀ x y : Fin m ⊕ Fin m → K,
      β ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = β x y := by
    intro A hA x y
    show spForm m K (f _) _ = spForm m K (f x) y
    rw [hf A hA x]
    exact (mem_statedSp_iff_forall A).mp hA (f x) y
  obtain ⟨c, hc⟩ := exists_eq_smul_spForm_of_invariant hm β hβ
  refine ⟨c, fun x => ?_⟩
  have hrad : ∀ y, spForm m K (f x - c • x) y = 0 := fun y => by
    have h1 : spForm m K (f x) y = c * spForm m K x y := hc x y
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, h1, sub_self]
  exact sub_eq_zero.mp (spForm_nondegenerate.1 _ hrad)

theorem eq_bot_or_eq_top_of_invariant_statedSp (W : Submodule K (Fin m ⊕ Fin m → K))
    (hW : ∀ A ∈ StatedSp m K, ∀ w ∈ W,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine eq_top_iff.mpr fun v _ => ?_
  by_cases hv : v = 0
  · rw [hv]; exact W.zero_mem
  obtain ⟨A, hA, hAw⟩ := exists_statedSp_mulVec_eq hw0 hv
  rw [← hAw]
  exact hW A hA w hwW

theorem exists_smul_statedSp_of_normalizes [Finite K] [CharP K 2] (hm : 1 ≤ m)
    {γ : GL (Fin m ⊕ Fin m) K} (hγ : ∀ A ∈ StatedSp m K, γ * A * γ⁻¹ ∈ StatedSp m K) :
    ∃ (μ : K) (s : GL (Fin m ⊕ Fin m) K), μ ≠ 0 ∧ s ∈ StatedSp m K ∧
      ∀ x : Fin m ⊕ Fin m → K,
        (γ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
          μ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
  classical
  set G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    ((γ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hG
  let Gl : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K) := Matrix.mulVecLin G
  let β : BilinForm K (Fin m ⊕ Fin m → K) := (spForm m K).compl₁₂ Gl Gl
  have hβ : ∀ A ∈ StatedSp m K, ∀ x y : Fin m ⊕ Fin m → K,
      β ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = β x y := by
    intro A hA x y
    have hA' := hγ A hA
    have hcomm : (γ * A * γ⁻¹) * γ = γ * A := inv_mul_cancel_right _ _
    have hmat : G * (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        ((γ * A * γ⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * G := by
      have := congrArg (fun u : GL (Fin m ⊕ Fin m) K =>
        (u : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) hcomm
      simp only [Units.val_mul] at this
      rw [hG]
      exact this.symm
    show spForm m K (G *ᵥ (_ *ᵥ x)) (G *ᵥ (_ *ᵥ y)) = spForm m K (G *ᵥ x) (G *ᵥ y)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    exact (mem_statedSp_iff_forall _).mp hA' _ _
  obtain ⟨c, hc⟩ := exists_eq_smul_spForm_of_invariant hm β hβ
  have hc0 : c ≠ 0 := by
    intro h0
    have hall : ∀ x, G *ᵥ x = 0 := by
      intro x
      apply spForm_nondegenerate.1
      intro z
      have h1 : spForm m K (G *ᵥ x) z =
          spForm m K (G *ᵥ x) (G *ᵥ (((γ⁻¹ : GL (Fin m ⊕ Fin m) K) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ z)) := by
        rw [Matrix.mulVec_mulVec, hG, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [h1]
      have := hc x (((γ⁻¹ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ z)
      rw [h0, zero_mul] at this
      exact this
    let i0 : Fin m := ⟨0, hm⟩
    have hx0 : (Pi.single (Sum.inl i0) 1 : Fin m ⊕ Fin m → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl i0)
      simp at this
    apply hx0
    have h2 := hall (Pi.single (Sum.inl i0) 1)
    have h3 : (Pi.single (Sum.inl i0) 1 : Fin m ⊕ Fin m → K) =
        (((γ⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) *ᵥ
          (G *ᵥ (Pi.single (Sum.inl i0) 1)) := by
      rw [Matrix.mulVec_mulVec, hG, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h3, h2, Matrix.mulVec_zero]
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [hμ]; ring)
  let s : GL (Fin m ⊕ Fin m) K :=
    (Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) (Units.mk0 μ⁻¹ (inv_ne_zero hμ0))) * γ
  have hs : ∀ x, (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = μ⁻¹ • (G *ᵥ x) := by
    intro x
    show (Matrix.scalar (Fin m ⊕ Fin m) μ⁻¹ * G) *ᵥ x = _
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_mulVec]
  refine ⟨μ, s, hμ0, ?_, fun x => ?_⟩
  · rw [mem_statedSp_iff_forall]
    intro x y
    rw [hs, hs]
    simp only [LinearMap.map_smul₂, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h1 : spForm m K (G *ᵥ x) (G *ᵥ y) = c * spForm m K x y := hc x y
    rw [h1, hμ]
    field_simp
  · rw [hs, smul_smul, mul_inv_cancel₀ hμ0, one_smul]

end CFSG.ClassicalGroups.Symplectic
