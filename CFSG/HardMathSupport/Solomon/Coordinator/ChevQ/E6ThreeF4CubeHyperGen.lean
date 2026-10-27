module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerNC

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

open Matrix

section Eigen

variable {L : Type*} [Field L]

theorem exists_cube_of_det_eq_one {M : Matrix (Fin 3) (Fin 3) L} (hdet : M.det = 1) {ζ : L}
    (hM : M ^ 3 = ζ • 1) : ∃ μ : L, μ ^ 3 = ζ := by
  by_contra h
  have h' : ∀ b : L, b ^ 3 ≠ ζ := fun b hb => h ⟨b, hb⟩
  have h1 := E6Three.det_sub_smul_one_of_pow_three_not_cube h' hM 0
  simp only [zero_smul, sub_zero, hdet] at h1
  exact h' 1 (by linear_combination h1)

theorem exists_conj_diag_of_pow_three_eq_smul {ω : L} (hω : IsPrimitiveRoot ω 3)
    (M : SpecialLinearGroup (Fin 3) L) {ζ : L}
    (hM : (M : Matrix (Fin 3) (Fin 3) L) ^ 3 = ζ • 1) :
    ∃ P : SpecialLinearGroup (Fin 3) L, ∀ i j : Fin 3, i ≠ j →
      ((P * M * P⁻¹ : SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨μ, hμ⟩ := exists_cube_of_det_eq_one M.2 hM
  set γ : GL (Fin 3) L := SpecialLinearGroup.toGL M with hγdef
  have hγM : (γ : Matrix (Fin 3) (Fin 3) L) = M := SpecialLinearGroup.coe_GL_coe_matrix M
  have hγ : (γ : Matrix (Fin 3) (Fin 3) L) ^ 3 = ζ • 1 := by
    rw [hγM]
    exact hM
  have hζ0 : ζ ≠ 0 := E6Three.ne_zero_of_pow_three_eq_smul hγ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hζ0 (by rw [← hμ]; ring)
  set s : GL (Fin 3) L := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) with hs
  set γ' : GL (Fin 3) L := s⁻¹ * γ with hγ'
  have hsγ : Commute s⁻¹ γ :=
    (show Commute s γ from GeneralLinearGroup.scalar_commute _ γ).inv_left
  have hγ'3 : γ' ^ 3 = 1 := by
    rw [hγ', hsγ.mul_pow]
    apply Units.ext
    have e1 : ((s⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = Matrix.scalar (Fin 3) μ⁻¹ := by
      rw [hs, ← map_inv, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val,
        Units.val_mk0]
    have e2 : (ζ • 1 : Matrix (Fin 3) (Fin 3) L) = Matrix.scalar (Fin 3) ζ := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, e1, hγ, e2,
      ← map_pow, ← map_mul, Units.val_one, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow,
      map_one]
  have hcommE : ∀ x ∈ Subgroup.zpowers γ', ∀ y ∈ Subgroup.zpowers γ', x * y = y * x := by
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact (Commute.zpow_zpow_self γ' m n).eq
  have hexpE : ∀ x ∈ Subgroup.zpowers γ', x ^ 3 = 1 := by
    rintro x ⟨m, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, hγ'3, _root_.one_zpow]
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime (p := 3)
    ⟨ω, hω⟩ _ hcommE hexpE
  have hoff := hg γ' (Subgroup.mem_zpowers γ')
  have hγs : γ = s * γ' := by rw [hγ', mul_inv_cancel_left]
  have hsg : Commute s g := GeneralLinearGroup.scalar_commute _ g
  have hX : ∀ i j : Fin 3, i ≠ j →
      ((g * γ * g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
    intro i j hij
    have h1 : g * γ * g⁻¹ = s * (g * γ' * g⁻¹) := by
      rw [hγs, ← mul_assoc g s γ', ← hsg.eq]
      group
    rw [h1, Units.val_mul, hs, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_mul, hoff i j hij, mul_zero]
  set X : GL (Fin 3) L := g * γ * g⁻¹ with hXdef
  have hg0 : (g : Matrix (Fin 3) (Fin 3) L).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact (GeneralLinearGroup.det g).ne_zero
  have hDdet : (Matrix.diagonal ![(((GeneralLinearGroup.det g)⁻¹ : Lˣ) : L), 1, 1]).det ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, hg0]
  set D : GL (Fin 3) L := GeneralLinearGroup.mkOfDetNeZero _ hDdet with hD
  have hDv : (D : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![(((GeneralLinearGroup.det g)⁻¹ : Lˣ) : L), 1, 1] := rfl
  have hDX : D * X = X * D := by
    apply Units.ext
    rw [Units.val_mul D, Units.val_mul X D]
    ext i j
    rw [hDv, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst hij
      ring
    · rw [hX i j hij]
      ring
  have hPdet : ((D * g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hDv, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hg0]
  set P : SpecialLinearGroup (Fin 3) L := ⟨_, hPdet⟩ with hPdef
  have hPGL : SpecialLinearGroup.toGL P = D * g := Units.ext rfl
  have hP : SpecialLinearGroup.toGL (P * M * P⁻¹) = X := by
    rw [map_mul, map_mul, map_inv, hPGL, ← hγdef]
    calc D * g * γ * (D * g)⁻¹ = D * X * D⁻¹ := by
          rw [hXdef]
          group
      _ = X := by
          rw [hDX]
          group
  refine ⟨P, fun i j hij => ?_⟩
  have h2 := congrArg (fun Y : GL (Fin 3) L => (Y : Matrix (Fin 3) (Fin 3) L) i j) hP
  simp only [SpecialLinearGroup.coe_GL_coe_matrix] at h2
  rw [h2]
  exact hX i j hij

end Eigen

section Index

variable {G : Type*} [Group G]

theorem card_le_three_mul_inf_of_mul_pow_mem {E S : Subgroup G} [Finite E] {x : G} (hxE : x ∈ E)
    (hx3 : x ^ 3 = 1) (h : ∀ y ∈ E, ∃ k : ℕ, y * x ^ k ∈ S) :
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ S) := by
  classical
  have h' : ∀ y : E, ∃ k : Fin 3, (y : G) * x ^ (k : ℕ) ∈ S := by
    intro y
    obtain ⟨k, hk⟩ := h y y.2
    refine ⟨⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    have hxk : x ^ k = x ^ (k % 3) := by
      conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hx3, one_pow, one_mul]
    rw [hxk] at hk
    exact hk
  choose kf hkf using h'
  have hmem : ∀ y : E, (y : G) * x ^ (kf y : ℕ) ∈ E ⊓ S := fun y =>
    Subgroup.mem_inf.2 ⟨E.mul_mem y.2 (E.pow_mem hxE _), hkf y⟩
  have hf : Function.Injective
      (fun y : E => (kf y, (⟨(y : G) * x ^ (kf y : ℕ), hmem y⟩ : ↥(E ⊓ S)))) := by
    intro y y' hyy
    have h1 := congrArg Prod.fst hyy
    have h2 := congrArg (fun p : Fin 3 × ↥(E ⊓ S) => (p.2 : G)) hyy
    simp only at h1 h2
    rw [h1] at h2
    exact Subtype.ext (mul_right_cancel h2)
  haveI : Finite ↥(E ⊓ S) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hle := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at hle

end Index

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

end
