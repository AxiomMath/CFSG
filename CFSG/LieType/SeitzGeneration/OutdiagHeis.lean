module

public import CFSG.LieType.SeitzGeneration.OutdiagAbelian
public import CFSG.LieType.SeitzGeneration.OutdiagHeisNormal

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

section Core

variable {F : Type*} [Field F]

@[expose] def heisD (ω : F) : Matrix (Fin 3) (Fin 3) F := diagonal ![1, ω, ω ^ 2]

@[expose] def heisC (α : F) : Matrix (Fin 3) (Fin 3) F := !![0, 0, α; 1, 0, 0; 0, 1, 0]

@[expose] def outerHeisSet (ω α : F) : Set (SpecialLinearGroup (Fin 3) F) :=
  FixSL (heisC α) ∪ FixSL (heisD ω) ∪ FixSL (heisC α * heisD ω) ∪
    FixSL (heisC α * heisD ω ^ 2)

end Core

@[expose] def OuterHeisCore : Prop :=
  ∀ (F : Type) [Field F] [Finite F], 3 ∣ Nat.card F - 1 → 4 < Nat.card F → ∀ ω α : F,
    ω ^ 2 + ω + 1 = 0 → ω ≠ 1 → α ≠ 0 → (¬ ∃ μ : F, μ ^ 3 = α) →
      Subgroup.closure (outerHeisSet ω α) = ⊤

section Heis

variable {F : Type} [Field F]

theorem eq_top_of_comap_conjUnit {K : Subgroup (SpecialLinearGroup (Fin 3) F)} (P : GL (Fin 3) F)
    (h : K.comap (conjUnit P) = ⊤) : K = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [← conjUnit_conjUnit_inv P g]
  exact Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top (conjUnit P⁻¹ g))

theorem intertwine_mul_right {n : ℕ} {P M₁ M₂ N₁ N₂ : Matrix (Fin n) (Fin n) F}
    (h₁ : M₁ * P = P * N₁) (h₂ : M₂ * P = P * N₂) : (M₁ * M₂) * P = P * (N₁ * N₂) := by
  rw [Matrix.mul_assoc, h₂, ← Matrix.mul_assoc, h₁, Matrix.mul_assoc]

theorem intertwine_pow_right {n : ℕ} {P M N : Matrix (Fin n) (Fin n) F} (h : M * P = P * N)
    (k : ℕ) : M ^ k * P = P * N ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, intertwine_mul_right ih h, pow_succ]

variable [Finite F]

theorem closure_planeFix_heis_normal (hcore : OuterHeisCore) (hF3 : 3 ∣ Nat.card F - 1)
    (h4 : 4 < Nat.card F) {x y : GL (Fin 3) F} {ω α : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (hα : α ≠ 0)
    (hyx : (y : Matrix (Fin 3) (Fin 3) F) * x = ω • ((x : Matrix (Fin 3) (Fin 3) F) * y))
    (hy3 : (y : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1)
    (hx3 : (x : Matrix (Fin 3) (Fin 3) F) ^ 3 = α • 1) :
    Subgroup.closure (planeFix x y) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hprim : IsPrimitiveRoot ω 3 := by
    have h1 := orderOf_eq_prime hω3 hω1
    rw [← h1]
    exact IsPrimitiveRoot.orderOf ω
  by_cases hcube : ∃ μ : F, μ ^ 3 = α
  · obtain ⟨μ, hμ⟩ := hcube
    have hμ0 : μ ≠ 0 := by rintro rfl; exact hα (by rw [← hμ]; norm_num)
    obtain ⟨u, hu⟩ : ∃ u : Fˣ, (u : F) = μ⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμ0), rfl⟩
    have hu0 : (u : F) ≠ 0 := u.ne_zero
    obtain ⟨x₁, hx₁⟩ : ∃ g : GL (Fin 3) F,
        g = Matrix.GeneralLinearGroup.scalar (Fin 3) u * x := ⟨_, rfl⟩
    have hx₁c : (x₁ : Matrix (Fin 3) (Fin 3) F) = (u : F) • (x : Matrix (Fin 3) (Fin 3) F) := by
      rw [hx₁, coe_scalarGL_mul]
    have hyx₁ : (y : Matrix (Fin 3) (Fin 3) F) * x₁ =
        ω • ((x₁ : Matrix (Fin 3) (Fin 3) F) * y) := by
      rw [hx₁c, Matrix.mul_smul, hyx, Matrix.smul_mul, smul_comm]
    have hx₁3 : (x₁ : Matrix (Fin 3) (Fin 3) F) ^ 3 = (1 : F) • 1 := by
      rw [hx₁c, smul_pow, hx3, smul_smul, hu, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow]
    obtain ⟨P, ξ, hξ3, hyP, hx₁P⟩ := exists_heisenberg_basis_gl hprim hyx₁ hy3 hx₁3
    set K := Subgroup.closure (planeFix x y) with hK
    have hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K.comap (conjUnit P) := by
      intro a b d h
      rw [Subgroup.mem_comap]
      have hcomm : (diagonal ![ξ, ξ * ω, ξ * ω ^ 2] : Matrix (Fin 3) (Fin 3) F) *
          (diagSL a b d h : Matrix (Fin 3) (Fin 3) F) =
          (diagSL a b d h : Matrix (Fin 3) (Fin 3) F) * diagonal ![ξ, ξ * ω, ξ * ω ^ 2] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [diagSL, mul_comm]
      exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inr
        (mem_FixSL_conj hyP (mem_FixSL_of_mul_comm hcomm)))))
    have hcirc : ∀ (a b d : F) (h : a ^ 3 + b ^ 3 + d ^ 3 - 3 * a * b * d = 1),
        circSL a b d h ∈ K.comap (conjUnit P) := by
      intro a b d h
      rw [Subgroup.mem_comap]
      have hcomm : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) *
          (circSL a b d h : Matrix (Fin 3) (Fin 3) F) =
          (circSL a b d h : Matrix (Fin 3) (Fin 3) F) * !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
        have := congrArg Subtype.val (circSL_mul_shiftSL a b d h)
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
        exact this.symm
      have h2 := mem_FixSL_conj hx₁P (mem_FixSL_of_mul_comm hcomm)
      rw [hx₁c, mem_FixSL_smul hu0] at h2
      exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl h2)))
    exact eq_top_of_comap_conjUnit P (eq_top_of_torus_circ hdiag hcirc hω hω1 h4)
  · obtain ⟨P, ξ, hξ3, hyP, hxP⟩ := exists_heisenberg_basis_gl hprim hyx hy3 hx3
    have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
    set K := Subgroup.closure (planeFix x y) with hK
    have hDξ : (diagonal ![ξ, ξ * ω, ξ * ω ^ 2] : Matrix (Fin 3) (Fin 3) F) = ξ • heisD ω := by
      ext i j
      by_cases hij : i = j
      · subst hij; fin_cases i <;> simp [heisD, mul_comm]
      · simp [heisD, hij]
    have hle : outerHeisSet ω α ⊆ K.comap (conjUnit P) := by
      intro k hk
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine Subgroup.subset_closure ?_
      rcases hk with ((hk | hk) | hk) | hk
      · exact Or.inl (Or.inl (Or.inl (mem_FixSL_conj hxP hk)))
      · refine Or.inl (Or.inl (Or.inr ?_))
        refine mem_FixSL_conj hyP ?_
        rw [hDξ, mem_FixSL_smul hξ0]; exact hk
      · refine Or.inl (Or.inr ?_)
        have h1 : ((x * y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            (P : Matrix (Fin 3) (Fin 3) F) = P * (heisC α * (ξ • heisD ω)) := by
          rw [Units.val_mul, ← hDξ]; exact intertwine_mul_right hxP hyP
        refine mem_FixSL_conj h1 ?_
        rw [Matrix.mul_smul, mem_FixSL_smul hξ0]; exact hk
      · refine Or.inr ?_
        have h1 : ((x * y ^ 2 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            (P : Matrix (Fin 3) (Fin 3) F) = P * (heisC α * (ξ • heisD ω) ^ 2) := by
          rw [Units.val_mul, Units.val_pow_eq_pow_val, ← hDξ]
          exact intertwine_mul_right hxP (intertwine_pow_right hyP 2)
        refine mem_FixSL_conj h1 ?_
        rw [smul_pow, Matrix.mul_smul, mem_FixSL_smul (pow_ne_zero 2 hξ0)]; exact hk
    have htop := hcore F hF3 h4 ω α hω hω1 hα hcube
    have : K.comap (conjUnit P) = ⊤ := by
      rw [eq_top_iff, ← htop, Subgroup.closure_le]
      exact hle
    exact eq_top_of_comap_conjUnit P this

end Heis

end CFSG.LieType.SeitzGeneration
