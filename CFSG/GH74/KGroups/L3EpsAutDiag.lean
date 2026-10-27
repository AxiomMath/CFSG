module

public import CFSG.GH74.KGroups.L3EpsLin

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Mono

variable {F : Type} [Field F]

theorem exists_perm_of_conj_diag (A : GL (Fin 3) F) (f e : Fin 3 → F) (hf : Function.Injective f)
    (h : (A : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal f = Matrix.diagonal e * (A : Matrix (Fin 3) (Fin 3) F)) :
    ∃ ρ : Equiv.Perm (Fin 3), ∀ i j, (A : Matrix (Fin 3) (Fin 3) F) i j ≠ 0 → i = ρ j := by
  classical
  have hent : ∀ i j, (A : Matrix (Fin 3) (Fin 3) F) i j ≠ 0 → e i = f j := by
    intro i j hij
    have := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    have h2 : f j * (A : Matrix (Fin 3) (Fin 3) F) i j = e i * (A : Matrix (Fin 3) (Fin 3) F) i j := by
      rw [mul_comm]; exact this
    exact (mul_right_cancel₀ hij h2).symm
  have hcol : ∀ j, ∃ i, (A : Matrix (Fin 3) (Fin 3) F) i j ≠ 0 := by
    intro j
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have h1 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := congrFun (congrFun h1 j) j
    rw [Matrix.mul_apply] at h2
    simp [hcon] at h2
  choose ρ₀ hρ₀ using hcol
  have hinj : Function.Injective ρ₀ := by
    intro j j' hjj
    have h1 := hent _ _ (hρ₀ j)
    have h2 := hent _ _ (hρ₀ j')
    rw [hjj] at h1
    exact hf (h1.symm.trans h2)
  let ρ : Equiv.Perm (Fin 3) := Equiv.ofBijective ρ₀ (Finite.injective_iff_bijective.1 hinj)
  refine ⟨ρ, fun i j hij => ?_⟩
  by_contra hne
  obtain ⟨j'', hj''⟩ := (Equiv.ofBijective ρ₀ (Finite.injective_iff_bijective.1 hinj)).surjective i
  have hj''' : ρ₀ j'' = i := hj''
  have h1 := hent _ _ hij
  have h2 := hent _ _ (hρ₀ j'')
  rw [hj'''] at h2
  have : j = j'' := hf (h1.symm.trans h2)
  subst this
  exact hne (hj'''.symm)

theorem conj_diag_of_perm (A : GL (Fin 3) F) (ρ : Equiv.Perm (Fin 3))
    (hρ : ∀ i j, (A : Matrix (Fin 3) (Fin 3) F) i j ≠ 0 → i = ρ j) (φ : Fin 3 → F) :
    (A : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal φ * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun i => φ (ρ.symm i)) := by
  have h : (A : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal φ =
      Matrix.diagonal (fun i => φ (ρ.symm i)) * (A : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : (A : Matrix (Fin 3) (Fin 3) F) i j = 0
    · simp [hij]
    · have := hρ i j hij
      subst this
      simp [mul_comm]
  rw [h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

end Mono

section Theta

variable {F : Type} [Field F]

@[expose] noncomputable def entryMap (σ : F ≃+* F) (ε : ℕ) (x : F) : F :=
  if ε = 0 then σ x else (σ x)⁻¹

theorem entryMap_mul (σ : F ≃+* F) (ε : ℕ) (x y : F) :
    entryMap σ ε (x * y) = entryMap σ ε x * entryMap σ ε y := by
  unfold entryMap
  split_ifs
  · exact map_mul σ x y
  · rw [map_mul, mul_inv]

theorem entryMap_one (σ : F ≃+* F) (ε : ℕ) : entryMap σ ε 1 = 1 := by
  unfold entryMap
  split_ifs <;> simp

theorem entryMap_ne_zero (σ : F ≃+* F) (ε : ℕ) {x : F} (hx : x ≠ 0) : entryMap σ ε x ≠ 0 := by
  unfold entryMap
  split_ifs
  · simpa using hx
  · simpa using hx

theorem entryMap_injective (σ : F ≃+* F) (ε : ℕ) : Function.Injective (entryMap σ ε) := by
  intro x y h
  unfold entryMap at h
  split_ifs at h
  · exact σ.injective h
  · exact σ.injective (inv_injective h)

theorem diagSL_inv' (a b c : F) (h : a * b * c = 1) :
    (diagSL a b c h)⁻¹ = diagSL a⁻¹ b⁻¹ c⁻¹ (by
      calc a⁻¹ * b⁻¹ * c⁻¹ = (a * b * c)⁻¹ := by field_simp
        _ = 1 := by rw [h, inv_one]) := by
  have ha : a ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (h ▸ one_ne_zero))
  have hb : b ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (h ▸ one_ne_zero))
  have hc : c ≠ 0 := right_ne_zero_of_mul (h ▸ one_ne_zero)
  apply inv_eq_of_mul_eq_one_right
  rw [diagSL_mul, ← diagSL_one (K := F) (by ring)]
  exact diagSL_congr (mul_inv_cancel₀ ha) (mul_inv_cancel₀ hb) (mul_inv_cancel₀ hc)

theorem coe_theta_diagSL (A : GL (Fin 3) F) (σ : F ≃+* F) {ε : ℕ} (hε : ε ≤ 1) (a b c : F)
    (h : a * b * c = 1) :
    ((theta A σ ε (diagSL a b c h) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) *
        Matrix.diagonal ![entryMap σ ε a, entryMap σ ε b, entryMap σ ε c] *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have hε' : ε = 0 ∨ ε = 1 := by omega
  rcases hε' with rfl | rfl
  · rw [coe_theta_zero, coe_diagSL, Matrix.diagonal_map (map_zero σ)]
    have e : (fun m => σ (![a, b, c] m)) = ![entryMap σ 0 a, entryMap σ 0 b, entryMap σ 0 c] := by
      ext i
      fin_cases i <;> simp [entryMap]
    rw [e]
  · rw [coe_theta_one, diagSL_inv', coe_diagSL, Matrix.diagonal_transpose,
      Matrix.diagonal_map (map_zero σ)]
    have e : (fun m => σ (![a⁻¹, b⁻¹, c⁻¹] m)) =
        ![entryMap σ 1 a, entryMap σ 1 b, entryMap σ 1 c] := by
      ext i
      fin_cases i <;> simp [entryMap]
    rw [e]

end Theta

section Action

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem prod_perm_eq {a b c : F} (π : Equiv.Perm (Fin 3)) :
    (![a, b, c] (π 0)) * (![a, b, c] (π 1)) * (![a, b, c] (π 2)) = a * b * c := by
  have h := Equiv.prod_comp π ![a, b, c]
  simpa [Fin.prod_univ_three, mul_assoc] using h

theorem aut_diag_action (α : MulAut (projectiveSL 3 F)) (t₀ t₁ t₂ : F) (ht : t₀ * t₁ * t₂ = 1)
    (hinj : Function.Injective ![t₀, t₁, t₂])
    (hα : ∃ (x y z : F) (hxyz : x * y * z = 1),
      α (proj 3 F (diagSL t₀ t₁ t₂ ht)) = proj 3 F (diagSL x y z hxyz)) :
    ∃ (σ : F ≃+* F) (ε : ℕ) (π : Equiv.Perm (Fin 3)), ε ≤ 1 ∧
      ∀ (a b c : F) (h : a * b * c = 1),
        ∃ h' : entryMap σ ε (![a, b, c] (π 0)) * entryMap σ ε (![a, b, c] (π 1)) *
            entryMap σ ε (![a, b, c] (π 2)) = 1,
          α (proj 3 F (diagSL a b c h)) = proj 3 F (diagSL (entryMap σ ε (![a, b, c] (π 0)))
            (entryMap σ ε (![a, b, c] (π 1))) (entryMap σ ε (![a, b, c] (π 2))) h') := by
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 α
  have hαtheta : ∀ g : SL(3, F), α (proj 3 F g) = proj 3 F (theta A σ ε g) := by
    intro g
    rw [hαeq, ← descendAut_theta, descendAut_proj]
  obtain ⟨x, y, z, hxyz, hxyz'⟩ := hα
  rw [hαtheta] at hxyz'
  obtain ⟨c, hc3, hc⟩ := proj_eq_proj_iff.1 hxyz'
  set Θt := theta A σ ε (diagSL t₀ t₁ t₂ ht) with hΘt
  set D := diagSL x y z hxyz with hD
  have hD' : (D : Matrix (Fin 3) (Fin 3) F) =
      (Θt : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F) := by
    have h1 : (Θt : Matrix (Fin 3) (Fin 3) F) * ((Θt⁻¹ * D : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = D := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [← h1, hc]
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hM : (Θt : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun i => ![x, y, z] i * ((c⁻¹ : Fˣ) : F)) := by
    ext i j
    have h2 := congrFun (congrFun hD' i) j
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, hD, coe_diagSL, Matrix.diagonal_apply] at h2
    rw [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte] at h2 ⊢
      rw [Units.val_inv_eq_inv_val]
      field_simp
      exact h2.symm
    · simp only [hij, ↓reduceIte] at h2 ⊢
      exact (mul_eq_zero.1 h2.symm).resolve_right hc0
  set f : Fin 3 → F := ![entryMap σ ε t₀, entryMap σ ε t₁, entryMap σ ε t₂] with hf
  set e : Fin 3 → F := fun i => ![x, y, z] i * ((c⁻¹ : Fˣ) : F) with he
  have hconj : (A : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal f *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal e := by
    rw [← hM, hΘt, coe_theta_diagSL A σ hε]
  have hmul : (A : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal f =
      Matrix.diagonal e * (A : Matrix (Fin 3) (Fin 3) F) := by
    rw [← hconj, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  have hfinj : Function.Injective f := by
    have : f = entryMap σ ε ∘ ![t₀, t₁, t₂] := by
      ext k
      fin_cases k <;> rfl
    rw [this]
    exact (entryMap_injective σ ε).comp hinj
  obtain ⟨ρ, hρ⟩ := exists_perm_of_conj_diag A f e hfinj hmul
  refine ⟨σ, ε, ρ.symm, hε, fun a b c' h => ?_⟩
  have hprod : entryMap σ ε (![a, b, c'] (ρ.symm 0)) * entryMap σ ε (![a, b, c'] (ρ.symm 1)) *
      entryMap σ ε (![a, b, c'] (ρ.symm 2)) = 1 := by
    rw [← entryMap_mul, ← entryMap_mul, prod_perm_eq, h, entryMap_one]
  refine ⟨hprod, ?_⟩
  rw [hαtheta]
  congr 1
  apply Subtype.ext
  rw [coe_theta_diagSL A σ hε a b c' h, conj_diag_of_perm A ρ hρ, coe_diagSL]
  congr 1
  have hh : ∀ j : Fin 3, ![entryMap σ ε a, entryMap σ ε b, entryMap σ ε c'] j =
      entryMap σ ε (![a, b, c'] j) := by
    intro j
    fin_cases j <;> rfl
  ext k
  fin_cases k
  · exact hh (ρ.symm 0)
  · exact hh (ρ.symm 1)
  · exact hh (ρ.symm 2)

end Action

end CFSG.GH74.KGroups.L3Eps
