module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Lang.TwE6Step3
open scoped MatrixGroups

section Diag

variable {ν : ℕ} {L : Type} [Field L]

@[expose] def diagSL (ν : ℕ) (L : Type) [Field L] : Subgroup SL(ν, L) where
  carrier := {X | ∀ i j, i ≠ j → (X : Matrix (Fin ν) (Fin ν) L) i j = 0}
  mul_mem' := by
    intro X Y hX hY i j hij
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i = k
    · subst hik
      rw [hY _ _ hij, mul_zero]
    · rw [hX _ _ hik, zero_mul]
  one_mem' := by
    intro i j hij
    simp [Matrix.one_apply, hij]
  inv_mem' := by
    intro X hX i j hij
    have hd : (X : Matrix (Fin ν) (Fin ν) L) =
        Matrix.diagonal (fun i => (X : Matrix (Fin ν) (Fin ν) L) i i) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
      · simp [Matrix.diagonal_apply_ne _ hab, hX a b hab]
    rw [Matrix.SpecialLinearGroup.coe_inv, hd, Matrix.adjugate_diagonal]
    simp [Matrix.diagonal_apply_ne _ hij]

theorem mem_diagSL {X : SL(ν, L)} :
    X ∈ diagSL ν L ↔ ∀ i j, i ≠ j → (X : Matrix (Fin ν) (Fin ν) L) i j = 0 := Iff.rfl

@[expose] def diagSLOf (x : Fin ν → Lˣ) (hx : ∏ i, x i = 1) : SL(ν, L) :=
  ⟨Matrix.diagonal (fun i => (x i : L)), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, hx, Units.val_one]⟩

theorem coe_diagSLOf (x : Fin ν → Lˣ) (hx : ∏ i, x i = 1) :
    ((diagSLOf x hx : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      Matrix.diagonal (fun i => (x i : L)) :=
  rfl

theorem diagSLOf_mem (x : Fin ν → Lˣ) (hx : ∏ i, x i = 1) : diagSLOf x hx ∈ diagSL ν L := by
  intro i j hij
  simp [coe_diagSLOf, Matrix.diagonal_apply_ne _ hij]

theorem exists_units_of_mem_diagSL {X : SL(ν, L)} (hX : X ∈ diagSL ν L) :
    ∃ (x : Fin ν → Lˣ) (hx : ∏ i, x i = 1), X = diagSLOf x hx := by
  have hd : (X : Matrix (Fin ν) (Fin ν) L) =
      Matrix.diagonal (fun i => (X : Matrix (Fin ν) (Fin ν) L) i i) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.diagonal_apply_ne _ hab, hX a b hab]
  have hdet : ∏ i, (X : Matrix (Fin ν) (Fin ν) L) i i = 1 := by
    have h := X.2
    rwa [hd, Matrix.det_diagonal] at h
  have hne : ∀ i, (X : Matrix (Fin ν) (Fin ν) L) i i ≠ 0 := fun i h0 => by
    have : ∏ j, (X : Matrix (Fin ν) (Fin ν) L) j j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdet] at this
    exact one_ne_zero this
  refine ⟨fun i => Units.mk0 _ (hne i), Units.ext ?_, Subtype.ext ?_⟩
  · rw [Units.coe_prod]
    simpa using hdet
  · simpa [coe_diagSLOf] using hd

@[expose] def PermDiag (B : SL(ν, L)) (ρ : Equiv.Perm (Fin ν)) : Prop :=
  ∀ v : Fin ν → L, (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * Matrix.diagonal v *
    (B : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal (fun k => v (ρ k))

@[expose] def conjUni (B : SL(ν, L)) (σ : L →+* L) : SL(ν, L) →* SL(ν, L) :=
  (MulAut.conj B⁻¹).toMonoidHom.comp (stdUnitary σ)

theorem conjUni_apply (B : SL(ν, L)) (σ : L →+* L) (X : SL(ν, L)) :
    conjUni B σ X = B⁻¹ * stdUnitary σ X * B := by
  simp [conjUni, MulAut.conj_apply]

theorem coe_conjUni_diagSLOf {B : SL(ν, L)} {ρ : Equiv.Perm (Fin ν)} (hB : PermDiag B ρ)
    (σ : L →+* L) (x : Fin ν → Lˣ) (hx : ∏ i, x i = 1) :
    ((conjUni B σ (diagSLOf x hx) : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      Matrix.diagonal (fun k => ((σ (x (ρ k)) : L))⁻¹) := by
  rw [conjUni_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_stdUnitary, coe_diagSLOf]
  have h1 : ((Matrix.diagonal (fun i => (x i : L))).map σ) =
      Matrix.diagonal (fun i => σ (x i : L)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.diagonal_apply_ne _ hab]
  have h3 : (Matrix.diagonal (fun i => σ (x i : L)))⁻¹ =
      Matrix.diagonal (fun i => (σ (x i : L))⁻¹) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => (σ (x i : L))⁻¹ * σ (x i : L)) = fun _ => 1 := by
      funext i
      exact inv_mul_cancel₀ ((map_ne_zero σ).2 (Units.ne_zero (x i)))
    rw [this]
    exact Matrix.diagonal_one
  rw [h1, h3, Matrix.diagonal_transpose]
  exact hB _

theorem lang_diagSL [IsAlgClosed L] [NeZero ν] {Q : ℕ} (hQ : 2 ≤ Q) (σ : L →+* L)
    (hσ : ∀ c, σ c = c ^ Q) {B : SL(ν, L)} {ρ : Equiv.Perm (Fin ν)} (hB : PermDiag B ρ) :
    ∀ δ ∈ diagSL ν L, ∃ δ' ∈ diagSL ν L, conjUni B σ δ' * δ'⁻¹ = δ := by
  intro δ hδ
  obtain ⟨w, hw, rfl⟩ := exists_units_of_mem_diagSL hδ
  haveI : Nonempty (Fin ν) := ⟨0⟩
  have hw' : ∏ i, (w i)⁻¹ = 1 := by
    rw [Finset.prod_inv_distrib, hw, inv_one]
  obtain ⟨x, hx, hxw⟩ := exists_lang_monomial ρ (e := (Q : ℤ)) (by simpa using hQ)
    (fun i => (w i)⁻¹) hw'
  refine ⟨diagSLOf x hx, diagSLOf_mem x hx, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [coe_conjUni_diagSLOf hB σ x hx, Matrix.SpecialLinearGroup.coe_mul, coe_diagSLOf,
    coe_diagSLOf, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  have h1 := hxw k
  have h2 : (x k : L) * (x (ρ k) : L) ^ Q = ((w k : L))⁻¹ := by
    have := congrArg (fun u : Lˣ => (u : L)) h1
    simpa [zpow_natCast] using this
  rw [hσ]
  have hxk : (x k : L) ≠ 0 := Units.ne_zero _
  have hxρ : (x (ρ k) : L) ≠ 0 := Units.ne_zero _
  have hwk : (w k : L) ≠ 0 := Units.ne_zero _
  have hxρQ : (x (ρ k) : L) ^ Q ≠ 0 := pow_ne_zero _ hxρ
  field_simp at h2 ⊢
  linear_combination (-1 : L) * h2

theorem permGL_inv_mul_diagonal_mul (π : Equiv.Perm (Fin ν)) (u : Fin ν → L) :
    (↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Matrix.diagonal u *
      ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
        Matrix.diagonal (fun k => u (π k)) := by
  rw [← map_inv, MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply,
    Matrix.permMatrixHom_apply, inv_inv, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  change (Matrix.diagonal u).submatrix (⇑π ∘ id) (id ∘ ⇑(π⁻¹).symm) = _
  have : (π⁻¹).symm = π := by
    rw [Equiv.Perm.inv_def, Equiv.symm_symm]
  rw [this, Function.comp_id, Function.id_comp]
  exact Matrix.submatrix_diagonal_equiv u π

theorem permDiag_pin {B : SL(ν, L)} (d : Fin ν → Lˣ) (π : Equiv.Perm (Fin ν))
    (hB : ∀ Y : Matrix (Fin ν) (Fin ν) L, (B : Matrix (Fin ν) (Fin ν) L) * Y *
      (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) = ((diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ :
        GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) * Y *
          (↑(diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹)⁻¹ : Matrix (Fin ν) (Fin ν) L)) :
    PermDiag B π⁻¹ := by
  intro v
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hM
  have hMM : (M : Matrix (Fin ν) (Fin ν) L) * (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = 1 := M.mul_inv
  have hMM' : (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * (M : Matrix (Fin ν) (Fin ν) L) = 1 := M.inv_mul
  have hBB : (B : Matrix (Fin ν) (Fin ν) L) * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hBB' : (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * (B : Matrix (Fin ν) (Fin ν) L) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hZ : ∀ Z : Matrix (Fin ν) (Fin ν) L, (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * Z *
      (B : Matrix (Fin ν) (Fin ν) L) =
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * Z * (M : Matrix _ _ L) := by
    intro Z
    have h1 := hB ((↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * Z * (M : Matrix _ _ L))
    have h2 : (M : Matrix (Fin ν) (Fin ν) L) * ((↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * Z *
        (M : Matrix _ _ L)) * (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = Z := by
      calc (M : Matrix (Fin ν) (Fin ν) L) * ((↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * Z *
          (M : Matrix _ _ L)) * (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) =
          ((M : Matrix (Fin ν) (Fin ν) L) * (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L)) * Z *
            ((M : Matrix _ _ L) * (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L)) := by
            simp only [Matrix.mul_assoc]
        _ = Z := by rw [hMM, Matrix.one_mul, Matrix.mul_one]
    rw [h2] at h1
    calc (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * Z * (B : Matrix (Fin ν) (Fin ν) L) =
        (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * ((B : Matrix (Fin ν) (Fin ν) L) *
          ((↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * Z * (M : Matrix _ _ L)) *
            (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L)) * (B : Matrix (Fin ν) (Fin ν) L) := by rw [h1]
      _ = ((↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * (B : Matrix (Fin ν) (Fin ν) L)) *
          ((↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * Z * (M : Matrix _ _ L)) *
            ((↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * (B : Matrix (Fin ν) (Fin ν) L)) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
  rw [hZ]
  have hMinv : (M⁻¹ : GL (Fin ν) L) = (permGL π : GL (Fin ν) L) * (diagHom ν d)⁻¹ := by
    rw [hM, _root_.mul_inv_rev, inv_inv]
  rw [hMinv, hM, Units.val_mul, Units.val_mul]
  have hDD : (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Matrix.diagonal v *
      ((diagHom ν d : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal v := by
    rw [← map_inv, coe_diagHom, coe_diagHom, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have h0 : (d i : L) ≠ 0 := Units.ne_zero _
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
    field_simp
  have hPP : ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) *
      (↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) = 1 :=
    (permGL π : GL (Fin ν) L).mul_inv
  have hPP' : (↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) *
      ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) = 1 :=
    (permGL π : GL (Fin ν) L).inv_mul
  have h3 : (↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) *
      Matrix.diagonal (fun k => v (π⁻¹ k)) *
        ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal v := by
    rw [permGL_inv_mul_diagonal_mul π (fun k => v (π⁻¹ k))]
    congr 1
    funext k
    simp
  calc ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) *
        (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) *
        Matrix.diagonal v * (((diagHom ν d : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) *
          (↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L)) =
      ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) *
        ((↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) *
        Matrix.diagonal v * ((diagHom ν d : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
          (↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
        simp only [Matrix.mul_assoc]
    _ = ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) * Matrix.diagonal v *
          (↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by rw [hDD]
    _ = ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) * ((↑(permGL π : GL (Fin ν) L)⁻¹ :
          Matrix (Fin ν) (Fin ν) L) * Matrix.diagonal (fun k => v (π⁻¹ k)) *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
          (↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by rw [h3]
    _ = (((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) * (↑(permGL π : GL (Fin ν) L)⁻¹ :
          Matrix (Fin ν) (Fin ν) L)) * Matrix.diagonal (fun k => v (π⁻¹ k)) *
          (((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) * (↑(permGL π : GL (Fin ν) L)⁻¹ :
            Matrix (Fin ν) (Fin ν) L)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPP, Matrix.one_mul, Matrix.mul_one]

end Diag

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
