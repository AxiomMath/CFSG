module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutOuter

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)

theorem coe_scalar_mul_apply (c : Fˣ) (g : GL (Fin 6) F) (i j : Fin 6) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 6) c * g : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) i j = c * (g : Matrix (Fin 6) (Fin 6) F) i j := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_mul]

theorem exists_apply_ne_zero (g : GL (Fin 6) F) :
    ∃ i j, (g : Matrix (Fin 6) (Fin 6) F) i j ≠ 0 := by
  by_contra hg
  push Not at hg
  have h0 : (g : Matrix (Fin 6) (Fin 6) F) = 0 := Matrix.ext hg
  have := g.mul_inv
  rw [h0, Matrix.zero_mul] at this
  exact zero_ne_one (congrFun (congrFun this 0) 0)

theorem sixProj_injOn_binarySp {g g' : sixS h} (hg : g ∈ binarySp h) (hg' : g' ∈ binarySp h)
    (hgg' : sixProj h g = sixProj h g') : g = g' := by
  obtain ⟨c, hc⟩ := (sixProj_eq_iff h).mp hgg'
  obtain ⟨i, j, hij⟩ := exists_apply_ne_zero (g : GL (Fin 6) F)
  have hgij : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i j = 1 :=
    ((mem_bot_iff h).mp (hg i j)).resolve_left hij
  have hc1 : (c : F) = 1 := by
    have h1 := hg' i j
    rw [hc, coe_scalar_mul_apply, hgij, mul_one] at h1
    exact ((mem_bot_iff h).mp h1).resolve_left c.ne_zero
  have hc1' : c = 1 := Units.ext hc1
  refine Subtype.ext ?_
  rw [hc, hc1', map_one, one_mul]

theorem sigmaS_scalar (c : Fˣ) :
    ((sigmaS h ⟨_, scalar_mem_sixS h c⟩ : sixS h) : GL (Fin 6) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (c ^ 2) := by
  refine Units.ext ?_
  rw [coe_sigmaS, coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    scalar_apply, scalar_apply, diagonal_map (map_zero _), Units.val_pow_eq_pow_val,
    barEquiv_apply]

theorem sigmaS_scalar_mul (c : Fˣ) (g : sixS h) :
    ((sigmaS h ((⟨_, scalar_mem_sixS h c⟩ : sixS h) * g) : sixS h) : GL (Fin 6) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (c ^ 2) * (sigmaS h g : GL (Fin 6) F) := by
  rw [map_mul, Subgroup.coe_mul, sigmaS_scalar]

theorem scalar_sq_mul_inv (c : Fˣ) (x : GL (Fin 6) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) (c ^ 2) *
        ((Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ * x) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c * x := by
  rw [← mul_assoc, ← map_inv, ← map_mul, sq, mul_assoc, mul_inv_cancel, mul_one]

theorem fixed_sigmaQ_eq :
    {x : sixQ h | sigmaQ h x = x} = ((binarySp h).map (sixProj h) : Set (sixQ h)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := sixProj_surjective h x
    change sigmaQ h (sixProj h g) = sixProj h g at hx
    rw [sigmaQ_sixProj'] at hx
    obtain ⟨c, hc⟩ := (sixProj_eq_iff h).mp hx
    set g' : sixS h := (⟨_, scalar_mem_sixS h c⟩ : sixS h) * g with hg'
    have hfix : sigmaS h g' = g' := by
      refine Subtype.ext ?_
      rw [hg', sigmaS_scalar_mul]
      have hσg : (sigmaS h g : GL (Fin 6) F) =
          (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ * (g : GL (Fin 6) F) := by
        rw [hc, inv_mul_cancel_left]
      rw [hσg, scalar_sq_mul_inv]
      rfl
    refine ⟨g', (sigmaS_eq_self_iff h g').mp hfix, ?_⟩
    rw [eq_comm, sixProj_eq_iff]
    exact ⟨c, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    change sigmaQ h (sixProj h g) = sixProj h g
    rw [sigmaQ_sixProj', (sigmaS_eq_self_iff h g).mpr hg]

theorem coe_t0Elt_eq :
    ((t0Elt h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 + single 0 3 1 := by
  rw [t0Elt, coe_tElt, nMat_dMat_one]

noncomputable abbrev lOne : (Fin 6 → F) →ₛₗ[h.bar] (Fin 6 → F) :=
  antiunitaryMap h ((t0Elt h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)

theorem lOne_apply (v : Fin 6 → F) :
    lOne h v = ![h.bar (v 0) + h.bar (v 3), h.bar (v 1), h.bar (v 2), h.bar (v 3), h.bar (v 4),
      h.bar (v 5)] := by
  rw [antiunitaryMap_apply, coe_t0Elt_eq]
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_six, one_apply, single_apply]

theorem lOne_lOne (v : Fin 6 → F) : lOne h (lOne h v) = v := by
  have := h.charP
  rw [lOne_apply, lOne_apply]
  funext i
  fin_cases i <;> simp [map_add, h.bar_bar]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem gramForm_self_eq_of_mem_fixed {x : Fin 6 → F} (hx : lOne h x = x) :
    gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) x x =
      gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) (Pi.single 0 1) x := by
  rw [lOne_apply] at hx
  have e0 : x 0 ^ 2 + x 3 ^ 2 = x 0 := by simpa [bar_eq_sq h] using congrFun hx 0
  have e1 : x 1 ^ 2 = x 1 := by simpa [bar_eq_sq h] using congrFun hx 1
  have e2 : x 2 ^ 2 = x 2 := by simpa [bar_eq_sq h] using congrFun hx 2
  have e3 : x 3 ^ 2 = x 3 := by simpa [bar_eq_sq h] using congrFun hx 3
  have e4 : x 4 ^ 2 = x 4 := by simpa [bar_eq_sq h] using congrFun hx 4
  have e5 : x 5 ^ 2 = x 5 := by simpa [bar_eq_sq h] using congrFun hx 5
  rw [gramForm_sixJ, gramForm_sixJ]
  simp only [bar_eq_sq h, Pi.single_apply]
  simp
  linear_combination x 3 * e0 + x 4 * e1 + x 5 * e2 + (x 0 - x 3 - 1) * e3 + x 1 * e4 +
    x 2 * e5 + (x 1 * x 4 + x 2 * x 5 + x 0 * x 3 - x 3) * two_eq_zero h

theorem gramForm_mulVec_mulVec (g : sixS h) (x y : Fin 6 → F) :
    gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F)
        (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ x)
        (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ y) =
      gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) x y := by
  rw [gramForm_mulVec, mem_primeFormUnitary.mp g.2.1]

theorem mulVec_lOne_of_twisted {g : sixS h} (hg : t0Elt h * sigmaS h g * (t0Elt h)⁻¹ = g)
    (v : Fin 6 → F) :
    ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ lOne h v =
      lOne h (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ v) := by
  have hmat : ((t0Elt h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map h.bar =
        ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
          ((t0Elt h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    have h1 : t0Elt h * sigmaS h g = g * t0Elt h :=
      calc t0Elt h * sigmaS h g = (t0Elt h * sigmaS h g * (t0Elt h)⁻¹) * t0Elt h := by group
        _ = g * t0Elt h := by rw [hg]
    have h2 := congrArg (fun x : sixS h => ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) h1
    simp only [Subgroup.coe_mul, Units.val_mul, coe_sigmaS, coe_glAut] at h2
    exact h2
  rw [antiunitaryMap_apply, antiunitaryMap_apply, mulVec_mulVec]
  have hbar : (fun i => h.bar ((((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ v) i)) =
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map h.bar *ᵥ fun i => h.bar (v i) := by
    funext i
    exact RingHom.map_mulVec h.bar _ v i
  rw [hbar, mulVec_mulVec, hmat]

theorem twisted_inv {g : sixS h} (hg : t0Elt h * sigmaS h g * (t0Elt h)⁻¹ = g) :
    t0Elt h * sigmaS h g⁻¹ * (t0Elt h)⁻¹ = g⁻¹ := by
  rw [map_inv]
  calc t0Elt h * (sigmaS h g)⁻¹ * (t0Elt h)⁻¹ = (t0Elt h * sigmaS h g * (t0Elt h)⁻¹)⁻¹ := by
        group
    _ = g⁻¹ := by rw [hg]

theorem gramForm_single_zero (y : Fin 6 → F) :
    gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) (Pi.single 0 1) y = y 3 := by
  rw [gramForm_sixJ]
  simp

theorem mulVec_single_zero_of_twisted {g : sixS h}
    (hg : t0Elt h * sigmaS h g * (t0Elt h)⁻¹ = g) :
    ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  set G := ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) with hG
  set Gi := (((g⁻¹ : sixS h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) with hGi
  have hGGi : G * Gi = 1 := by
    rw [hG, hGi, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one]
  have hvan : ∀ x : Fin 6 → F, lOne h x = x →
      gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F)
        (G *ᵥ Pi.single 0 1 - Pi.single 0 1) x = 0 := by
    intro x hx
    set y := Gi *ᵥ x with hy
    have hyfix : lOne h y = y := by
      rw [hy, ← mulVec_lOne_of_twisted h (twisted_inv h hg), hx]
    have hGy : G *ᵥ y = x := by rw [hy, mulVec_mulVec, hGGi, one_mulVec]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    calc gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) (G *ᵥ Pi.single 0 1) x
        = gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) (G *ᵥ Pi.single 0 1) (G *ᵥ y) := by
          rw [hGy]
      _ = gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) (Pi.single 0 1) y :=
          gramForm_mulVec_mulVec h g _ _
      _ = gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) y y :=
          (gramForm_self_eq_of_mem_fixed h hyfix).symm
      _ = gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) (G *ᵥ y) (G *ᵥ y) :=
          (gramForm_mulVec_mulVec h g _ _).symm
      _ = gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) (Pi.single 0 1) x := by
          rw [hGy, gramForm_self_eq_of_mem_fixed h hx]
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hspan := span_conjFixed_of_ne (h := h) (τ := lOne h) (lOne_lOne h) hc₀
  have hall : ∀ y : Fin 6 → F,
      gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F)
        (G *ᵥ Pi.single 0 1 - Pi.single 0 1) y = 0 := by
    intro y
    have hle : Submodule.span F (conjFixed h (lOne h) : Set (Fin 6 → F)) ≤
        LinearMap.ker (gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F)
          (G *ᵥ Pi.single 0 1 - Pi.single 0 1)) :=
      Submodule.span_le.mpr fun x hx => hvan x hx
    rw [hspan] at hle
    exact hle (Submodule.mem_top (x := y))
  have h0 := gramForm_separatingLeft h (primeFormGram_det_ne_zero (sixJ h)) _ hall
  exact sub_eq_zero.mp h0

theorem commute_t0Elt_of_twisted {g : sixS h} (hg : t0Elt h * sigmaS h g * (t0Elt h)⁻¹ = g) :
    t0Elt h * g = g * t0Elt h := by
  set G := ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) with hG
  have hcol : ∀ a, G a 0 = if a = 0 then 1 else 0 := by
    intro a
    have := congrFun (mulVec_single_zero_of_twisted h hg) a
    rw [mulVec_single_one, col_apply, Pi.single_apply] at this
    exact this
  have hrow : ∀ b, G 3 b = if b = 3 then 1 else 0 := by
    intro b
    have h1 : (G *ᵥ Pi.single b 1) 3 = (Pi.single b 1 : Fin 6 → F) 3 := by
      have := gramForm_mulVec_mulVec h g (Pi.single 0 1) (Pi.single b 1)
      rw [mulVec_single_zero_of_twisted h hg, gramForm_single_zero, gramForm_single_zero] at this
      exact this
    rw [mulVec_single_one, col_apply, Pi.single_apply] at h1
    rw [h1]
    simp only [eq_comm]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_t0Elt_eq, ← hG,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  congr 1
  ext a b
  simp only [mul_apply, single_apply]
  fin_cases a <;> fin_cases b <;> simp [hcol, hrow]

theorem fixed_alphaOne_eq :
    {x : sixQ h | alphaOne h x = x} =
      ((binarySp h ⊓ Subgroup.centralizer {t0Elt h}).map (sixProj h) : Set (sixQ h)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := sixProj_surjective h x
    change alphaOne h (sixProj h g) = sixProj h g at hx
    rw [alphaOne_sixProj] at hx
    obtain ⟨c, hc⟩ := (sixProj_eq_iff h).mp hx
    set g' : sixS h := (⟨_, scalar_mem_sixS h c⟩ : sixS h) * g with hg'
    have htw : t0Elt h * sigmaS h g' * (t0Elt h)⁻¹ = g' := by
      refine Subtype.ext ?_
      have hX : ((t0Elt h * sigmaS h g * (t0Elt h)⁻¹ : sixS h) : GL (Fin 6) F) =
          (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ * (g : GL (Fin 6) F) := by
        rw [hc, inv_mul_cancel_left]
      have hcomm : ∀ y : GL (Fin 6) F, y * Matrix.GeneralLinearGroup.scalar (Fin 6) (c ^ 2) =
          Matrix.GeneralLinearGroup.scalar (Fin 6) (c ^ 2) * y := fun y =>
        (commute_scalar (c ^ 2) y).eq
      rw [Subgroup.coe_mul, Subgroup.coe_mul, sigmaS_scalar_mul, ← mul_assoc, hcomm,
        mul_assoc, mul_assoc]
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at hX
      rw [← mul_assoc ((t0Elt h : sixS h) : GL (Fin 6) F), hX, scalar_sq_mul_inv]
      rfl
    have hcomm := commute_t0Elt_of_twisted h htw
    have hfix : sigmaS h g' = g' := by
      have h1 : sigmaS h g' = (t0Elt h)⁻¹ * g' * t0Elt h :=
        calc sigmaS h g' = (t0Elt h)⁻¹ * (t0Elt h * sigmaS h g' * (t0Elt h)⁻¹) * t0Elt h := by
              group
          _ = (t0Elt h)⁻¹ * g' * t0Elt h := by rw [htw]
      rw [h1, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    refine ⟨g', ⟨(sigmaS_eq_self_iff h g').mp hfix,
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩, ?_⟩
    rw [eq_comm, sixProj_eq_iff]
    exact ⟨c, rfl⟩
  · rintro ⟨g, ⟨hg, hgc⟩, rfl⟩
    change alphaOne h (sixProj h g) = sixProj h g
    rw [alphaOne_sixProj, (sigmaS_eq_self_iff h g).mpr hg,
      (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm, mul_inv_cancel_right]

end CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
