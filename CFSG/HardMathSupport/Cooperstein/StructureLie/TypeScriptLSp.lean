module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLHeart
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalIdentification
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Module Submodule CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial

section Heart

variable {m : ℕ}

@[expose] noncomputable def sumZeroDot (m : ℕ) : LinearMap.BilinForm (ZMod 2) (sumZero m) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => ∑ i, (x : Fin m → ZMod 2) i * (y : Fin m → ZMod 2) i)
    (fun x x' y => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (fun x y y' => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, Finset.mul_sum])

theorem sumZeroDot_apply (x y : sumZero m) :
    sumZeroDot m x y = ∑ i, (x : Fin m → ZMod 2) i * (y : Fin m → ZMod 2) i :=
  rfl

theorem sumZeroDot_comm (x y : sumZero m) : sumZeroDot m x y = sumZeroDot m y x := by
  simp only [sumZeroDot_apply, mul_comm]

theorem sumZeroDot_of_mem_onesLine (x : sumZero m) {y : sumZero m} (hy : y ∈ onesLine m) :
    sumZeroDot m x y = 0 := by
  obtain ⟨c, hc⟩ := mem_onesLine.mp hy
  rw [sumZeroDot_apply, hc, ← Finset.sum_mul, mem_sumZero.mp x.2, zero_mul]

@[expose] noncomputable def heartForm (m : ℕ) :
    LinearMap.BilinForm (ZMod 2) (sumZero m ⧸ onesLine m) :=
  let step1 : (sumZero m ⧸ onesLine m) →ₗ[ZMod 2] (sumZero m →ₗ[ZMod 2] ZMod 2) :=
    (onesLine m).liftQ (sumZeroDot m) (fun x hx => by
      rw [LinearMap.mem_ker]
      ext y
      rw [sumZeroDot_comm]
      exact sumZeroDot_of_mem_onesLine y hx)
  ((onesLine m).liftQ step1.flip (fun p hp => by
    rw [LinearMap.mem_ker]
    ext x
    exact sumZeroDot_of_mem_onesLine x hp)).flip

theorem heartForm_mk (x y : sumZero m) :
    heartForm m (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = sumZeroDot m x y :=
  rfl

theorem heartForm_isAlt (m : ℕ) : (heartForm m).IsAlt := by
  intro e
  induction e using Submodule.Quotient.induction_on with
  | H x =>
    rw [heartForm_mk, sumZeroDot_apply]
    have h : ∀ a : ZMod 2, a * a = a := by decide
    simp only [h]
    exact mem_sumZero.mp x.2

theorem heartForm_nondegenerate (m : ℕ) : (heartForm m).Nondegenerate := by
  have : FiniteDimensional (ZMod 2) (sumZero m ⧸ onesLine m) := inferInstance
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro e he
  induction e using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.Quotient.mk_eq_zero, mem_onesLine]
    have key : ∀ i j : Fin m,
        (x : Fin m → ZMod 2) i + (x : Fin m → ZMod 2) j = 0 := by
      intro i j
      have h := he (Submodule.Quotient.mk (pairVec i j))
      rw [heartForm_mk, sumZeroDot_apply, coe_pairVec] at h
      classical
      simpa only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h
    rcases isEmpty_or_nonempty (Fin m) with hm | ⟨⟨i₀⟩⟩
    · exact ⟨0, funext fun j => isEmptyElim j⟩
    · refine ⟨(x : Fin m → ZMod 2) i₀, funext fun j => ?_⟩
      have h := key i₀ j
      generalize (x : Fin m → ZMod 2) i₀ = a at h ⊢
      generalize (x : Fin m → ZMod 2) j = b at h ⊢
      revert a b
      decide

theorem finrank_heart_six : finrank (ZMod 2) (sumZero 6 ⧸ onesLine 6) = 4 := by
  rw [finrank_quotient_onesLine (by norm_num) (by decide)]

theorem heartForm_heartRep (σ : Equiv.Perm (Fin m)) (x y : sumZero m ⧸ onesLine m) :
    heartForm m
      (((heartRep m σ : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m)) :
        sumZero m ⧸ onesLine m →ₗ[ZMod 2] sumZero m ⧸ onesLine m) x)
      (((heartRep m σ : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m)) :
        sumZero m ⧸ onesLine m →ₗ[ZMod 2] sumZero m ⧸ onesLine m) y) = heartForm m x y := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [heartRep_apply_mk, heartRep_apply_mk, heartForm_mk, heartForm_mk, sumZeroDot_apply,
        sumZeroDot_apply]
      simp only [coe_sumZeroEquiv, permCoord_apply]
      exact Equiv.sum_comp σ⁻¹ (fun i => (x : Fin m → ZMod 2) i * (y : Fin m → ZMod 2) i)

theorem range_heartRep_le_bilinIsometryGroup (m : ℕ) :
    (heartRep m).range ≤ bilinIsometryGroup (heartForm m) := by
  rintro _ ⟨σ, rfl⟩ x y
  exact heartForm_heartRep σ x y

end Heart

theorem map_bilinIsometryGroup_congrLinearEquiv {R W W' : Type*} [CommSemiring R]
    [AddCommMonoid W] [Module R W] [AddCommMonoid W'] [Module R W']
    (f : LinearMap.BilinForm R W) (b : LinearMap.BilinForm R W') (e : W ≃ₗ[R] W')
    (he : ∀ x y, b (e x) (e y) = f x y) :
    (bilinIsometryGroup f).map (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom =
      bilinIsometryGroup b := by
  have key : ∀ g : LinearMap.GeneralLinearGroup R W,
      LinearMap.GeneralLinearGroup.congrLinearEquiv e g ∈ bilinIsometryGroup b ↔
        g ∈ bilinIsometryGroup f := by
    intro g
    rw [mem_bilinIsometryGroup, mem_bilinIsometryGroup]
    have happ : ∀ z, ((LinearMap.GeneralLinearGroup.congrLinearEquiv e g :
        LinearMap.GeneralLinearGroup R W') : W' →ₗ[R] W') z =
        e (((g : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) (e.symm z)) := fun z => rfl
    constructor
    · intro h x y
      have := h (e x) (e y)
      rw [happ, happ, e.symm_apply_apply, e.symm_apply_apply, he, he] at this
      exact this
    · intro h x y
      rw [happ, happ, he, h]
      rw [← he, e.apply_symm_apply, e.apply_symm_apply]
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (key g).mpr hg
  · intro hx
    refine ⟨(LinearMap.GeneralLinearGroup.congrLinearEquiv e).symm x, ?_,
      (LinearMap.GeneralLinearGroup.congrLinearEquiv e).apply_symm_apply x⟩
    exact (key _).mp (by rw [MulEquiv.apply_symm_apply]; exact hx)

section Order

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem nonempty_bilinIsometryGroup_mulEquiv_perm_six {f : LinearMap.BilinForm (ZMod 2) W}
    (hnd : f.Nondegenerate) (halt : f.IsAlt) (h4 : finrank (ZMod 2) W = 4) :
    Nonempty (↥(bilinIsometryGroup f) ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
      f halt hnd
  obtain rfl : m = 2 := by omega
  exact ⟨((bilinIsometryGroupEquivIsometryGroup f).trans e).trans glSymplecticTwoPerm⟩

theorem natCard_bilinIsometryGroup_symplectic_four {f : LinearMap.BilinForm (ZMod 2) W}
    (hnd : f.Nondegenerate) (halt : f.IsAlt) (h4 : finrank (ZMod 2) W = 4) :
    Nat.card ↥(bilinIsometryGroup f) = 720 := by
  obtain ⟨ψ⟩ := nonempty_bilinIsometryGroup_mulEquiv_perm_six hnd halt h4
  rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

end Order

theorem exists_heartSix_of_symplectic_four {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (f : LinearMap.BilinForm (ZMod 2) W) (hnd : f.Nondegenerate)
    (halt : f.IsAlt) (h4 : Module.finrank (ZMod 2) W = 4)
    (hinj : Function.Injective (CFSG.ComponentClassification.OutcomeLocal.heartRep 6)) :
    ∃ β : W ≃ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6),
      (bilinIsometryGroup f).map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
        (heartRep 6).range := by
  have : FiniteDimensional (ZMod 2) (sumZero 6 ⧸ onesLine 6) := inferInstance
  have hE4 := finrank_heart_six
  obtain ⟨e⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_form_isometry f
      (heartForm 6) halt hnd (heartForm_isAlt 6) (heartForm_nondegenerate 6) (by omega)
  refine ⟨e.toLinearEquiv, ?_⟩
  rw [map_bilinIsometryGroup_congrLinearEquiv f (heartForm 6) e.toLinearEquiv e.map_app']
  have hcard : Nat.card ↥(bilinIsometryGroup (heartForm 6)) = 720 :=
    natCard_bilinIsometryGroup_symplectic_four (heartForm_nondegenerate 6) (heartForm_isAlt 6) hE4
  have : Finite ↥(bilinIsometryGroup (heartForm 6)) :=
    Nat.finite_of_card_ne_zero (by omega)
  symm
  apply Subgroup.eq_of_le_of_card_ge (range_heartRep_le_bilinIsometryGroup 6)
  rw [hcard, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  rfl

end CFSG.HardMathSupport.Cooperstein.StructureLie
