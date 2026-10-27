module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHBasic
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslHb
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslType

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartOne.KCUnitary
open scoped commutatorElement

theorem t6psph_finite_generalLinearGroup {E W : Type} [Field E] [Finite E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

@[expose] noncomputable def t6psph_scalarGL {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (d : Eˣ) : LinearMap.GeneralLinearGroup E W :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.smulOfUnit d)

theorem t6psph_scalarGL_central {E W : Type} [Field E] [AddCommGroup W] [Module E W] (d : Eˣ) :
    t6psph_scalarGL (E := E) (W := W) d ∈ Subgroup.center (LinearMap.GeneralLinearGroup E W) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv E W).injective
  exact (smulOfUnit_comm (V := W) d (LinearMap.GeneralLinearGroup.generalLinearEquiv E W h)).symm

theorem t6psph_det_scalarGL {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    [Module.Free E W] (d : Eˣ) :
    Units.map (LinearMap.det : Module.End E W →* E) (t6psph_scalarGL (E := E) (W := W) d) =
      d ^ Module.finrank E W := by
  apply Units.ext
  have := congrArg Units.val (det_smulOfUnit (E := E) (V := W) d)
  rw [LinearEquiv.coe_det] at this
  rw [Units.val_pow_eq_pow_val] at this ⊢
  exact this

theorem t6psph_sqOK_generalLinear (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (h4 : ∃ s : Finset E, s.card = 4) {q : ℕ} (hq : 10 ≤ q) :
    t6psph_SqOK q (LinearMap.GeneralLinearGroup E W) := by
  haveI := t6psph_finite_generalLinearGroup (E := E) (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · intro hQ hT g
    set D : LinearMap.GeneralLinearGroup E W →* Eˣ :=
      Units.map (LinearMap.det : Module.End E W →* E) with hD
    have hker : CFSG.IsQuasisimple ↥D.ker := isQuasisimple_ker_det hm (Or.inr h4)
    have hcomm : commutator (LinearMap.GeneralLinearGroup E W) = D.ker :=
      t6psph_commutator_eq_ker D hker.1
    by_cases hm3 : 3 ≤ Module.finrank E W
    · exfalso
      rw [hcomm] at hT
      obtain ⟨e⟩ := nonempty_specialLinearGroup_mulEquiv_ker_det (E := E) (W := W)
      exact not_isTypeL2_specialLinear hO hm3 hq (p6_isTypeL2_of_equiv e.symm hT)
    · have hm2 : Module.finrank E W = 2 := by omega
      rw [hcomm]
      refine t6psph_sq_of_scalar D
        (fun g => ⟨t6psph_scalarGL (D g), t6psph_scalarGL_central _, ?_⟩) g
      rw [hD, t6psph_det_scalarGL, hm2]
  · refine t6psph_sqOK_of_commutative hq fun a b => Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    exact (End_commute_of_finrank_le_one (by omega) _ _).eq

end CFSG.HardMathSupport.Dickson.Sec6.I1431
