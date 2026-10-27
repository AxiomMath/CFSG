module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ISetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IFaith
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAutStd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4I_conjNormal_bijective_std :
    Function.Bijective (MulAut.conjNormal : ProjOrth Sec4IQ →* MulAut Sec4IOmega) := by
  refine ⟨conjNormal_injective_seven sec4IQ_nondegenerate sec4IQ_finrank sec4IQ_quadSign, ?_⟩
  intro α
  obtain ⟨A, hA⟩ := sec4I_exists_conj_of_mulAut_std α
  refine ⟨toProj Sec4IQ A, ?_⟩
  apply MulEquiv.ext
  intro p
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  exact (hA p).symm

theorem sec4I_exists_theta (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) (ψ : omegaProj hQ ≃* Sec4IOmega) :
    ∃ Θ : ProjOrth Q ≃* ProjOrth Sec4IQ, ∀ (g : ProjOrth Q) (w : omegaProj hQ),
      ((ψ ((MulAut.conjNormal g : MulAut (omegaProj hQ)) w) : Sec4IOmega) : ProjOrth Sec4IQ) =
        Θ g * ((ψ w : Sec4IOmega) : ProjOrth Sec4IQ) * (Θ g)⁻¹ := by
  let c0e : ProjOrth Sec4IQ ≃* MulAut Sec4IOmega :=
    MulEquiv.ofBijective MulAut.conjNormal sec4I_conjNormal_bijective_std
  let Θ' : ProjOrth Q →* ProjOrth Sec4IQ :=
    c0e.symm.toMonoidHom.comp
      ((MulAut.congr ψ).toMonoidHom.comp
        (MulAut.conjNormal : ProjOrth Q →* MulAut (omegaProj hQ)))
  have hinj : Function.Injective Θ' :=
    c0e.symm.injective.comp ((MulAut.congr ψ).injective.comp
      (conjNormal_injective_seven hQ hdim hσ))
  haveI : Finite (ProjOrth Sec4IQ) := Nat.finite_of_card_ne_zero (by
    rw [natCard_projOrth_seven sec4IQ_nondegenerate sec4IQ_finrank]
    norm_num)
  have hbij : Function.Bijective Θ' := hinj.bijective_of_nat_card_le (by
    rw [natCard_projOrth_seven hQ hdim, natCard_projOrth_seven sec4IQ_nondegenerate
      sec4IQ_finrank])
  refine ⟨MulEquiv.ofBijective Θ' hbij, fun g w => ?_⟩
  have h1 : MulAut.conjNormal (Θ' g) = MulAut.congr ψ (MulAut.conjNormal g) :=
    c0e.apply_symm_apply (MulAut.congr ψ (MulAut.conjNormal g))
  have h3 : (MulAut.congr ψ (MulAut.conjNormal g)) (ψ w) =
      ψ ((MulAut.conjNormal g : MulAut (omegaProj hQ)) w) := by
    simp [MulAut.congr_apply]
  have h2 : (((MulAut.conjNormal (Θ' g) : MulAut Sec4IOmega) (ψ w) : Sec4IOmega) :
      ProjOrth Sec4IQ) = Θ' g * ((ψ w : Sec4IOmega) : ProjOrth Sec4IQ) * (Θ' g)⁻¹ :=
    MulAut.conjNormal_apply _ _
  rw [h1, h3] at h2
  exact h2

end CFSG.OddStandard.SmallF3.Omega
