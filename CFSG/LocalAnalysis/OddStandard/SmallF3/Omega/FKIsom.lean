module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap

variable {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  [AddCommGroup V'] [Module (ZMod 3) V'] [FiniteDimensional (ZMod 3) V']
  {Q : QuadraticForm (ZMod 3) V} {Q' : QuadraticForm (ZMod 3) V'}

@[expose] def FKStmt (hQ : Q.Nondegenerate) : Prop :=
  ∀ α : MulAut (omegaProj hQ), α * α = 1 → (¬ ∃ p : omegaProj hQ, α = MulAut.conj p) →
    ∃ (β : MulAut (omegaProj hQ)) (x : OGroup Q), x * x = 1 ∧ x ∉ omegaGroup hQ ∧
      β⁻¹ * α * β = MulAut.conjNormal (toProj Q x)

theorem fk_congr_conjNormal (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) (x : OGroup Q) :
    MulAut.congr (omegaProjCongr hQ hQ' e h2) (MulAut.conjNormal (toProj Q x)) =
      MulAut.conjNormal (toProj Q' (orthogonalGroupCongr e x)) := by
  refine MulEquiv.ext fun y => ?_
  apply Subtype.ext
  have hy : projOrthCongr e (((omegaProjCongr hQ hQ' e h2).symm y : omegaProj hQ) :
      ProjOrth Q) = (y : ProjOrth Q') := by
    have := coe_omegaProjCongr hQ hQ' e h2 ((omegaProjCongr hQ hQ' e h2).symm y)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, coe_omegaProjCongr,
    MulAut.conjNormal_apply, MulAut.conjNormal_apply, map_mul, map_mul, map_inv,
    projOrthCongr_toProj, hy]

theorem fkStmt_of_isometry (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) (h : FKStmt hQ') :
    FKStmt hQ := by
  intro α hα2 hinner
  set ε := omegaProjCongr hQ hQ' e h2 with hε
  have hα'2 : MulAut.congr ε α * MulAut.congr ε α = 1 := by
    rw [← map_mul, hα2, map_one]
  have hinner' : ¬ ∃ p : omegaProj hQ', MulAut.congr ε α = MulAut.conj p := by
    rintro ⟨p, hp⟩
    apply hinner
    refine ⟨ε.symm p, MulAut.congr ε |>.injective ?_⟩
    rw [hp]
    refine MulEquiv.ext fun y => ?_
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  obtain ⟨β', x', hx'2, hx'Ω, hβ'⟩ := h _ hα'2 hinner'
  refine ⟨MulAut.congr ε.symm β', (orthogonalGroupCongr e).symm x', ?_, ?_, ?_⟩
  · rw [← map_mul, hx'2, map_one]
  · intro hmem
    apply hx'Ω
    have := Subgroup.mem_map_of_mem (orthogonalGroupCongr e).toMonoidHom hmem
    rw [isoO_map_omegaGroup hQ hQ' e h2] at this
    simpa using this
  · apply (MulAut.congr ε).injective
    rw [fk_congr_conjNormal hQ hQ' e h2, MulEquiv.apply_symm_apply, ← hβ']
    simp only [map_mul, map_inv]
    rw [show MulAut.congr ε (MulAut.congr ε.symm β') = β' from MulEquiv.ext fun y => by
      simp [MulAut.congr_apply]]

end CFSG.OddStandard.SmallF3.Omega
