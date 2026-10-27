module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaNorm
public import CFSG.Assembly.ComponentTypeDefs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.RankThree.PartTwo.KFacts
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_psuConj_of_isConjByGL (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (φ : MulAut (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)))
    (hφ : LocalBalance.Lemma53Ns.IsConjByGL (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K) φ) :
    ∃ A : unitaryIsom3 h,
      MulAut.congr (unitaryPSUEquiv h (n := 3) (by norm_num)).symm φ = psuConj h A := by
  obtain ⟨g, hg, hgφ⟩ := hφ
  obtain ⟨l, hl⟩ := exists_scalar_mul_mem_unitaryIsom3 h hq hg
  refine ⟨⟨_, hl⟩, ?_⟩
  refine MulEquiv.ext fun x => ?_
  obtain ⟨s, rfl⟩ := unitaryProj_surjective h 3 x
  have hmem : g * (s : GL (Fin 3) K) * g⁻¹ ∈ unitarySU p f K 3 :=
    (Subgroup.mem_normalizer_iff.1 hg _).1 s.2
  show (unitaryPSUEquiv h (n := 3) (by norm_num)).symm
      (φ ((unitaryPSUEquiv h (n := 3) (by norm_num)) (unitaryProj h 3 s))) =
    psuConj h ⟨_, hl⟩ (unitaryProj h 3 s)
  rw [unitaryPSUEquiv_unitaryProj]
  have key := hgφ s ⟨_, hmem⟩ rfl
  refine (congrArg _ key).trans ?_
  show _ = unitaryProj h 3 (suConj h ⟨_, hl⟩ s)
  refine (MulEquiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (unitaryPSUEquiv_unitaryProj h (n := 3) (by norm_num) _).symm
  congr 1
  apply Subtype.ext
  rw [coe_suConj]
  change _ = ((Matrix.GeneralLinearGroup.scalar (Fin 3) l * g) * (s : GL (Fin 3) K) *
    (Matrix.GeneralLinearGroup.scalar (Fin 3) l * g)⁻¹)
  have hc := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3) l (g * (s : GL (Fin 3) K) * g⁻¹)
  calc g * (s : GL (Fin 3) K) * g⁻¹
      = (g * (s : GL (Fin 3) K) * g⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 3) l *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) l)⁻¹ := by group
    _ = _ := by
      rw [← hc]
      group

end CFSG.HardMathSupport.Solomon.Coordinator
