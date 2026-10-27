module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBlocks

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

section Blocks

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem goodBlocks_derived {g : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin n → K)))) :
    ∃ k : ℕ, ∀ x ∈ derivedSeries ↥(fixSubgroup (slConjugation n K g)) k,
      (x : SpecialLinearGroup (Fin n) K) ∈
        ⨆ h : {h : primaryFactors (glA g : Module.End K (Fin n → K)) // IsGoodFactor g h},
          specialFactor g h.1.1 := by
  classical
  haveI : ∀ b : {b : primaryFactors (glA g : Module.End K (Fin n → K)) // ¬ IsGoodFactor g b},
      Group.IsSolvable (blockGL (glA g : Module.End K (Fin n → K)) b.1.1) := fun b =>
    isSolvable_blockGL_of_not_good b.1.2 b.2
  haveI : Group.IsSolvable ((b : primaryFactors (glA g : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) := inferInstance
  haveI : Group.IsSolvable ((b : {b : primaryFactors (glA g : Module.End K (Fin n → K)) //
      ¬ IsGoodFactor g b}) → blockGL (glA g : Module.End K (Fin n → K)) b.1.1) :=
    t6psl_isSolvable_pi
  obtain ⟨k, hk⟩ := t6psl_derived_le_ker (blockDetHom hsq)
  refine ⟨k, fun x hx => ?_⟩
  have hg1 : blockDetHom hsq x = 1 := MonoidHom.mem_ker.1 (hk hx)
  exact mem_iSup_specialFactor_of_blockDetHom_eq_one hsq x hg1

theorem isSolvable_centralizer_of_no_good {g : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin n → K))))
    (hno : ∀ h ∈ primaryFactors (glA g : Module.End K (Fin n → K)), ¬ IsGoodFactor g h) :
    Group.IsSolvable ↥(fixSubgroup (slConjugation n K g)) := by
  obtain ⟨k, hk⟩ := goodBlocks_derived hsq
  have hempty : IsEmpty {h : primaryFactors (glA g : Module.End K (Fin n → K)) //
      IsGoodFactor g h} := ⟨fun h => hno h.1.1 h.1.2 h.2⟩
  refine ⟨⟨k, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  have := hk x hx
  rw [iSup_of_empty, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact Subtype.ext this

end Blocks

end CFSG.HardMathSupport.Dickson.Sec6.I1431
