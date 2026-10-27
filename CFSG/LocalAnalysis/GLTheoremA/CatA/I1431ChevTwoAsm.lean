module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem i1431ChevTwoS_of_residuals (h1 : U42InnField) (h2 : U42Outer) (h3 : U42FieldTwo) :
    I1431ChevTwoS := by
  intro Y _ _ hY hcore hRk hcat ξ hξ3 hξ1 J hJ hJT
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    have hchar : d.1.characteristic = 2 := hi
    obtain ⟨J', hJ', ψ, hψs, hψk⟩ := H1431c.component_to_simple_explicit hJ
    have hq : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ
    have hq' : CFSG.Open.IsQuasisimple (PQuot 3 J') :=
      CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ'
    haveI : Nontrivial (PQuot 3 J') := by
      have := hq'.2.toNontrivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 J' ⧸ Subgroup.center (PQuot 3 J'))
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.psimple_equiv_of_central_surj hq ψ hψs hψk
    have hT' : catalogIs (PSimple 3 J') S9.isU4two := by
      obtain ⟨i', hi', ⟨f⟩⟩ := hJT
      exact ⟨i', hi', ⟨eP.symm.trans f⟩⟩
    have hβ3 : H1431c.inducedAut ξ ^ 3 = 1 := by
      rw [show H1431c.inducedAut ξ =
          CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot Y ξ from rfl,
        ← map_pow, hξ3, map_one]
    have hβ1 : H1431c.inducedAut ξ ≠ 1 := fun h => hξ1 (H1431c.eq_one_of_inducedAut_eq_one hY.1 h)
    have hP : U42Pumpup (Y ⧸ Subgroup.center Y) (H1431c.inducedAut ξ) := ⟨hβ3, hβ1, J', hJ', hT'⟩
    have hS : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY
    by_cases hin : H1431c.inducedAut ξ ∈ innAutDerived (Y ⧸ Subgroup.center Y)
    · have hf := h1 _ hS hnab d hchar ⟨e⟩ _ hin hP
      exact ⟨.lie d, h3 Y hY hcore hRk d trivial hchar hf ⟨e⟩ _ hin hP, ⟨e⟩⟩
    · exact ⟨.lie d, Or.inr (Or.inr (Or.inr (Or.inr (h2 _ hS hnab d hchar ⟨e⟩ _ hin hP)))),
        ⟨e⟩⟩
  | _ => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
