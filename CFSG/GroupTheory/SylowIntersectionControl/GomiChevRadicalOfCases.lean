module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalSimple
public import CFSG.LieType.ChevTwo.ModelSplit
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalClassical
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalOfChar
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Blueprint

theorem gomiChevRadical_of_cases (hsplit : LieType.ChevTwo.ChevTwoModelSplit)
    (hexc : ∀ {K : Type} [Group K] [Finite K] {t : StatedLieTag} {f : ℕ}, IsSimpleGroup K →
      ChevalleyExceptionalModel K t 2 f → ChevParabolicRadicalSimple K)
    (hree : ∀ {K : Type} [Group K] [Finite K] {n f : ℕ}, IsSimpleGroup K →
      LieModel K .twistedF4 n 2 f → ChevParabolicRadicalSimple K)
    (htits : ∀ {K : Type} [Group K] [Finite K] {n f : ℕ}, IsSimpleGroup K →
      LieModel K .Tits n 2 f → ChevParabolicRadicalSimple K)
    (halt : ∀ {K : Type} [Group K] [Finite K], IsSimpleGroup K →
      (K ≃* alternatingGroup (Fin 6)) → ChevParabolicRadicalSimple K)
    (hu : ∀ {K : Type} [Group K] [Finite K], IsSimpleGroup K →
      StatedClassicalModel K .PSU 3 3 1 → ChevParabolicRadicalSimple K) :
    GomiChevRadical := by
  refine gomiChevRadical_of_simple fun K _ _ hK hc => ?_
  rcases hsplit K hc with ⟨t, n, f, ht, hm⟩ | ⟨n, f, hm⟩ | he | hm
  · rcases id hm with ⟨htc, hcl⟩ | ⟨rfl, -, hce⟩ | ⟨rfl, htr, -⟩ | ⟨rfl, rfl, hsz⟩
    · exact chevParabolicRadicalSimple_of_statedClassicalModel hK htc hcl
    · exact hexc hK hce
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at htr
      rcases htr with rfl | rfl | rfl
      · exact absurd hm.admissible.2.2.2.1 (by decide)
      · exact hree hK hm
      · exact absurd rfl ht
    · exact chevParabolicRadicalSimple_of_overgroups hK
        (QuasithinUnique.Bridge.Over.overgroups_isSz hsz)
  · exact htits hK hm
  · exact halt hK he.some
  · exact hu hK hm

end CFSG.GroupTheory
