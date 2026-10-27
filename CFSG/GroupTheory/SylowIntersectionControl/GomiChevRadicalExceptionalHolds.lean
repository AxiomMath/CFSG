module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Exceptional
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.ExcUntwisted
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.E6Twisted
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalOfChar

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Blueprint

theorem chevParabolicRadicalSimple_of_chevalleyExceptionalModel
    {K : Type} [Group K] [Finite K] {t : StatedLieTag} {f : ℕ} (hK : IsSimpleGroup K)
    (h : ChevalleyExceptionalModel K t 2 f) : ChevParabolicRadicalSimple K := by
  have key : ∀ {t : StatedLieTag}, t ∈ chevalleyExceptionalTags →
      Quasithin.LieOver.AsLieTwoAt t → ChevalleyExceptionalModel K t 2 f →
        ChevParabolicRadicalSimple K := fun ht hA h =>
    chevParabolicRadicalSimple_of_overgroups hK
      (hA 0 f K hK h.1 (Or.inr (Or.inl ⟨rfl, ht, h⟩))).1
  cases t <;> first | exact (h.2 : False).elim | skip
  case G2 => exact key (by decide) Quasithin.LieOver.asLieTwoAt_g2 h
  case F4 => exact key (by decide) Quasithin.LieOver.asLieTwoAt_f4 h
  case E6 => exact key (by decide) Quasithin.LieOver.asLieTwoAt_e6 h
  case E7 => exact key (by decide) Quasithin.LieOver.asLieTwoAt_e7 h
  case E8 => exact key (by decide) Quasithin.LieOver.asLieTwoAt_e8 h
  case twistedE6 => exact key (by decide) Quasithin.LieOver.asLieTwoAt_twistedE6 h
  case trialityD4 => exact key (by decide) Quasithin.LieOver.asLieTwoAt_trialityD4 h

end CFSG.GroupTheory
