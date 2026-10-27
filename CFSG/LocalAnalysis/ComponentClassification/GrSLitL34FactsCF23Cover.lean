module

public import Certificates.Certificate22222
public import CFSG.LieType.Multipliers.L34
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

theorem invFixParts {i t : ℕ} (hi : i < 36) (ht : t < 64)
    (h2 : sq1M t i = true) : invFixM t i = true := by
  have h := Certificates.certificate22222
  simp only [invFixOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h i hi t ht with h' | h'
  · rw [h2] at h'
    exact absurd h' (by decide)
  · exact h'

theorem sq1M_of {t i : ℕ} (hi : i < 36)
    (h : wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1) : sq1M t i = true := by
  have hy := (tabRep_wordTab (tg t)).comp (tabRep_repTab hi)
  exact ((hy.comp hy).beq_iff TabRep.idTab).2 h

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

end CFSG.ComponentClassification.GrSLit.L34Facts.Real
