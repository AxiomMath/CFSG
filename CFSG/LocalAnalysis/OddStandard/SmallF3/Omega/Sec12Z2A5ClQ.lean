module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128ClQ

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec128_normal_perfect_typeK {Q : Type} [Group Q]
    (hQ : IsO4Plus4 Q ∨ BenderL34Socle Q) (P : Subgroup Q) [hPn : P.Normal]
    (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥) :
    (P.index = 2 ∧
        Nonempty (↥P ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))))) ∨
      LieModel ↥P .PSL 2 2 4 ∨ LieModel ↥P .PSU 3 2 2 ∨ LieModel ↥P .PSL 3 2 2 := by
  rcases hQ with h | ⟨E, hEn, hEs, -, hd, hT⟩
  · obtain ⟨hidx, hty⟩ := sec128_normal_perfect_type (Or.inl h) P hP hP1
    rcases hty with h1 | h1 | h1
    · exact Or.inl ⟨hidx, h1⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr h1))
  · haveI := hEn
    have hPE : P = E := benderL34_perfect_eq hEs hd hP hP1
    subst hPE
    exact Or.inr hT

end CFSG.OddStandard.SmallF3.Omega
