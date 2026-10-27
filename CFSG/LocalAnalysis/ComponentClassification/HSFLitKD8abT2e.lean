module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Basic
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD7Basic

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

variable {S}

theorem mem_normalizer_of_conj_le {n : X} {H : Subgroup X} (h : ∀ g ∈ H, n * g * n⁻¹ ∈ H) :
    n ∈ normalizer (H : Set X) := by
  have hle : H.map (MulAut.conj n).toMonoidHom ≤ H := by
    rintro _ ⟨g, hg, rfl⟩
    exact h g hg
  refine Sec7.mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [card_map_of_injective (MulAut.conj n).injective]

end KD8ab

end CFSG.ComponentClassification.HSFLit
