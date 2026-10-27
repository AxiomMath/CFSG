module

public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Struct

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_isom_of_normalizes (hF : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {g : GL (Fin 3) K} (hg : ∀ s ∈ unitarySU p f K 3, g * s * g⁻¹ ∈ unitarySU p f K 3) :
    ∃ u ∈ unitaryIsom3 hF, ∀ s : GL (Fin 3) K, g * s * g⁻¹ = u * s * u⁻¹ := by
  obtain ⟨c, u, hu, rfl⟩ := LocalBalance.AutL3.exists_isom_of_normalizes hF hq
    (LocalBalance.AutL3.mem_normalizer_of_forall hF fun M => ⟨⟨_, hg M M.2⟩, rfl⟩)
  refine ⟨u, hu, fun s => ?_⟩
  have hc : ∀ w : GL (Fin 3) K, GeneralLinearGroup.scalar (Fin 3) c * w =
      w * GeneralLinearGroup.scalar (Fin 3) c := fun w => (commute_scalar c w).eq.symm
  rw [show GeneralLinearGroup.scalar (Fin 3) c * u * s * (GeneralLinearGroup.scalar (Fin 3) c * u)⁻¹
      = GeneralLinearGroup.scalar (Fin 3) c * (u * s * u⁻¹) *
        (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ by group, hc]
  group

end CFSG.HardMathSupport.Solomon.Coordinator
