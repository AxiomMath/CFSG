module

public import CFSG.Sporadic.Schreier.LyOddCoreAll
public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Ly


theorem pPrimeCore_cen_eq_bot_of_Ly {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hLy : IsSporadic G .Ly) {t : G} (ht : orderOf t = 2) :
    pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ := by
  have htop : CFSG.generalizedFitting G = ⊤ := by
    rw [generalizedFitting_eq_componentClassification]
    exact ComponentClassification.GSLit.generalizedFitting_eq_top_of_simple
  let e : CFSG.generalizedFitting G ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hF : IsSimpleGroup (CFSG.generalizedFitting G) := e.isSimpleGroup
  have hnab : ∃ a b : CFSG.generalizedFitting G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hJ : Nonempty (CFSG.generalizedFitting G ≃* NativeSporadic.Ly) :=
    ⟨e.trans hLy.some⟩
  obtain ⟨-, h⟩ := CFSG.Sporadic.LySchreier.full_group_all_involution_odd_core hF hnab hJ
  have h2 := h t ht
  rwa [ComponentClassification.SymmetricLocal.oddCore_eq_pPrimeCore_two] at h2

end Ly

end CFSG.OddStandard.Solomon75
