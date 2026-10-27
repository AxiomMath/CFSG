module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUDelta

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv CFSG.Sporadic.Th.Max3

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem phiU_spec :
    d.phiU (centralizerSelf u) = altRep2A ∧
    d.phiU.range = Subgroup.centralizer {altRep2A} ∧
    d.phiU.ker = CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) ∧
    (∀ s : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}, s ≠ 1 →
      CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J) →
      ((d.phiU s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2, 2, 2}) ∧
    (∀ s : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}, s * s = 1 →
      ¬ CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J) →
      ((d.phiU s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2}) ∧
    ∃ j₀ : Fin 9, 4 ≤ (j₀ : ℕ) ∧ ∀ c : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
      ((c : J ⧸ Subgroup.center J) ∈ B.map (QuotientGroup.mk' (Subgroup.center J)) ↔
        ((d.phiU c : alternatingGroup (Fin 9)) : Perm (Fin 9)) j₀ = j₀) :=
  ⟨d.phiU_self, d.range_phiU, d.ker_phiU, fun _ hs1 hs => d.cycleType_phiU_of_genuine hs1 hs,
    fun _ hss hs => d.cycleType_phiU_of_not_genuine hss hs, d.exists_mem_map_iff_phiU⟩

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
