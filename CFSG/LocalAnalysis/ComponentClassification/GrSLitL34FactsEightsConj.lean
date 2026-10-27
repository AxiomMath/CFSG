
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEightsConjBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEightsConjBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylow
public import Certificates.Certificate22205
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsQuatBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem conjParts : ConjParts := by
  have h := Certificates.certificate22205
  simp only [conjOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact ⟨fun d hd => ⟨(h.1 d hd).1.1, (h.1 d hd).1.2, (h.1 d hd).2⟩,
    fun d hd => ⟨(h.2 d hd).1.1, (h.2 d hd).1.2, (h.2 d hd).2⟩⟩

theorem exists_conj_tg4_U1 {v : Equiv.Perm (Fin 42)} (hv : v ∈ U1) (hv1 : v ≠ 1) :
    ∃ s ∈ P1, s * v * s⁻¹ = wordPerm (tg 4) := by
  obtain ⟨k, hk, rfl⟩ := mem_U1_iff.1 hv
  have hk0 : k ≠ 0 := fun h => hv1 (by rw [h, wordPerm_tg_zero])
  obtain ⟨d, hd, rfl⟩ := conjP1_idx k hk hk0
  obtain ⟨hf, hinv, hc⟩ := conjParts.p1 d hd
  refine ⟨wordPerm d.2, mem_of_found_enum enumerates_P1 (tabRep_wordTab _) hf, ?_⟩
  have hi := tabRep_invTab_of_invOK hinv (tabRep_wordTab d.2)
  exact ((tabRep_wordTab d.2).conjTab (tabRep_tgT d.1) hi).perm_eq (hc ▸ tabRep_tgT 4)

theorem exists_conj_tg4_U2 {v : Equiv.Perm (Fin 42)} (hv : v ∈ U2) (hv1 : v ≠ 1) :
    ∃ s ∈ P2, s * v * s⁻¹ = wordPerm (tg 4) := by
  obtain ⟨k, hk, rfl⟩ := mem_U2_iff.1 hv
  have hk0 : k ≠ 0 := fun h => hv1 (by rw [h, mul_zero, wordPerm_tg_zero])
  obtain ⟨d, hd, rfl⟩ := conjP2_idx k hk hk0
  obtain ⟨hf, hinv, hc⟩ := conjParts.p2 d hd
  refine ⟨wordPerm d.2, mem_of_found_enum enumerates_P2 (tabRep_wordTab _) hf, ?_⟩
  have hi := tabRep_invTab_of_invOK hinv (tabRep_wordTab d.2)
  exact ((tabRep_wordTab d.2).conjTab (tabRep_tgT (4 * d.1)) hi).perm_eq (hc ▸ tabRep_tgT 4)

end CFSG.ComponentClassification.GrSLit.L34Facts
