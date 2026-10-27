module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRCert
public import Certificates.Certificate22970
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4TShape

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem exists_of_mem_zT0Tabs {ET : Array Tab} (hET : Enumerates T0 ET.toList) {zt : Tab}
    (hz : zt ∈ (zT0Tabs ET).toList) :
    ∃ z ∈ T0, TabRep zt z ∧ ∀ t ∈ T0, z * t = t * z := by
  simp only [zT0Tabs, Array.toList_filter, List.mem_filter] at hz
  obtain ⟨hzET, hzc⟩ := hz
  obtain ⟨z, hzT, hrep⟩ := hET.sound zt hzET
  refine ⟨z, hzT, hrep, fun t ht => ?_⟩
  have hle : T0 ≤ centralizer ({z} : Set (Equiv.Perm (Fin 42))) := by
    show closure (wordSet wT₀) ≤ _
    rw [closure_le]
    intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_wordSet_iff.mp hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rw [allBelow_eq_true] at hzc
    have hj' : j < (wordTabs wT₀).size := by rw [size_wordTabs]; exact hj
    have h := (commT_iff hrep (tabRep_wordTabs wT₀ hj)).1 (hzc j hj')
    rw [getElem!_pos wT₀ j hj]
    exact h.symm
  exact (mem_centralizer_singleton_iff.mp (hle ht)).symm

theorem exists_pos_r2Tabs {ER ES ZT : Array Tab} (hER : Enumerates R ER.toList)
    (hES : Enumerates S ES.toList)
    (hZT : ∀ zt ∈ ZT.toList, ∃ z ∈ T0, TabRep zt z ∧ ∀ t ∈ T0, z * t = t * z)
    {y : Equiv.Perm (Fin 42)} (hyR : y ∈ R) (hy4 : y ^ 4 = 1) (hyS : y ∉ S)
    (hyZ : ∀ z ∈ T0, (∀ t ∈ T0, z * t = t * z) → y * z = z * y) :
    ∃ i < (r2Tabs ER ES ZT).size, TabRep (r2Tabs ER ES ZT)[i]! y := by
  obtain ⟨k, hk, hrep⟩ := hER.exists_pos hyR
  have hmem : ER[k]! ∈ (r2Tabs ER ES ZT).toList := by
    simp only [r2Tabs, Array.toList_filter, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨getElem!_mem hk, ⟨?_, ?_⟩, ?_⟩
    · exact ((tabRep_powTab hrep 4).beq_iff TabRep.idTab).2 hy4
    · rw [allBelow_eq_true]
      intro i hi
      obtain ⟨z, hzT, hzrep, hzc⟩ := hZT _ (getElem!_mem hi)
      exact (commT_iff hrep hzrep).2 (hyZ z hzT hzc)
    · cases hf : found (indexOf ES) ES ER[k]!
      · rfl
      · exact absurd (mem_of_found_enum hES hrep hf) hyS
  obtain ⟨i, hi, he⟩ := exists_getElem!_of_mem hmem
  exact ⟨i, hi, he ▸ hrep⟩

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts GrS4

theorem l34GraphCosetIndexFact :
    L34GraphCosetIndexFact := by
  intro y hyR y' hy'R _ _ hZc hy4 hy'4 hd4 hyS hy'S
  have h := Certificates.certificate22970
  unfold graphIdxOK at h
  set ER := enumBFS 42 gTabs 241920 with hER
  set ES := enumBFS 42 gensS 20160 with hES
  set ET := enumBFS 42 (wordTabs wT₀) 64 with hET
  have hZT := fun zt hzt => exists_of_mem_zT0Tabs (ET := ET.tabs) enumerates_T0 (zt := zt) hzt
  obtain ⟨i, hi, hirep⟩ := exists_pos_r2Tabs (ER := ER.tabs) enumerates_R enumerates_S hZT hyR
    hy4 hyS fun z hz hzc => (hZc z hz hzc).1
  obtain ⟨j, hj, hjrep⟩ := exists_pos_r2Tabs (ER := ER.tabs) enumerates_R enumerates_S hZT hy'R
    hy'4 hy'S fun z hz hzc => (hZc z hz hzc).2
  simp only [r2PairsOK, allBelow_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨hinv, h2⟩ := h i hi j hj
  have hirep' := tabRep_invTab_of_invOK hinv hjrep
  have hd := hirep.comp hirep'
  rcases h2 with h2 | h2
  · exact absurd (((tabRep_powTab hd 4).beq_iff TabRep.idTab).2 hd4) (by rw [h2]; decide)
  · exact mem_of_found_enum enumerates_S hd h2

theorem l34EndTShapeStep_of_covers
    (hExp : L34BFixExponentFact)
    (hSq : L34BFixOuterSquareFact) : L34EndTShapeStep :=
  l34EndTShapeStep_of_facts hExp hSq l34GraphCosetIndexFact

end CFSG.ComponentClassification.GrSLit
