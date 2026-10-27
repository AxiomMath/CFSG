module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2PermSound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzTitsThree
public import Certificates.Certificate19750
public import Certificates.Data.CoreD2Tits
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding.CoreD2 Certificates.CoreD2Perm CFSG.Sporadic.Schreier.Tits
open CFSG.ComponentClassification.PSL3Four

theorem tits_core_generation : CoreGenerationOf ↥titsD 3 :=
  Certificates.certificate19750

theorem tits_core_arr_size (j : ℕ) : (titsDArr j).size = 1755 := by
  unfold titsDArr CFSG.Sporadic.Schreier.Tits.commArr
  unfold CFSG.Monster.B.Co2.Native.compA
  exact Array.size_ofFn

theorem tits_core_tab_a : TabRep titsData.aT (titsDGen 0) := by
  have h : titsData.aT = titsDArr 0 := by simp only [titsData]
  rw [h]
  exact ⟨tits_core_arr_size 0, fun i => titsDArr_rep (j := 0) (by norm_num) i⟩

theorem tits_core_tab_b : TabRep titsData.bT (titsDGen 1) := by
  have h : titsData.bT = titsDArr 1 := by simp only [titsData]
  rw [h]
  exact ⟨tits_core_arr_size 1, fun i => titsDArr_rep (j := 1) (by norm_num) i⟩

theorem titsD_eq_closure_pair :
    titsD = Subgroup.closure ({titsDGen 0, titsDGen 1} : Set (Equiv.Perm (Fin 1755))) := by
  unfold titsD
  congr 1
  ext x
  simp [Fin.exists_fin_two, eq_comm]

theorem coreGenerationOf_tits : CoreGenerationOf ↥titsD 3 :=
  tits_core_generation


theorem kFactTitsThreeCore : KFactTitsThreeCore := by
  intro L _ _ d hd ⟨e⟩ S
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  obtain ⟨eS⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv L 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  exact glbCore_two_eq_top_of_coreGenerationOf
    (coreGenerationOf_of_mulEquiv Nat.prime_three eS.symm coreGenerationOf_tits) S

end CFSG.AGLEmbeddingD2
