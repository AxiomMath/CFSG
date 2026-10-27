module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma38_of_37F (h37F : Asc82Lemma37F) (hd : Asc82Omega8MinusData) :
    Asc82Lemma38 := by
  intro G _ _ t L hS hLie
  obtain ⟨z, hz, J, hJ, hJF⟩ := hd G L hS.inF hLie
  obtain ⟨K, hzK⟩ := hz.2
  obtain ⟨hzKmem, hKle, -⟩ := hzK
  have hzL : z ∈ L := (hKle hzKmem).1
  have hzt : z ∈ centralizer ({t} : Set G) := hS.component.le hzL
  exact (h37F G t L hS z 1 hz (by simpa using hzt) J) ⟨by simpa using hJ, hJF⟩

end CFSG.OddStandard.SmallF3.Omega
