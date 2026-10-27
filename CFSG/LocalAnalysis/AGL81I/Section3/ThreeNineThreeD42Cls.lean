module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeD42ConjData

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.D42Over

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin

@[expose] def kA : trialityGroup8 := ⟨wordGL kAW, wordGL_mem kAW⟩

@[expose] def kB : trialityGroup8 := ⟨wordGL kBW, wordGL_mem kBW⟩

@[expose] def OvergroupConj (k : trialityGroup8) : Prop :=
  ∀ H : Subgroup trialityGroup8, Subgroup.centralizer {k} ≤ H →
    (∀ h ∈ H, h * k * h⁻¹ = k ∨ h * k * h⁻¹ = k * k) ∨ H = ⊤

structure D42ClsFacts : Prop where
  index_kA : (Subgroup.centralizer {kA}).index = 139776
  index_kB : (Subgroup.centralizer {kB}).index = 326144
  overgroup_kA : OvergroupConj kA
  overgroup_kB : OvergroupConj kB

end CFSG.LocalAnalysis.AGL81I.Section3.D42Over

end
