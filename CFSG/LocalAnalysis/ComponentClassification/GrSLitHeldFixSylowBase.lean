
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixPermTools
public import CFSG.Sporadic.HeldB.InnerRestrict
public import CFSG.Sporadic.HeldB.OuterCentRestrict
public import CFSG.Sporadic.HeldB.AutModelCore
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterCentAux
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowData
public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Th.F2Spec

@[expose] public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier

def hfX : Equiv.Perm (Fin 8330) := evalSignedWord heOuterLetters hfXWord

theorem hfAUArrs_eq : hfAUArrs = heLetterArrs := rfl

theorem hfX_mem : hfX ∈ heAutGroup := by
  rw [hfX]
  refine evalSignedWord_mem heAutGroup (fun g hg => ?_) _
  simp only [heOuterLetters, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
  · exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
  · exact heAutU_mem_heAutGroup

def hfTau (i : ℕ) : Equiv.Perm (Fin 8330) := ((hfTauWords.getD i []).map heInnerCP1).prod

def hfTL (j : ℕ) : Equiv.Perm (Fin 8330) := if j = 0 then heT1P else hfTau (j - 1)

def hfYL (j : ℕ) : Equiv.Perm (Fin 8330) := if j < 9 then heInnerCP1 j else hfX

def hfY : Equiv.Perm (Fin 8330) := (hfYWord.map hfYL).prod

def hfT0L (j : ℕ) : Equiv.Perm (Fin 8330) := if j < 5 then hfTL j else hfY

theorem hfTTabs_size : hfTTabs.size = 5 := by simp [hfTTabs]

theorem hfT0Tabs_size : hfT0Tabs.size = 6 := by simp [hfT0Tabs]

def hfT : Subgroup (Equiv.Perm (Fin 8330)) := genGroup 8330 hfTTabs hfTL

def hfT0 : Subgroup (Equiv.Perm (Fin 8330)) := genGroup 8330 hfT0Tabs hfT0L

theorem heInnerCP1_mem_grp1 {j : ℕ} (hj : j < 9) : heInnerCP1 j ∈ heInnerGrp1 :=
  subset_closure ⟨j, hj, rfl⟩

theorem hfT_le_hfT0 : hfT ≤ hfT0 := by
  rw [hfT, genGroup, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj5 : j < 5 := hfTTabs_size ▸ hj
  refine subset_closure ⟨j, by rw [hfT0Tabs_size]; omega, ?_⟩
  simp [hfT0L, hj5]

theorem hfY_mem : hfY ∈ heAutGroup := by
  refine heAutGroup.list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  simp only [hfYL]
  split_ifs
  · exact heP_le_heAutGroup (heInnerCP1_mem j)
  · exact hfX_mem

theorem hfY_mem_hfT0 : hfY ∈ hfT0 :=
  subset_closure ⟨5, by rw [hfT0Tabs_size]; norm_num, by simp [hfT0L]⟩

end CFSG.ComponentClassification.GrSLit.HeldFix
