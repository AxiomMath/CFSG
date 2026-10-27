module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.J1Rows
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23J1

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed

variable {Y : Type} [Group Y] {τ : Y}

theorem z2a5_not_J1
    [Finite Y] (h : Z2A5Hyp Y τ) {S : Subgroup Y}
    (hS : FixedData Y S) : ¬ NativeSporadic.IsSporadic ↥S .J1 := by
  rintro ⟨eS⟩
  haveI := hS.normal
  have htop : S = ⊤ := CFSG.EvenSporadicStandard.HSStd.InvCent.Harada.eq_top_of_J1 hS.cent eS
  have eG : Y ≃* NativeSporadic.Carrier .J1 :=
    ((Subgroup.topEquiv (G := Y)).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans eS
  have hcY : CFSG.ComponentClassification.GSThmB.CF23I.OneClass Y :=
    CFSG.ComponentClassification.GSThmB.CF23I.OneClass.of_mulEquiv eG
      CFSG.ComponentClassification.GSThmB.CF23I.oneClass_j1
  obtain ⟨x, hxX, hx2⟩ := z2a5_exists_inv h
  have hXle : oTwoRes (centralizer ({τ} : Set Y)) ≤ centralizer ({τ} : Set Y) :=
    (Subgroup.closure_le _).2 fun _ hx => hx.1
  obtain ⟨g, hg⟩ := hcY x τ hx2 h.1
  have hconj : x ∈ conjClassIn (⊤ : Subgroup Y) τ :=
    ⟨g, Subgroup.mem_top g, by rw [← hg]; group⟩
  obtain ⟨x', hx'X, hx'eq, -⟩ := (h.2.2 x).1 ⟨hconj, hXle hxX⟩
  apply z2a5_tau_not_mem h
  have hx'inv : x'⁻¹ ∈ oTwoRes (centralizer ({τ} : Set Y)) :=
    (oTwoRes (centralizer ({τ} : Set Y))).inv_mem hx'X
  have hmem : τ = x * x'⁻¹ := by rw [hx'eq]; group
  exact hmem ▸ (oTwoRes (centralizer ({τ} : Set Y))).mul_mem hxX hx'inv

end CFSG.OddStandard.SmallF3.Omega
