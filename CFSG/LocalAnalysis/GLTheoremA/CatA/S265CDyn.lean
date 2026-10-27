module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CFam

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def IsELabel (lab : GLALabel) : Prop :=
  lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6

@[expose] def DynCThreeS (P : GLALabel → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (labL : GLALabel) (β : MulAut S),
    Subgroup.center S = ⊥ → Y10GField.InnDiagKind S labL β → β ^ 3 = 1 → β ≠ 1 → P labL →
    ∀ J : Subgroup S, IsComponentOf J (fixSubgroup β) →
      ¬ catalogIs (↥J ⧸ Subgroup.center ↥J) S9.isF4two ∧
      ¬ catalogIs (↥J ⧸ Subgroup.center ↥J) isTitsIdx ∧
      (catalogIs (↥J ⧸ Subgroup.center ↥J) S9.isTE6two →
        catalogIs S (fun i => isE7TwoIdx i ∨ isE8TwoIdx i)) ∧
      (catalogIs (↥J ⧸ Subgroup.center ↥J) S9.isTD4two → catalogIs S S9.isTE6two)

theorem dynCThreeS_of_split (hE : DynCThreeS IsELabel)
    (hO : DynCThreeS fun lab => ¬ IsELabel lab) : DynCThreeS fun _ => True := by
  intro S _ _ labL β hcen hin hβ3 hβ1 _ J hJ
  by_cases h : IsELabel labL
  · exact hE S labL β hcen hin hβ3 hβ1 h J hJ
  · exact hO S labL β hcen hin hβ3 hβ1 h J hJ

section Assembly

theorem dynkinItemCThree_of_s (h : DynCThreeS fun _ => True) : DynkinItemCThree := by
  intro Γ _ _ L K A y hlie hAel _ hInn hyA hyC hK
  obtain ⟨labL, β, J, -, hcen, hin, hβp, hβ1, hJ, ⟨e⟩⟩ :=
    I141F.exists_sLevel_of_i141 Nat.prime_three (by norm_num) hlie hAel hInn hyA hyC hK
  obtain ⟨h1, h2, h3, h4⟩ := h _ labL β hcen hin hβp hβ1 trivial J hJ
  have tr : ∀ {Q : TauCeti.CFSGIndex → Prop}, catalogIs (PSimple 3 K) Q →
      catalogIs (↥J ⧸ Subgroup.center ↥J) Q :=
    fun ⟨i, hi, ⟨f⟩⟩ => ⟨i, hi, ⟨e.symm.trans f⟩⟩
  exact ⟨fun hc => h1 (tr hc), fun hc => h2 (tr hc), fun hc => h3 (tr hc), fun hc => h4 (tr hc)⟩

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.S265C
