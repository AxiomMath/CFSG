module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamiliesAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.AGLEmbedding

variable {Y : Type} [Group Y] [Finite Y] {Rb : Sylow 3 Y} {Y₀ : Subgroup Y} {K : Subgroup Y}

theorem isPGroup_centralizer_of_cover_three (h : ReducedNongeneration 3 Y Rb Y₀) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype) :
    IsPGroup 3 (Subgroup.centralizer (K : Set Y)) := by
  have : Fact (Nat.Prime 3) := ⟨h.prime⟩
  refine isPGroup_centralizer_of_forall_mem h.prime h.ne_two h.core_eq_bot hKn fun c hc hcp => ?_
  refine mem_of_mem_centralizer_of_orderOf_eq Rb hKn (fun c' hc' hc'p => ?_) hc hcp
  obtain ⟨z, -, rfl⟩ := hcent c' hc' hc'p
  exact z.2

theorem centralizer_le_sylow_of_cover_three (h : ReducedNongeneration 3 Y Rb Y₀) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype) :
    Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨h.prime⟩
  have : K.Normal := hKn
  exact (isPGroup_centralizer_of_cover_three h hKn hcent).le_sylow_of_normal Rb

theorem sup_centralizer_le_normalCore (h : ReducedNongeneration 3 Y Rb Y₀) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype) :
    K ⊔ Subgroup.centralizer (K : Set Y) ≤ (K ⊔ (Rb : Subgroup Y)).normalCore := by
  have : K.Normal := hKn
  have : (K ⊔ Subgroup.centralizer (K : Set Y)).Normal := inferInstance
  exact Subgroup.normal_le_normalCore.2
    (sup_le_sup_left (centralizer_le_sylow_of_cover_three h hKn hcent) K)

theorem not_le_sup_centralizer_of_no_inner (h : ReducedNongeneration 3 Y Rb Y₀) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype)
    (hno : ¬ ∃ E : Subgroup Y, E ≤ (Rb : Subgroup Y) ∧
      E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
      E ≤ K ⊔ Subgroup.centralizer (K : Set Y))
    {E : Subgroup Y} (hER : E ≤ (Rb : Subgroup Y)) (hEa : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) : ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y) := fun hEKC =>
  hno ⟨E, hER, hEKC.trans (sup_centralizer_le_normalCore h hKn hcent), hEa, hEc, hEKC⟩

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
