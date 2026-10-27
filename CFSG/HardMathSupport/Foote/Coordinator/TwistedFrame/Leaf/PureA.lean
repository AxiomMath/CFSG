module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Basic
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Coords
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PureAAux2
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.RootTuples

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false


namespace TwPureAAux

open PureAAux

theorem dichData_of_parts (τ : Tag)
    (h1 : ∀ β ∈ rootFinset τ, (β (iθ τ) = 0 ∨ β (iθ τ) = 1) →
      highRoot τ ≠ β ∧ highRoot τ ≠ -β ∧
        ∀ q ∈ commCandidates, q.1 • highRoot τ + q.2 • β ∉ rootFinset τ)
    (h2 : ∀ β ∈ rootFinset τ, iform β β = iform (highRoot τ) (highRoot τ) → β (iθ τ) = -1 →
      highRoot τ ≠ β ∧ highRoot τ ≠ -β ∧
        (∀ q ∈ commCandidates, q ≠ (1, 1) → q.1 • highRoot τ + q.2 • β ∉ rootFinset τ) ∧
        highRoot τ + β ∈ rootFinset τ) : DichData τ := by
  refine ⟨h1, h2, ?_, ?_, ?_, CoordAux.highRoot_degree τ⟩
  · intro β hβ
    have hneg : IsRoot τ (-β) := IsRoot.neg (mem_rootFinset.1 hβ)
    have h := CoordAux.degree_le_two hneg
    have h' := CoordAux.degree_le_two (mem_rootFinset.1 hβ)
    simp only [Pi.neg_apply] at h
    omega
  · intro β hβ h2
    exact CoordAux.eq_highRoot_of_two_le (mem_rootFinset.1 hβ) (by omega)
  · intro β hβ h2
    have hneg : IsRoot τ (-β) := IsRoot.neg (mem_rootFinset.1 hβ)
    have : -β = highRoot τ := CoordAux.eq_highRoot_of_two_le hneg (by simp [h2])
    rw [← this]
    simp

theorem f4_part1 : ∀ β ∈ rootFinset Tag.F4, (β (iθ Tag.F4) = 0 ∨ β (iθ Tag.F4) = 1) →
    highRoot Tag.F4 ≠ β ∧ highRoot Tag.F4 ≠ -β ∧
      ∀ q ∈ commCandidates, q.1 • highRoot Tag.F4 + q.2 • β ∉ rootFinset Tag.F4 := by
  decide +kernel

theorem f4_part2 : ∀ β ∈ rootFinset Tag.F4,
    iform β β = iform (highRoot Tag.F4) (highRoot Tag.F4) → β (iθ Tag.F4) = -1 →
    highRoot Tag.F4 ≠ β ∧ highRoot Tag.F4 ≠ -β ∧
      (∀ q ∈ commCandidates, q ≠ (1, 1) → q.1 • highRoot Tag.F4 + q.2 • β ∉ rootFinset Tag.F4) ∧
      highRoot Tag.F4 + β ∈ rootFinset Tag.F4 := by
  decide +kernel

theorem e6_part1 : ∀ β ∈ rootFinset Tag.E6, (β (iθ Tag.E6) = 0 ∨ β (iθ Tag.E6) = 1) →
    highRoot Tag.E6 ≠ β ∧ highRoot Tag.E6 ≠ -β ∧
      ∀ q ∈ commCandidates, q.1 • highRoot Tag.E6 + q.2 • β ∉ rootFinset Tag.E6 := by
  decide +kernel

theorem e6_part2 : ∀ β ∈ rootFinset Tag.E6,
    iform β β = iform (highRoot Tag.E6) (highRoot Tag.E6) → β (iθ Tag.E6) = -1 →
    highRoot Tag.E6 ≠ β ∧ highRoot Tag.E6 ≠ -β ∧
      (∀ q ∈ commCandidates, q ≠ (1, 1) → q.1 • highRoot Tag.E6 + q.2 • β ∉ rootFinset Tag.E6) ∧
      highRoot Tag.E6 + β ∈ rootFinset Tag.E6 := by
  decide +kernel

theorem e8_part1 : ∀ β ∈ rootFinset Tag.E8, (β (iθ Tag.E8) = 0 ∨ β (iθ Tag.E8) = 1) →
    highRoot Tag.E8 ≠ β ∧ highRoot Tag.E8 ≠ -β ∧
      ∀ q ∈ commCandidates, q.1 • highRoot Tag.E8 + q.2 • β ∉ rootFinset Tag.E8 := by
  rw [DetectE8.rootFinset_E8_eq]
  decide +kernel

theorem e8_part2 : ∀ β ∈ rootFinset Tag.E8,
    iform β β = iform (highRoot Tag.E8) (highRoot Tag.E8) → β (iθ Tag.E8) = -1 →
    highRoot Tag.E8 ≠ β ∧ highRoot Tag.E8 ≠ -β ∧
      (∀ q ∈ commCandidates, q ≠ (1, 1) → q.1 • highRoot Tag.E8 + q.2 • β ∉ rootFinset Tag.E8) ∧
      highRoot Tag.E8 + β ∈ rootFinset Tag.E8 := by
  rw [DetectE8.rootFinset_E8_eq]
  decide +kernel

theorem dichData_F4 : DichData Tag.F4 := dichData_of_parts Tag.F4 f4_part1 f4_part2

theorem dichData_E6 : DichData Tag.E6 := dichData_of_parts Tag.E6 e6_part1 e6_part2

theorem dichData_E8 : DichData Tag.E8 := dichData_of_parts Tag.E8 e8_part1 e8_part2

theorem dichData (c : TwClass) : DichData c.tag := by
  cases c
  · exact dichData_F4
  · exact dichData_E6
  · exact dichData_E8
  · exact dichData_E8

theorem twPure_of_dich (c : TwClass) (hdat : DichData c.tag) (K : Type) [Field K] [Finite K]
    (hK : c.minQ ≤ Nat.card K) (D : LangLevi c.tag K c.w) : TwPure (c.X₁ D) (c.X₂ D) := by
  intro g hg hC
  have hcomm := TwBasicAux.frame_commute c D
  have hU₁ : Uθ c.tag K ≤ c.X₁ D :=
    TwBasicAux.rootSubgroup_le_frame D (TwBasicAux.highRoot_mem_S₁ c)
      (Pθ_le_normalizer_Uθ _ D.L (parabolicLevi_le_parabolicSubgroup _ D.g_mem))
  have hV₁ : Heis.Uneg c.tag K ≤ c.X₁ D :=
    TwBasicAux.rootSubgroup_le_frame D (TwBasicAux.neg_highRoot_mem_S₁ c)
      (Lθ_le_normalizer_Uneg _ D.L D.g_mem)
  have hco := twCoords c K hK D
  have hZ : ∀ d ∈ (c.X₁ D ⊔ c.X₂ D) ⊓ Qθ c.tag K,
      (∀ r ∈ (c.X₁ D ⊔ c.X₂ D) ⊓ Qθ c.tag K, r * d = d * r) → d ∈ Uθ c.tag K := by
    intro d hd hcen
    have hs := heisCoord_spec c.tag K
    have h1 : heisCoord c.tag K d ∈ VS (c.X₁ D ⊔ c.X₂ D) :=
      Submodule.subset_span ⟨d, hd, rfl⟩
    have h2 : heisCoord c.tag K d ∈ VM (c.X₁ D ⊔ c.X₂ D) :=
      Submodule.subset_span ⟨d, ⟨hd.2, Subgroup.mem_centralizer_iff.2 hcen⟩, rfl⟩
    have h0 : heisCoord c.tag K d ∈ VS (c.X₁ D ⊔ c.X₂ D) ⊓ VM (c.X₁ D ⊔ c.X₂ D) := ⟨h1, h2⟩
    rw [hco.inf_eq_bot] at h0
    exact (hs.eq_zero_iff d hd.2).1 ((Submodule.mem_bot K).1 h0)
  exact pure_of_center_sup hdat hcomm hU₁ hV₁ hZ hg hC

end TwPureAAux

theorem twPure_A (c : TwClass) (hc : c ≠ TwClass.e8Twelve) (K : Type) [Field K] [Finite K]
    (hK : c.minQ ≤ Nat.card K) (D : LangLevi c.tag K c.w) : TwPure (c.X₁ D) (c.X₂ D) :=
  TwPureAAux.twPure_of_dich c (TwPureAAux.dichData c) K hK D

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
