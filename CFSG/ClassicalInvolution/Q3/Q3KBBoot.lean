module

public import CFSG.ClassicalInvolution.Q3.Q3KBTriple
public import CFSG.ClassicalInvolution.Q3.Q3NGGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NG


section Stage2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem stage2_of_classTriple3_gen' (hG : TripleGeneration3) {K : Subgroup G} {z : G}
    (hS : BootTripleSetting3 K z) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.exact.group, deltaCore F = ⊥) ∧
      StronglyBalanced T.exact.group ∧ classicalInvolutionOddCore ↥K₁ = ⊥ ∧
      classicalInvolutionOddCore ↥K₂ = ⊥ ∧ classicalInvolutionOddCore ↥K₃ = ⊥ := by
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hS.member
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hS.below
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hIH
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hS.nonabelian hb1 (Set.singleton_subset_iff.mpr hbc)
  have h2 : TwoBalancedWrt T.exact.group :=
    twoBalancedWrt_of_quotient_deltaCore_eq_bot T.exact.isElemAbelian.1 fun a ha ha1 F hF =>
      deltaCore_modOdd_eq_bot_of_exactTriple hΩ hIH T.exact T.ind T.mem₁ T.mem₂ T.mem₃ ha ha1
        (hnc a ha1) hF
  exact stage2_of_exactTriple3
    (componentClassificationOddCore_eq_bot_of_simple hS.nonabelian) hΩ.conjInvariant hIH hO
    T.exact T.ind T.mem₁ T.mem₂ T.mem₃ T.cls₁ T.cls₂ T.cls₃ (fun b _ hb1 => hnc b hb1) h2
    (hG G K z hS K₁ K₂ K₃ z₁ z₂ z₃ T)

end Stage2

theorem bootTriple3_of_gen' (hG : TripleGeneration3) (hP1 : P1Cover3) : BootTriple3 := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hT
  have hS : BootTripleSetting3 K z := ⟨hnab, hz, hBelow, h3, h4, hΔ, hT⟩
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hIH
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hnab hb1 (Set.singleton_subset_iff.mpr hbc)
  obtain ⟨K₁, K₂, K₃, z₁, z₂, z₃, hE, hind, ⟨h₁, hz₁⟩, ⟨h₂, hz₂⟩, ⟨h₃, hz₃⟩⟩ :=
    hT.exists_exactTriple
  have T₀ : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃ := ⟨hE, hind, h₁, h₂, h₃, hz₁, hz₂, hz₃⟩
  obtain ⟨-, -, hex₁, -, -⟩ := stage2_of_classTriple3_gen' hG hS T₀
  obtain ⟨b, hb⟩ := h₁
  have hexact : ExactMembers3 (conjClass3 K) := by
    refine exactMembers3_of_conjugates hex₁ fun L hL => ?_
    obtain ⟨a, rfl⟩ := hL
    refine ⟨a * b⁻¹, ?_⟩
    show conjSub a K = conjSub (a * b⁻¹) K₁
    rw [← hb, ← conjSub_mul]
    simp
  refine ⟨hexact, localOddCentral3_of_members_centralize hΩ.conjInvariant fun L hLΩ hLz => ?_⟩
  obtain ⟨M₁, M₂, M₃, w₁, w₂, w₃, T, hzT, F, hF, hzF, hLF⟩ := hP1 G K z hS L hLΩ hLz
  obtain ⟨hΔT, hSB, -⟩ := stage2_of_classTriple3_gen' hG hS T
  exact le_centralizer_involutionOddCore_of_covered hΩ.conjInvariant hO T.exact.isElemAbelian
    (fun c hc _ => group_le_centralizingLayer_of_exactTriple T.exact T.mem₁ T.mem₂ T.mem₃ hc)
    (fun c _ hc1 => hnc c hc1) hSB hΔT hzT hz.ne_one hLΩ hLz hF hzF hLF

theorem bootTriple3_of' (hMF1 : SingleClassComponents3At) (hgen : CentralizerGenerationModOTwoAt)
    (hcov : LieCovers3At) (hP1 : P1Cover3) : BootTriple3 :=
  bootTriple3_of_gen' (tripleGeneration3_of hMF1 hgen hcov) hP1

end CFSG.ClassicalInvolution.Q3.Q3KB
