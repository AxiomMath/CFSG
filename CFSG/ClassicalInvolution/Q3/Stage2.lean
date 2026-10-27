module

public import CFSG.ClassicalInvolution.Q3.Closure
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def frameFamily3 (Ω : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ L ≤ Subgroup.centralizer (A : Set G) ∧ ∃ z ∈ A, IsClassicalMember3 L z}

theorem memberFamily3_of_exactTriple {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω)
    (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃) : MemberFamily3 Ω T.group (frameFamily3 Ω T.group) := by
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₂A : z₂ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₃A : z₃ ∈ T.group := Subgroup.subset_closure (by simp)
  refine
    { elem := T.isElemAbelian
      card := T.card_eq_eight hind
      subset := fun L hL => hL.1
      nonempty := ⟨K₁, hΩ₁, T.le_centralizer₁, z₁, hz₁A, hz₁⟩
      involution := fun L hL => by
        obtain ⟨-, hLA, z', hz'A, hz'⟩ := hL
        exact ⟨z', hz'A, hz', hLA⟩
      generate := ?_ }
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Subgroup.subset_closure ⟨K₁, ⟨hΩ₁, T.le_centralizer₁, z, hz₁A, hz₁⟩, hz₁⟩
    · exact Subgroup.subset_closure ⟨K₂, ⟨hΩ₂, T.le_centralizer₂, z, hz₂A, hz₂⟩, hz₂⟩
    · exact Subgroup.subset_closure ⟨K₃, ⟨hΩ₃, T.le_centralizer₃, z, hz₃A, hz₃⟩, hz₃⟩
  · rw [Subgroup.closure_le]
    rintro w ⟨L, ⟨-, -, z', hz'A, hz'⟩, hw⟩
    rw [involution_unique3 hw hz']
    exact hz'A

theorem stage2_of_exactTriple3_of_model (h0 : ModelClauseZero) (hM : M11Facts)
    (hKG1 : LieLocallyTwoBalanced3) (hM11 : M11LocallyTwoBalanced)
    (hOG : CFSG.Open.componentClassificationOddCore G = ⊥) (hΩ : InClass3 Ω)
    (hIH : LocalLieSystems3 Ω) (hO : LocalOddCentralizer3 Ω) {K₁ K₂ K₃ : Subgroup G}
    {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω)
    (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember3 K₁ z₁)
    (hz₂ : IsClassicalMember3 K₂ z₂) (hz₃ : IsClassicalMember3 K₃ z₃)
    (hnc : ∀ b ∈ T.group, b ≠ 1 → b ∉ Subgroup.center G)
    (hMF1 : ∀ a ∈ T.group, a ≠ 1 → ∀ (ι : Type)
      (D : LieSystemData3 ι (LocalQuot Ω a) (localFamily Ω a)), SingleClassComponents3 D)
    (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ T.group, IsFrameInvolution3 (frameFamily3 Ω T.group) a →
      CentralizerGenerationModOTwo Ω T.group a)
    (hcover : ∀ a ∈ T.group, IsFrameInvolution3 (frameFamily3 Ω T.group) a →
      LieCovers3 Ω (frameFamily3 Ω T.group) a) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.group, deltaCore F = ⊥) ∧ StronglyBalanced T.group ∧
      classicalInvolutionOddCore ↥K₁ = ⊥ ∧ classicalInvolutionOddCore ↥K₂ = ⊥ ∧
      classicalInvolutionOddCore ↥K₃ = ⊥ := by
  have hM' := memberFamily3_of_exactTriple T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃
  have hL : LocalHypotheses3 Ω T.group :=
    { inClass := hΩ
      noncentral := hnc
      lie := hIH
      single := hMF1 }
  have hlink : ∀ a ∈ T.group, IsFrameInvolution3 (frameFamily3 Ω T.group) a →
      InvolutionLink3 Ω T.group (frameFamily3 Ω T.group) a := by
    intro a ha hfa
    obtain ⟨K, hK, hKz⟩ := hfa
    exact involutionLink_of_lieCovers3 hL ha hKz.ne_one hM'.subset
      (fun L hL => by
        obtain ⟨z, hzA, hz, -⟩ := hM'.involution L hL
        exact ⟨z, hzA, hz⟩)
      (hcover a ha ⟨K, hK, hKz⟩)
  have hgen := generation_of_memberFamily3 hΩ hM' hconn hgenModO hlink
  exact stage2_of_exactTriple3_of_balance hOG hΩ.conjInvariant hIH hO T hind hΩ₁ hΩ₂ hΩ₃ hz₁
    hz₂ hz₃ hnc
    (fun a ha ha1 => componentBalanceAt_of_localLieSystems3 h0 hM hKG1 hM11 hΩ hIH
      (fun h => hnc a ha ha1 (h rfl)))
    hgen

theorem localOddCentral3_of_exactTriple_of_model (h0 : ModelClauseZero) (hM : M11Facts)
    (hKG1 : LieLocallyTwoBalanced3) (hM11 : M11LocallyTwoBalanced)
    (hOG : CFSG.Open.componentClassificationOddCore G = ⊥) (hΩ : InClass3 Ω)
    (hIH : LocalLieSystems3 Ω) (hO : LocalOddCentralizer3 Ω) {K₁ K₂ K₃ : Subgroup G}
    {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω)
    (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember3 K₁ z₁)
    (hz₂ : IsClassicalMember3 K₂ z₂) (hz₃ : IsClassicalMember3 K₃ z₃)
    (hnc : ∀ b ∈ T.group, b ≠ 1 → b ∉ Subgroup.center G)
    (hMF1 : ∀ a ∈ T.group, a ≠ 1 → ∀ (ι : Type)
      (D : LieSystemData3 ι (LocalQuot Ω a) (localFamily Ω a)), SingleClassComponents3 D)
    (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ T.group, IsFrameInvolution3 (frameFamily3 Ω T.group) a →
      CentralizerGenerationModOTwo Ω T.group a)
    (hcover : ∀ a ∈ T.group, IsFrameInvolution3 (frameFamily3 Ω T.group) a →
      LieCovers3 Ω (frameFamily3 Ω T.group) a)
    {x : G} (hx : x ∈ T.group) (hx1 : x ≠ 1)
    (hcov : ∀ L ∈ Ω, L ≤ Subgroup.centralizer ({x} : Set G) →
      ∃ F ∈ signalizerFunctorEk 2 2 T.group, x ∈ F ∧ L ≤ Subgroup.centralizer (F : Set G)) :
    LocalOddCentral Ω {x} := by
  have hM' := memberFamily3_of_exactTriple T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃
  have hL : LocalHypotheses3 Ω T.group :=
    { inClass := hΩ
      noncentral := hnc
      lie := hIH
      single := hMF1 }
  have hlink : ∀ a ∈ T.group, IsFrameInvolution3 (frameFamily3 Ω T.group) a →
      InvolutionLink3 Ω T.group (frameFamily3 Ω T.group) a := by
    intro a ha hfa
    obtain ⟨K, hK, hKz⟩ := hfa
    exact involutionLink_of_lieCovers3 hL ha hKz.ne_one hM'.subset
      (fun L hL => by
        obtain ⟨z, hzA, hz, -⟩ := hM'.involution L hL
        exact ⟨z, hzA, hz⟩)
      (hcover a ha ⟨K, hK, hKz⟩)
  exact localOddCentral3_of_exactTriple_of_balance hOG hΩ.conjInvariant hIH hO T hind hΩ₁ hΩ₂ hΩ₃
    hz₁ hz₂ hz₃ hnc
    (fun a ha ha1 => componentBalanceAt_of_localLieSystems3 h0 hM hKG1 hM11 hΩ hIH
      (fun h => hnc a ha ha1 (h rfl)))
    (generation_of_memberFamily3 hΩ hM' hconn hgenModO hlink) hx hx1 hcov

end CFSG.ClassicalInvolution.Q3
