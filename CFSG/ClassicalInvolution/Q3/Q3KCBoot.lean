module

public import CFSG.ClassicalInvolution.Q3.Q3KCGen
public import CFSG.ClassicalInvolution.Q3.Q3KCLink
public import CFSG.ClassicalInvolution.Q3.Q3KBBoot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KC

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NG


theorem rankTwoSpan_eq_top_of_covers {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hIH : LocalLieSystems3 Ω) (hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G)
    (hconn : OmegaConnected Ω) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω)
    (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃)
    (hcov : ∀ a ∈ T.group, IsFrameInvolution3 (frameFamily3 Ω T.group) a →
      LieCovers3 Ω (frameFamily3 Ω T.group) a) :
    (⨆ F ∈ signalizerFunctorEk 2 2 T.group, Subgroup.centralizer (F : Set G)) = ⊤ := by
  have hM' := memberFamily3_of_exactTriple T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃
  refine generation_of_memberFamily3 hΩ hM' hconn
    (fun a ha hfa => ?_) fun a ha hfa => ?_
  · obtain ⟨L, -, hLa⟩ := hfa
    exact centralizerGenerationModOTwo_of_exactTriple hIH T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ ha
      hLa.ne_one (hnc a hLa.ne_one)
  · obtain ⟨L, hL', hLa⟩ := hfa
    exact involutionLink_of_lieCovers3' hΩ hIH (hnc a hLa.ne_one) hM'.subset
      (fun M hM => by
        obtain ⟨w, hwA, hw, -⟩ := hM'.involution M hM
        exact ⟨w, hwA, hw⟩)
      (hcov a ha ⟨L, hL', hLa⟩)

theorem tripleGeneration3_of' (hcov : LieCovers3At) : TripleGeneration3 := by
  intro G _ _ _ K z hS K₁ K₂ K₃ z₁ z₂ z₃ T
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hS.member
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hS.below
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hS.nonabelian hb1 (Set.singleton_subset_iff.mpr hbc)
  exact rankTwoSpan_eq_top_of_covers hΩ hIH hnc (omegaConnected_range_conjSub hS.delta) T.exact
    T.ind T.mem₁ T.mem₂ T.mem₃ T.cls₁ T.cls₂ T.cls₃
    (fun a ha hfa => hcov G K z hS K₁ K₂ K₃ z₁ z₂ z₃ T a ha hfa)

theorem bootTriple3_of'' (hcov : LieCovers3At) (hP1 : P1Cover3) : BootTriple3 :=
  Q3KB.bootTriple3_of_gen' (tripleGeneration3_of' hcov) hP1

end CFSG.ClassicalInvolution.Q3.Q3KC
