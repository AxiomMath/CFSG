module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEControl
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEAltSeven
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEIsolated
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedStronglyEmbedded
import CFSG.GroupTheory.SylowIntersectionControl.GomiAltSixChev
import CFSG.GroupTheory.SylowIntersectionControl.Quotient
import CFSG.GroupTheory.SylowIntersectionControl.Regular

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

private theorem controls_gomiRegFamily_e (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    (h22 : GomiFact22) (h23 : GomiFact23) (h36 : GomiFact36)
    (h45 : ∀ S : Subgroup Ω, IsSylowTwoOf S G → ∃ X : Subgroup Ω, IsGomiSingularSubgroup G S X)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    ControlsSylowIntersections 2 (gomiRegFamily f G) ⊤ := by
  have hbt : IsGomi410Type G B := hBt
  rcases hbt with hchev | halt | h7
  · exact h.controls_gomiRegFamily_chev hfZ hchar hmono h22 h36 h45 hB hBt hGB hCQ hchev
  · obtain ⟨m, hm, ⟨e⟩⟩ := halt
    by_cases hm3 : m = 3
    · subst m
      exact h.controls_gomiRegFamily_chev hfZ hchar hmono h22 h36 h45 hB hBt hGB hCQ
        (isGomiChevTwo_of_mulEquiv_altSix e)
    · exact h.controls_gomiRegFamily_alt hchar hmono h23 hB hBt hGB hCQ (by omega) e
  · exact h.controls_gomiRegFamily_altSeven hchar hmono h23 hB hBt h7 hGB hCQ

theorem Gomi410Cex.isRegular_of_inputs (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    (hBender : GomiBender) (hBSL2 : GomiBenderSL2) (h22 : GomiFact22) (h23 : GomiFact23)
    (h36 : GomiFact36)
    (h45 : ∀ S : Subgroup Ω, IsSylowTwoOf S G → ∃ X : Subgroup Ω, IsGomiSingularSubgroup G S X)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    f.IsRegular G := by
  have hctl := controls_gomiRegFamily_e h hfZ hchar hmono h22 h23 h36 h45 hB hBt hGB hCQ
  have hiso : ¬ IsPIsolatedOver 2 (⊤ : Subgroup ↥(autOn G (gomiV G))) ⊥ :=
    not_isPIsolatedOver_autOn hBender hBSL2 hB hBt hCQ
  have hind : ∀ X ∈ gomiRegFamily f G, ¬ 2 ∣ X.index := fun _ hX => hX.2.1.not_two_dvd_nat
  have hp : 2 ∣ Nat.card ↥(autOn G (gomiV G)) :=
    (even_iff_two_dvd.mp (even_card_gomiBarOf hB hBt hCQ)).trans
      (Subgroup.card_subgroup_dvd_card (gomiBarOf G B))
  have hne : (gomiRegFamily f G).Nonempty :=
    ControlsSylowIntersections.nonempty_of_not_isPIsolatedOver hctl hiso
      (Gomi410Cex.eq_bot_of_normal_autOn h hfZ hchar hmono) hp
  have hctl' : ControlsSylowIntersections 2
      ((fun X => X.comap (gomiBar G)) '' gomiRegFamily f G) ⊤ :=
    ControlsSylowIntersections.comap_of_surjective (gomiBar_surjective G)
      (isNormalSetIn_gomiRegFamily f G) hne hind hctl hiso
  have hfam : (fun X : Subgroup ↥G => X.map G.subtype) ''
      ((fun X : Subgroup ↥(autOn G (gomiV G)) => X.comap (gomiBar G)) '' gomiRegFamily f G)
      = gomiBarPre G '' gomiRegFamily f G := by
    rw [Set.image_image]
    rfl
  have hfinal : ControlsSylowIntersections 2 (gomiBarPre G '' gomiRegFamily f G) G := by
    rw [← hfam]
    exact ControlsSylowIntersections.map_subtype hctl'
  refine PSubgroupSelection.IsRegular.of_controlsSylowIntersections
    (𝓓 := gomiBarPre G '' gomiRegFamily f G) ?_ ?_ ?_ hfinal
  · rintro X ⟨M, -, rfl⟩
    exact gomiBarPre_le G M
  · rintro X ⟨M, hM, rfl⟩
    rw [relIndex_gomiBarPre]
    exact hM.2.1.not_two_dvd_nat
  · rintro X ⟨M, hM, rfl⟩
    exact hM.2.2

theorem Gomi410Cex.isRegular (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    (hBender : GomiBender) (hBSL2 : GomiBenderSL2) (h22 : GomiFact22) (h23 : GomiFact23)
    (h36 : GomiFact36)
    (h45 : ∀ S : Subgroup Ω, IsSylowTwoOf S G → ∃ X : Subgroup Ω, IsGomiSingularSubgroup G S X)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (_hQB : ⁅pCoreOf 2 G, B⁆ ≤ gomiV G)
    (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    f.IsRegular G :=
  h.isRegular_of_inputs hfZ hchar hmono hBender hBSL2 h22 h23 h36 h45 hB hBt hGB hCQ

end CFSG.GroupTheory
