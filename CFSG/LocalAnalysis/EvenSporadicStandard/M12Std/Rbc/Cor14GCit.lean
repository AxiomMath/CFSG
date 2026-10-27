module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.GLevel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Quat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Sylow
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWitness
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.Sporadic.Schreier.M11

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

theorem exists_quaternion_sylow_of_pRank_one {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hr : CFSG.pRank 2 X = 1) (P : Sylow 2 X) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((P : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hP2 := hq.2.2
  haveI : IsSimpleGroup (X ⧸ center X) := hq.2.1
  let π : X →* X ⧸ center X := QuotientGroup.mk' (center X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  rcases Junction.sylow_cyclic_or_quaternion hr P with hcyc | ⟨e, he, ⟨eQ⟩⟩
  · exfalso
    let P' : Sylow 2 (X ⧸ center X) := Sylow.mapSurjective hπ P
    have hP' : (P' : Subgroup (X ⧸ center X)) = (P : Subgroup X).map π :=
      Sylow.coe_mapSurjective hπ P
    let gP : ↥(P : Subgroup X) →* ↥(P' : Subgroup (X ⧸ center X)) :=
      (π.comp (P : Subgroup X).subtype).codRestrict _ (fun x => hP' ▸ ⟨x, x.2, rfl⟩)
    have hgP : Function.Surjective gP := by
      rintro ⟨y, hy⟩
      rw [hP'] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      exact ⟨⟨p, hp⟩, rfl⟩
    have : IsCyclic ↥(P' : Subgroup (X ⧸ center X)) := isCyclic_of_surjective gP hgP
    exact Junction.not_isCyclic_sylow_two hP2 P' this
  · refine ⟨e + 2, by omega, ?_⟩
    rw [Nat.add_sub_cancel]
    exact ⟨eQ.symm⟩

section Cit

open _root_.Certificates


theorem oddLie_or_m11_of_rankOne
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : orderOf z = 2) {X : Subgroup G} (hzX : z ∈ X)
    (hX : IsCompIn X (centralizer ({z} : Set G))) (hrk : CFSG.pRank 2 ↥X = 1) :
    OddLieType G ∨ IsSporadic G .M11 := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hS := exists_quaternion_sylow_of_pRank_one hX.isQuasisimple hrk P
  have hXa : CFSG.Assembly.IsComponentOf X (centralizer ({z} : Set G)) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hX.1).2 hX.2
  obtain ⟨hw, hsub⟩ :=
    CFSG.ComponentClassification.QuaternionComponent.classicalInvolutionWitness_of_component
      hz hXa hzX P hS
  let eF : CFSG.Open.genFittingFStar G ≃* G :=
    (MulEquiv.subgroupCongr
      (CFSG.ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
        hna)).trans Subgroup.topEquiv
  have : IsSimpleGroup (CFSG.Open.genFittingFStar G) := eF.isSimpleGroup
  have hFnonab : ∃ a b : CFSG.Open.genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  rcases (hCIT G hFnonab z hz X hzX hsub P hS).1 hw with h | h
  · exact Or.inl ((CFSG.ClassicalInvolution.oddLieType_congr eF).1 h)
  · exact Or.inr ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h)

end Cit

section M11

open _root_.Certificates


theorem Out.false_of_isSporadic_m11 {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hO : Out G L t) (hM : IsSporadic G .M11) : False := by
  obtain ⟨e⟩ := hM
  have h1 : Nat.card G = 7920 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m11_card
  have h2 : Nat.card L = 95040 := PropA.card_of_isSporadic_m12 hO.m12
  have h3 := Subgroup.card_le_card_group L
  omega

end M11

end CFSG.EvenSporadicStandard.M12Std.Rbc

