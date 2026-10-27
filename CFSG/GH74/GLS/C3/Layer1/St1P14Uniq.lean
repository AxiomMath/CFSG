module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.GLS.C3.Layer1.Back112Glue
public import CFSG.GH74.GLS.TwoThin.G.Shape
public import CFSG.GH74.E2.K0Simple
public import CFSG.GH74.E2.TermLeaves

public section

namespace CFSG.GH74.GLS.C3.Layer1.P14

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.PumpCalc
open scoped commutatorElement

section Rank

theorem rank_le_one_of_isCyclic {U : Type} [Group U] [Finite U] (h : IsCyclic U) :
    Group.rank U ≤ 1 := by
  obtain ⟨g, hg⟩ := h.exists_generator
  have hcl : Subgroup.closure (↑({g} : Finset U) : Set U) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subgroup.zpowers g := hg x
    rw [Subgroup.zpowers_eq_closure] at hx
    simpa using hx
  simpa using Group.rank_le hcl

theorem rank_quaternion_le_two (n : ℕ) [NeZero n] : Group.rank (QuaternionGroup n) ≤ 2 := by
  have hcl : Subgroup.closure (↑({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
      Finset (QuaternionGroup n)) : Set (QuaternionGroup n)) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have ha1 : (QuaternionGroup.a (1 : ZMod (2 * n)) : QuaternionGroup n) ∈
        Subgroup.closure (↑({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
          Finset (QuaternionGroup n)) : Set (QuaternionGroup n)) :=
      Subgroup.subset_closure (by simp)
    have hx0 : (QuaternionGroup.xa (0 : ZMod (2 * n)) : QuaternionGroup n) ∈
        Subgroup.closure (↑({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
          Finset (QuaternionGroup n)) : Set (QuaternionGroup n)) :=
      Subgroup.subset_closure (by simp)
    have hapow : ∀ i : ZMod (2 * n), (QuaternionGroup.a i : QuaternionGroup n) ∈
        Subgroup.closure (↑({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
          Finset (QuaternionGroup n)) : Set (QuaternionGroup n)) := by
      intro i
      have := Subgroup.pow_mem _ ha1 i.val
      rwa [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val] at this
    cases g with
    | a i => exact hapow i
    | xa i =>
      have : (QuaternionGroup.xa i : QuaternionGroup n) =
          QuaternionGroup.xa 0 * QuaternionGroup.a i := by
        simp [QuaternionGroup.xa_mul_a]
      rw [this]
      exact Subgroup.mul_mem _ hx0 (hapow i)
  have := Group.rank_le hcl
  have hcard : (({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
      Finset (QuaternionGroup n))).card ≤ 2 := Finset.card_le_two
  omega

theorem two_le_pRank_of_rank_three {U : Type} [Group U] [Finite U] (hU : IsPGroup 2 U)
    (h3 : 3 ≤ Group.rank U) : 2 ≤ CFSG.pRank 2 U := by
  by_contra hlt
  have hno : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions U := by
    intro a b hab
    by_contra hne
    exact hlt (CFSG.GH74.E2.two_le_pRank_of_commuting_involutions a.2 b.2
      (fun h => hne (Subtype.ext h)) hab)
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hU hno with
    hc | ⟨k, -, ⟨e⟩⟩
  · have := rank_le_one_of_isCyclic hc
    omega
  · have h1 : Group.rank U = Group.rank (QuaternionGroup (2 ^ k)) := (Group.rank_congr e).symm
    have := rank_quaternion_le_two (2 ^ k)
    omega

end Rank

section Component

theorem two_le_pRank_of_c2u2
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) {L : Type} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hcls : InC2 L ∨ InU2 L) (hgen : CFSG.GH74.Gen4 L)
    (hno : ¬ (IsL34Quotient L ∧ CFSG.IsElementaryAbelian 2 ↥(center L) ∧
      Nat.card ↥(center L) ≤ 4)) :
    2 ≤ CFSG.pRank 2 L := by
  by_cases hz : center L = ⊥
  · exact LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
      (by rw [hz, Subgroup.card_bot]; exact odd_one)
  · rcases hcls with hC | hU
    · rcases TwoThin.c2ShapeG_of_inC2 hG hF hC hgen with h | h | h
      · exact absurd h hz
      · obtain ⟨U, hU, hr⟩ := CFSG.GH74.E2.rank_ge4_of_shape2M12 h
        exact (two_le_pRank_of_rank_three hU (by omega)).trans (C3.Layer1.Back.pRank_le_top U)
      · obtain ⟨U, hU, hr⟩ := CFSG.GH74.E2.rank_ge3_of_shape2Sz8 h
        exact (two_le_pRank_of_rank_three hU hr).trans (C3.Layer1.Back.pRank_le_top U)
    · obtain ⟨hq', hc⟩ := hU
      rcases hc with ⟨p, f, hp, hf, hodd, hL⟩ | hB | hl
      · have hs : IsSimpleGroup L := (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hL).2.2
        exact absurd (center_eq_bot_of_isSimple hs hq) hz
      · have hs : IsSimpleGroup L := by
          obtain ⟨e⟩ := hB
          have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
            alternatingGroup.isSimpleGroup (by simp)
          exact e.isSimpleGroup
        exact absurd (center_eq_bot_of_isSimple hs hq) hz
      · exact absurd hl hno

end Component

section Unique

theorem l34type_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsL34Quotient A ∧ CFSG.IsElementaryAbelian 2 ↥(center A) ∧ Nat.card ↥(center A) ≤ 4) :
    IsL34Quotient B ∧ CFSG.IsElementaryAbelian 2 ↥(center B) ∧ Nat.card ↥(center B) ≤ 4 := by
  obtain ⟨hl, hel, hcard⟩ := h
  refine ⟨TwoThin.isL34Quotient_of_mulEquiv e hl, ?_, ?_⟩
  · exact isElementaryAbelian_two_of_mulEquiv (Subgroup.centerCongr e) hel
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hcard

variable {G : Type} [Group G] [Finite G]

end Unique

end CFSG.GH74.GLS.C3.Layer1.P14
