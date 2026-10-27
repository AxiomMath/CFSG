module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionB
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourModel
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPosition

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_normal_map_oddCore_neighbour_E7_two {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK'
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hXL : X ≤ L := hXJ.trans (map_subtype_le _)
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  obtain ⟨g, z, hzL, hgz, hz1, hzU⟩ := exists_conj_eq_mul_twoCentral_E7_two hset hK e ht hKt
  obtain ⟨g₁, y, hyD, hy1, hg₁, P, hP, ⟨eP⟩⟩ :=
    exists_le_centralizer_mulEquiv_of_conj_eq_mul_twoCentral_E7_of_one_le hset le_rfl hK' e htC
      ht hXodd hXJ hzL hz1 hzU hgz
  subst hDe
  set eD := perpLeviMapEquivE7 (G := G) e with heD
  have hDL : ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype ≤ L :=
    map_subtype_le _
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht
    (map_perpLevi_le_centralizer_E7_of_charTwo e hXJ)
    (F4Pilot.isQuasisimple_open_of_mulEquiv eD isQuasisimple_open_perpLevi_E7)
    (F4Pilot.center_eq_bot_congr eD center_perpLevi_E7_eq_bot)
    ((CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eD).2.1 isSolvable_outer_perpLevi_E7)
    (hDL.trans hLt) hsyl hyD hy1 (Or.inr hg₁) hP ⟨eP.trans eD⟩

theorem exists_nonsplit_le_posJE7_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    ∃ A : Subgroup (adjointGroup .E7 K), A ≤ posJE7 K ∧ Nat.card A = 3 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK'
  obtain ⟨A, hAJ, -, hA⟩ := E6Pilot.exists_nonsplit_le_subgroupOf_highRootSL2 (τ := .E7) (K := K)
  exact ⟨A, hAJ, by rw [hA, hK]⟩

end CFSG.SeitzReduction.E7Pilot
