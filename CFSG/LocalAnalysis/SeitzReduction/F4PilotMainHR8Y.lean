module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainKinds
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusPointwiseAut

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

theorem rDiag_perm_pow_exponent {K : Type} [Field K] (c : Kˣ) :
    (fun j => rDiag c (ReeTag.F4.perm j) ^ ReeTag.F4.exponent (ReeTag.F4.perm j)) =
      ![1, 1, 1, c] := by
  funext j
  rw [CFSG.RankThree.Chevalley.EvenF4QPlus.exponent_perm_F4,
    CFSG.RankThree.Chevalley.EvenF4QPlus.perm_F4_eq_rev]
  fin_cases j <;> simp [rDiag, ReeTag.tag, Tag.rank]
  · show (1 : Kˣ) ^ 2 = 1
    exact one_pow 2
  · show (1 : Kˣ) ^ 2 = 1
    exact one_pow 2
  · rfl
  · rfl

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem graphAutF4_rootDiagUnit_rDiag (c : Kˣ) :
    ((graphAutF4 K ⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ :
      adjointGroup .F4 K) : ModGL .F4 K) = rootDiagUnit .F4 ![1, 1, 1, c] := by
  have h := CFSG.RankThree.Chevalley.EvenF4QPlus.finiteExceptionalAut_rootDiagUnit (L := K)
    (rDiag c) (f4RootDiagUnit_mem_adjointGroup _)
  rw [rDiag_perm_pow_exponent] at h
  exact h

theorem map_graphAutF4_torusLineR :
    ((torusLineR K).subgroupOf (adjointGroup .F4 K)).map (graphAutF4 K).toMonoidHom =
      (torusLineS K).subgroupOf (adjointGroup .F4 K) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨c, hc⟩ := mem_torusLineR.1 (mem_subgroupOf.1 hh)
    have hh' : h = ⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ :=
      Subtype.ext hc.symm
    subst hh'
    refine mem_subgroupOf.2 (mem_torusLineS.2 ⟨c, ?_⟩)
    exact (graphAutF4_rootDiagUnit_rDiag c).symm
  · intro hg
    obtain ⟨c, hc⟩ := mem_torusLineS.1 (mem_subgroupOf.1 hg)
    refine ⟨⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩,
      mem_subgroupOf.2 (mem_torusLineR.2 ⟨c, rfl⟩), Subtype.ext ?_⟩
    change ((graphAutF4 K ⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ :
      adjointGroup .F4 K) : ModGL .F4 K) = g
    rw [graphAutF4_rootDiagUnit_rDiag, hc]

end Torus

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem symm_trans_graphAutF4_symm (e : L ≃* adjointGroup .F4 K) :
    (e.trans (graphAutF4 K).symm).symm.toMonoidHom =
      e.symm.toMonoidHom.comp (graphAutF4 K).toMonoidHom :=
  MonoidHom.ext fun _ => rfl

theorem neighbourTorusG_Y_eq (e : L ≃* adjointGroup .F4 K) :
    neighbourTorusG e .Y = (((torusLineR K).subgroupOf (adjointGroup .F4 K)).map
      (e.trans (graphAutF4 K).symm).symm.toMonoidHom).map L.subtype := by
  rw [symm_trans_graphAutF4_symm, ← Subgroup.map_map, map_graphAutF4_torusLineR]
  rfl

theorem neighbourLeviG_Y_eq (e : L ≃* adjointGroup .F4 K) :
    neighbourLeviG e .Y =
      ((C3Levi K).map (e.trans (graphAutF4 K).symm).symm.toMonoidHom).map L.subtype := by
  rw [symm_trans_graphAutF4_symm, ← Subgroup.map_map, map_graphAutF4_C3Levi]
  rfl

end Transport

section HR8Y

theorem hr8YInput_holds : HR8YInput := by
  intro hcat G _ _ L K _ t f e hw hf htY
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have : CharP K ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
  exact neighbour_overgroup_torusLineR hcat hw.standard hf hw.card_eq
    (e.trans (graphAutF4 K).symm) hw.orderOf_eq hw.inf_eq (neighbourTorusG_Y_eq e) htY
    (neighbourLeviG_Y_eq e)

end HR8Y

end CFSG.SeitzReduction.F4Pilot
