module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Spor
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.Monster.B.CTIB.ComponentsSeventeen

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem IsU42Root.card_quotient_center {D : Type} [Group D] {α : MulAut D} {S : Subgroup D}
    (h : IsU42Root α S) : Nat.card (S ⧸ center S) = 25920 := by
  have := h.2.2.2.1
  have hz : center S = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.2.2.2.2.1).2
  rw [← h.2.2.2.2.2]
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).toEquiv

theorem b_u42Free :
    SporadicU42Free .B := by
  have hU := u42_fails_card_quotient_center_mem (N := {76532479683774853939200, 3311126603366400})
    (by norm_num)
  refine sporadicU42Free_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hU hU (fun G _ _ ⟨e⟩ t ht K hK => ?_)
    (outer_comps_of_forall_inner (s := .B) ?_ _)
  swap
  · have hB : ∀ β : MulAut (NativeSporadic.Carrier .B), β ∈ inner (NativeSporadic.Carrier .B) :=
      CFSG.ComponentClassification.BMCase.inner_of_mulEquiv_pinnedB NativeSporadic.B
        ⟨MulEquiv.refl NativeSporadic.B⟩
    exact hB
  obtain ⟨-, hiso, -⟩ :=
    CFSG.Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t
      ht K hK
  rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · left
    rw [Nat.card_congr φ.toEquiv, CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
  · right
    obtain ⟨ψ⟩ := CFSG.Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
    rw [Set.mem_singleton_iff, Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
      CFSG.Monster.B.E6.FieldInvF4.card_groupJ]

theorem m_u42Free
    :
    SporadicU42Free .M := by
  intro D _ _ hD hs α S h
  have hα : α ∈ inner D := CFSG.ComponentClassification.CatLeafProof.monsterInnerInput D hD hs α
  obtain ⟨t, ht, hαt⟩ :=
    exists_involution_of_mem_inner (h.center_eq_bot_of_isSimpleGroup hD) h.1 hα
  have hcomp := h.isComponent
  have hCt : α.toMonoidHom.eqLocus (MonoidHom.id D) = centralizer ({t} : Set D) := by
    rw [← hαt]
    exact eqLocus_conj t
  set C := α.toMonoidHom.eqLocus (MonoidHom.id D)
  have h2 := CFSG.ComponentClassification.CatLeafProof.monsterLocalComponentsInput D hD hs t ht
    ((S.subgroupOf C).map (MulEquiv.subgroupCongr hCt).toMonoidHom)
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulEquiv.subgroupCongr hCt) hcomp)
  have hcardq : Nat.card (((S.subgroupOf C).map (MulEquiv.subgroupCongr hCt).toMonoidHom) ⧸
      center ((S.subgroupOf C).map (MulEquiv.subgroupCongr hCt).toMonoidHom)) = 25920 := by
    rw [card_quotient_center_congr
      (((S.subgroupOf C).equivMapOfInjective _ (MulEquiv.subgroupCongr hCt).injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe h.2.1))]
    exact h.card_quotient_center
  rw [hcardq] at h2
  exact absurd h2.1 (by norm_num)

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
