module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Cn
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Rk
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt17
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Final.Thm4
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.DisconnectedInvolutionGraph.Helpers (NoCommutingDistinctInvolutions
  no_commuting_distinct_involutions_of_injective no_commuting_distinct_involutions_sylow_iff)
open scoped commutatorElement

theorem lemma17_2_of (h31 : Lemma31Narrow) : Lemma17_2 := by
  intro G _ _ z k S M h hOdd J hJ
  have hMC : M = Cen z := h.ctx.eq_of_oddCover hOdd
  have hMne : M ≠ ⊤ := h.ctx.mem.1.1
  subst hMC
  have ctx : Stage2Ctx G z k S := h.ctx.ctx
  have hz2 : orderOf z = 2 := ctx.central.1
  have hz2' : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  have hJC : J ≤ Cen z := hJ.1
  have hcentJ : ∀ A : Subgroup G, A ≤ J → z ∈ centralizer (A : Set G) := fun A hA => by
    rw [mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hJC (hA hx))
  have hzY : z ∈ Cen z ⊓ centralizerSection J (pPrimeCoreOf 2 J) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_, ?_, ?_⟩
    · exact Subgroup.centralizer_le_normalizer _ (hcentJ J le_rfl)
    · exact Subgroup.centralizer_le_normalizer _ (hcentJ _ (Subgroup.map_subtype_le _))
    · intro x hx
      have : ⁅x, z⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.mp (hJC hx))
      rw [this]
      exact one_mem _
  set Y := Cen z ⊓ centralizerSection J (pPrimeCoreOf 2 J) with hYdef
  have hp : IsPGroup 2 ↥(zpowers (⟨z, hzY⟩ : ↥Y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz2, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  set R : Subgroup G := (Q : Subgroup ↥Y).map Y.subtype with hRdef
  have hR : CFSG.ABGLocalTools.IsSylowOf 2 R Y := ⟨Q, rfl⟩
  have hzR : z ∈ R := ⟨⟨z, hzY⟩, hQ (mem_zpowers _), rfl⟩
  have hR1 : R ≠ ⊥ := fun hbot => by
    rw [hbot, Subgroup.mem_bot] at hzR
    rw [hzR, orderOf_one] at hz2
    omega
  have hcl := h31 G z k S ctx (Cen z) J R hMne hJ hR hR1
  have hncR : NoCommutingDistinctInvolutions ↥R := by
    rcases hcl.1 with hc | hq | hd
    · exact noCommuting_of_isCyclic hc
    · exact noCommuting_of_isQuat hq
    · exact absurd (hcl.2.1 hd) (not_alt7_or_L2_of_nonsimple (TwoThin.isQuasisimple_hat hJ)
        (hat_not_isSimpleGroup ctx hJ))
  let eQ : ↥(Q : Subgroup ↥Y) ≃* ↥R :=
    Subgroup.equivMapOfInjective (Q : Subgroup ↥Y) Y.subtype Y.subtype_injective
  have hncQ : NoCommutingDistinctInvolutions ↥(Q : Subgroup ↥Y) :=
    no_commuting_distinct_involutions_of_injective eQ.toMonoidHom eQ.injective hncR
  have hncY : NoCommutingDistinctInvolutions ↥Y :=
    (no_commuting_distinct_involutions_sylow_iff Q).mpr hncQ
  have hle1 := pRank_le_one_of_noCommuting hncY
  have hge1 : 1 ≤ CFSG.pRank 2 ↥Y := by
    have hel := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers (p := 2) hz2'
    have hcard : Nat.card ↥(zpowers z) = 2 ^ 1 := by rw [Nat.card_zpowers, hz2, pow_one]
    have := CFSG.GH74.Uniqueness.SU.SU1.le_pRank (p := 2) one_lt_two (H := Y) (E := zpowers z)
      (Subgroup.zpowers_le.2 hzY) hel hcard
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two]
    exact this
  omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
