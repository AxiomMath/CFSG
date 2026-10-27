module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf14Inner
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf21Vertex

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.P24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q8P.Asc77
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer (tqMembers exactCore)
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Perp


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}

theorem v3_out_gen₂ (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h4 : Thm4RTwinBelow 3 n)
    (hPerp : PerpHypS n Y R S t₀) {c : Y} (hcc : c * c = 1) (hc1 : c ≠ 1) {b : Y} {J J' : Subgroup Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) (hJ' : J' ∈ CoreAssembly.conjClass (tightCore R))
    (htJ : IsUniqueInvolution J b) (htJ' : IsUniqueInvolution J' b) (hne : J' ≠ J)
    (hcJ : c ∈ trivialOnQuot J) (hcJ' : c ∈ trivialOnQuot J')
    (htC : b ∈ Subgroup.centralizer ({c} : Set Y)) :
    Quiet c b htC ∨ TwinExitPf9.LiftedAtSec J c b htC ∨ (ExitAt J c b htC ∧ MovedOddFreeAt c b htC) := by
  have hC := CoreData.of_S hPerp.core
  have hZ : Subgroup.center Y = ⊥ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.center_eq_bot_of_fstar_simple hC.simple hC.nonab
  obtain ⟨S₀, h₀⟩ := TwinEdge.twinCoreHyp_core hPerp.core.toHyp
  have hid := TwinEdge.tightCore_idem R
  have hΩeq : CoreAssembly.conjClass (tightCore (tightCore R)) =
      CoreAssembly.conjClass (tightCore R) := by rw [hid]
  have hJ0 : J ∈ CoreAssembly.conjClass (tightCore (tightCore R)) := by rw [hΩeq]; exact hJ
  obtain ⟨SJ, hJd⟩ := exists_datum_at h₀ hid hJ0 htJ
  have hRcJ : tightCore J = J := tightCore_eq_of_mem hid hJ0
  have hcm : c ∈ centralizerModOdd ⊤ J :=
    ⟨Subgroup.mem_top _, hcJ.1, mem_normalizer_oddCore_of_mem_normalizer hcJ.1,
      fun l hl => hcJ.2 l hl⟩
  have hJ'tw : J' ∈ twinSet (CoreAssembly.conjClass (tightCore J)) (tightCore J) := by
    rw [hRcJ, conjClass_eq_of_mem hJ0, hΩeq]
    exact ⟨hJ', b, htJ, htJ'⟩
  have hne' : J' ≠ tightCore J := by rw [hRcJ]; exact hne
  exact TwinExitPf9.quietLiftedSecExit_of_twin hSp hD4 h4 hJd hRcJ hZ hcc hc1 hcm htC hJ'tw hne' hcJ'

end Perp

section Out2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {K₀ K K' : Subgroup G} {b d : G} {B : Subgroup G}

@[expose] def TwinInnerOutAt (Ω : Set (Subgroup G)) : Prop :=
  ∀ (K₀ : Subgroup G),
    AscStand Ω K₀ → CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.EIHAll (Nat.card G) →
      (∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) →
      ∀ {K K' : Subgroup G} {b d c : G} {B : Subgroup G}, TwinInnerHyp Ω K K' b d c B →
        ∀ hbc : b ∈ Subgroup.centralizer ({c} : Set G),
          Quiet c b hbc ∨ SecLift Ω c K ∨ (ExitAt K c b hbc ∧ MovedOddFreeAt c b hbc)


theorem hyp51TwinInnerAt_of_outAt [CoreLike G] (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (hM12 : ModelFactM12) (hO : TwinInnerOutAt Ω) : Hyp51TwinInnerAt Ω := by
  intro K₀ hst hE hq2 K K' b d c hK hK' hne hb hb' htq htq' B hB hbB hdB hcB hgen hc1 hbc
    hd1 hdb hd2 hdK
  have X : TwinInnerHyp Ω K K' b d c B :=
    ⟨hK, hK', hne, hb, hb', htq, htq', hB, hbB, hdB, hcB, hgen, hc1, hbc, hd1, hdb, hd2, hdK⟩
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hB.1.is_comm.comm (⟨b, hbB⟩ : B) ⟨c, hcB⟩
      exact congrArg Subtype.val this)
  have out1 := hO _ hst hE hq2 X hbC
  have out2 := hO _ hst hE hq2 X.swap hbC
  have hexit : ∀ {J : Subgroup G}, ExitAt J c b hbC → MovedOddFreeAt c b hbC → Hyp51At B c :=
    fun he hm => hyp51At_of_exit hSp hD4 hM12 hB hcB hbB hc1 hb.ne_one hbc hbC he hm
  have hquiet : Quiet c b hbC → Hyp51At B c := fun q =>
    hyp51At_of_quiet hB hcB hbB hc1 hb.ne_one hbc hbC q
  rcases out1 with q | l1 | ⟨e1, m1⟩
  · exact hquiet q
  · rcases out2 with q | l2 | ⟨e2, m2⟩
    · exact hquiet q
    · exact hyp51At_of_secLifts hst hE hq2 X l1 l2
    · exact hexit e2 m2
  · exact hexit e1 m1

end Out2

section Perp2


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}

theorem twinInnerOutAt_of_perp (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h4 : Thm4RTwinBelow 3 n)
    (hP : PerpHypS n Y R S t₀) : TwinInnerOutAt (CoreAssembly.conjClass (tightCore R)) := by
  intro K₀ hst hE hq2 K K' b d c B X hbC
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hst.hyp
  have hcc : c * c = 1 := by rw [← pow_two]; exact X.hB.2 c X.hcB
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcc
  have hS := layer_q8Section hP hcc
  rcases v3_out_gen₂ hSp hD4 h4 hP hcc X.hc1 X.hK X.hK' X.hb X.hb' X.hne X.htq.2 X.htq'.2 hbC with
    q | l | e
  · exact Or.inl q
  · obtain ⟨htH, L, hL⟩ := TwinExitPf9.isLiftOf_of_liftedAtSec hΩ hc2' hS X.htq X.hb hbC l
    exact Or.inr (Or.inl ⟨L, _, hL⟩)
  · exact Or.inr (Or.inr e)

theorem hyp51TwinInnerPerp_of_model (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (hM12 : ModelFactM12) (h4 : Thm4RTwinBelow 3 n) : Hyp51TwinInnerPerp n := by
  intro Y _ _ R S t hP
  have : CoreLike Y := coreLike_of_core (CoreData.of_S hP.core)
  intro K₀
  exact hyp51TwinInnerAt_of_outAt hSp hD4 hM12 (twinInnerOutAt_of_perp hSp hD4 h4 hP) (K₀ := K₀)

end Perp2

end CFSG.ClassicalInvolution.Q8P.P24
