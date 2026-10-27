module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf53Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU24
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU29

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement



open CFSG.ClassicalInvolution.Balance

section U35

open CFSG.ClassicalInvolution.Q8P.P24 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer (tqMembers exactCore)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_sectionLifts (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hnoU : SecNoExit R u) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    (hOu : oddCoreIn (Subgroup.centralizer ({u} : Set Y)) = ⊥) :
    ∃ M M' : Subgroup Y,
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M (u * e) ∧
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M' (u * e) ∧
      conjSub g (tightCore R) ≤ M ∧ conjSub g K' ≤ M' ∧ (∀ a ∈ M, ∀ b ∈ M', a * b = b * a) := by
  classical
  have X := p23_innerHyp_u hc
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have h2g := p23_members_isPGroup hP hc hno hα
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hS := layer_q8Section hc.std.perp hd.hu2
  have hlt := card_layer_lt hc.std.perp hd.hu1
  have hlf := And.intro (secMemberLifted_of_noExit hP hlt hS hnoU X.htq)
    (secMemberLifted_of_noExit hP hlt hS hnoU X.htq')
  have htC := ue_comm_u hc
  obtain ⟨M, M', hM, hM', hne, hcomm, -, -, hmM, hmM'⟩ :=
    liftPair_of_twins hΩ hc2 hS X.htq X.htq' X.hne X.hb X.hb' htC hlf (x := 1)
      (Subgroup.one_mem _) (Subgroup.one_mem _) (Subgroup.one_mem _)
  have hcore : componentClassificationOddCore ↥(Subgroup.centralizer ({u} : Set Y)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hOu
  have hinj : ∀ a b : ↥(Subgroup.centralizer ({u} : Set Y)),
      oddQuotMk u a = oddQuotMk u b → a = b := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ componentClassificationOddCore ↥(Subgroup.centralizer ({u} : Set Y)) :=
      (QuotientGroup.eq).mp hab
    rw [hcore, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.mp h1)
  have hxcore : ∀ (J : Subgroup Y) (hJ : J ∈ tqMembers3 (Om R) u),
      IsPGroup 2 ↥J → ∀ x ∈ J, x ∈ TwinADescent.coreAt u J := by
    intro J hJ hJ2 x hx
    have hxC : x ∈ Subgroup.centralizer ({u} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_trivialOnQuot hJ2 hJ.2 hx).symm
    have hle : Subgroup.zpowers x ≤ J ⊓ Subgroup.centralizer ({u} : Set Y) :=
      Subgroup.zpowers_le.mpr ⟨hx, hxC⟩
    have h2x : IsPGroup 2 ↥(Subgroup.zpowers x) :=
      hJ2.to_le (Subgroup.zpowers_le.mpr hx)
    exact le_tightCore_of_isPGroup hle h2x (Subgroup.mem_zpowers x)
  refine ⟨M, M', hM, hM', ?_, ?_, ?_⟩
  · intro x hx
    exact hmM x (hxcore _ X.htq (h2g _ X.hK) x hx) (X.hb.commute_of_mem hx).symm
  · intro x hx
    exact hmM' x (hxcore _ X.htq' (h2g _ X.hK') x hx) (X.hb'.commute_of_mem hx).symm
  · intro a ha b hb
    have haC : a ∈ Subgroup.centralizer ({u} : Set Y) := hM.le ha
    have hbC : b ∈ Subgroup.centralizer ({u} : Set Y) := hM'.le hb
    have := hcomm (oddQuotMk u ⟨a, haC⟩) ⟨⟨a, haC⟩, ha, rfl⟩
      (oddQuotMk u ⟨b, hbC⟩) ⟨⟨b, hbC⟩, hb, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (hinj _ _ this)

end U35

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
