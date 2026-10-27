module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusAE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusSetup

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement


section N

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem eq_one_of_mem_two_of_mem_oddCoreOf {H Q : Subgroup Y} (hQ : IsPGroup 2 ↥Q) {d : Y}
    (hdQ : d ∈ Q) (hdH : d ∈ oddCoreOf H) : d = 1 :=
  eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hdH
    (hQ.to_le (Subgroup.zpowers_le.mpr hdQ))

theorem nside_ae (h : PerpHypS n Y R S t) {c : Y}
    {J J' Q Q' : Subgroup Y} {w : Y} (hT : LayerTwins Y R c J J' Q Q' w) {m : ℕ}
    (hm : m = 5 ∨ m = 6) (I : TC.Thin.AEIdent (TwinDisc.secFam (Om R) c) m) {x : Y}
    (hxc : x ∈ Subgroup.centralizer ({c} : Set Y)) (hxodd : Odd (orderOf x))
    (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hxQ' : ∀ b ∈ Q', x * b = b * x) :
    ∀ q ∈ Q, x * q = q * x := by
  classical
  have hn5 : 5 ≤ m := by rcases hm with rfl | rfl <;> norm_num
  have hC := CoreData.of_S h.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hT.hc2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hS := p23_q8Section h hT.hc2
  have F := TwinDisc.AE5.q8Fam_of_aeIdent_n hn5 hS I
  have hgen := F.gen
  set σ := TwinDisc.secAct hΩ hc2' (⟨x, hxc⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) with hσ
  have hperm : ∀ L ∈ TwinDisc.secFam (Om R) c, ∃ L' ∈ TwinDisc.secFam (Om R) c,
      L.map σ.toMonoidHom = L' := by
    intro L hL'
    obtain ⟨J₁, hJ₁, rfl⟩ := TwinDisc.exists_of_mem_secFam hL'
    exact ⟨_, TwinDisc.secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxc hJ₁),
      TwinDisc.secAct_map_secImg hΩ hc2' ⟨x, hxc⟩⟩
  set ψ := TwinDisc.autOfTop hgen σ with hψ
  have hψP := TwinDisc.autOfTop_perm hgen σ hperm
  have hxJ' : x ∈ trivialOnQuot J' :=
    TwinADescent3.mem_tq_of_sylCent hΩ h2 hT.hJ'.1
      ⟨Q', hT.hQ', fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hxQ' b hb).symm⟩
  have hmemJ' := TwinDisc.secImg_mem_secFam hT.hJ'
  have hfixJ' := TwinDisc.secAct_fix_secImg hΩ hc2' (F.two _ hmemJ') hxc hxJ'
  have hfix : ∀ y : ↥(TC.Thin.pSpan (TwinDisc.secFam (Om R) c)),
      (y : SecQ R c) ∈ TwinDisc.secImg (Om R) c J' → ψ y = y := fun y hy =>
    Subtype.ext (hfixJ' _ hy)
  have hψpow : ∀ j : ℕ, ∀ y : ↥(TC.Thin.pSpan (TwinDisc.secFam (Om R) c)),
      (((ψ ^ j) y : ↥(TC.Thin.pSpan (TwinDisc.secFam (Om R) c))) : SecQ R c) =
        (σ ^ j) (y : SecQ R c) := by
    intro j
    induction j with
    | zero => intro y; rfl
    | succ j ih =>
      intro y
      rw [pow_succ' ψ j, MulAut.mul_apply, TwinDisc.autOfTop_coe, ih, pow_succ' σ j,
        MulAut.mul_apply]
  have hσk : σ ^ orderOf x = 1 := by
    have h1 : (⟨x, hxc⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) ^ orderOf x = 1 :=
      Subtype.ext (by simpa using pow_orderOf_eq_one x)
    rw [hσ, ← map_pow, h1, map_one]
  have hψk : ψ ^ orderOf x = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [hψpow, hσk]
    rfl
  have hall := aut_eq_one_of_odd_fix hm F I ψ hψP hmemJ' hfix hxodd hψk
  have hσ1 : σ = 1 := by
    refine MulEquiv.ext fun a => ?_
    have := congrArg Subtype.val (hall ⟨a, TwinDisc.mem_pSpan_of_top hgen a⟩)
    exact this
  have hcomm := TwinDisc.comm_mem_oddCoreOf_of_secAct_eq_one hΩ hc2' hxc hσ1
  have hTs : IsSylow2In Q (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2' hT.hJ.2).mpr ⟨hT.hQ, hT.hQc⟩
  intro q hq
  have hqL : q ∈ TwinDisc.coreLayer (Om R) c := TwinDisc.coreAt_le_coreLayer hT.hJ (hTs.1 hq)
  have hd := hcomm q hqL
  have hdQ : x * q * x⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hxQ q hq) (Q.inv_mem hq)
  have h1 := eq_one_of_mem_two_of_mem_oddCoreOf hT.hQ.2.1 hdQ hd
  have h3 : x * q * x⁻¹ = q := mul_inv_eq_one.mp h1
  calc x * q = (x * q * x⁻¹) * x := by group
    _ = q * x := by rw [h3]

end N

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
