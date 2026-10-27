module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU29
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU24
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf50Odd

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

section U30

open CFSG.ClassicalInvolution.Q8P.P24 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_oddCent_eq_bot₂ (hD4 : ModelFactD42) (hT : TwinThmE.T4Supply) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    (halpha : ∀ A : Subgroup Y, A ≤ Subgroup.closure ({u * e, u, t} : Set Y) → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({u, t} : Set Y)))
    (hTwo : Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
  have hd := hc.data
  have htc : t ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_ut hc).symm
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hJ2 := p23_members_isPGroup hP hc hno hα
  have hut : u * t = t * u := (Subgroup.mem_centralizer_singleton_iff.mp htc).symm
  have hα' : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := by
    rw [Set.pair_comm]; exact hα
  have hBle : Subgroup.closure ({u * e, u} : Set Y) ≤ Subgroup.closure ({u * e, u, t} : Set Y) :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  have hAue : IsElemAbelian2 (Subgroup.closure ({u * e, u} : Set Y)) 2 :=
    T7A.isElemAbelian2_closure_pair (ue_sq hc) hd.hu2 (ue_ne_one hc) hd.hu1
      (fun h => hd.he1 (by simpa using h)) (by
        have := (Subgroup.mem_centralizer_singleton_iff.mp (ue_comm_u hc))
        exact this)
  have hαue : alphaOf (Subgroup.closure ({u * e, u} : Set Y)) = ⊥ := by
    rw [halpha _ hBle hAue]; exact hα
  have hmo := p23_movedOddFree_ue hD4 hT hcit hP hc
  have hq1 : oddCoreIn (Subgroup.centralizer ({u * e} : Set Y)) ≤
      oddCoreIn (Subgroup.centralizer ({u} : Set Y)) :=
    TwinOdd.oddCent_le_of_alpha (ue_comm_u hc) (ue_sq hc) (ue_ne_one hc) hαue hmo.2
  have hcomm : oddCoreIn (Subgroup.centralizer ({u} : Set Y)) ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact TwinDisc.oddCore_comm_of_alpha hα (Subgroup.subset_closure (by simp)) hd.hu1
      (Subgroup.subset_closure (by simp)) hm
  have hK : tightCore R ∈ twinSet (Om R) (tightCore R) :=
    mem_twinSet_self (CoreAssembly.mem_conjClass_self _) hz
  have hPo2 : TwinPerpV3.InO2C u t := by
    refine ⟨TwinSecXg.twinJoin (Om R) (tightCore R),
      TwinSecXg.twinJoin_le_centralizer hz, ?_, TwinSecXg.twinJoin_isPGroup hΩ hJ2 hz, ?_⟩
    · refine ⟨fun x hx g' => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact TwinSecXg.twinJoin_normalized hΩ hz (g' : Y) g'.2 (x : Y) hx
    · have hKle : tightCore R ≤ TwinSecXg.twinJoin (Om R) (tightCore R) :=
        fun x hx => TwinSecXg.le_twinJoin hK hx
      have hK'le : K' ≤ TwinSecXg.twinJoin (Om R) (tightCore R) :=
        fun x hx => TwinSecXg.le_twinJoin hc.std.hK' hx
      exact sup_le hKle hK'le hd.hu
  have h2 : oddCoreIn (Subgroup.centralizer ({u} : Set Y)) ≤
      oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
    TwinPerpV3.oddCoreIn_le_oddCoreIn_of_le
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2) hut hcomm hPo2
  have hcj : conjSub g (oddCoreIn (Subgroup.centralizer ({t} : Set Y))) ≤
      oddCoreIn (Subgroup.centralizer ({u * e} : Set Y)) := by
    have := conj_oddCoreIn_le (a := t) g
    rwa [hd.hgt] at this
  have hle1 : conjSub g (oddCoreIn (Subgroup.centralizer ({t} : Set Y))) ≤
      oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := hcj.trans (hq1.trans h2)
  have hcardc : Nat.card ↥(conjSub g (oddCoreIn (Subgroup.centralizer ({t} : Set Y)))) =
      Nat.card ↥(oddCoreIn (Subgroup.centralizer ({t} : Set Y))) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hle2 : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) ≤
      conjSub g (oddCoreIn (Subgroup.centralizer ({t} : Set Y))) :=
    (Subgroup.eq_of_le_of_card_ge hle1 hcardc.ge).ge
  have h1 : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) ≤
      oddCoreIn (Subgroup.centralizer ({u} : Set Y)) :=
    hle2.trans (hcj.trans hq1)
  have heq : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) =
      oddCoreIn (Subgroup.centralizer ({u} : Set Y)) := le_antisymm h1 h2
  set N : Subgroup Y := oddCoreIn (Subgroup.centralizer ({t} : Set Y)) with hN
  have hnorm_of : ∀ x : Y, (∀ y ∈ N, x * y * x⁻¹ ∈ N) → (∀ y ∈ N, x⁻¹ * y * x ∈ N) →
      x ∈ Subgroup.normalizer (N : Set Y) := by
    intro x h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => h1 h hh, fun hh => ?_⟩
    have := h2 _ hh
    simpa [mul_assoc] using this
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := fun x hx =>
    hnorm_of x (fun y hy => conj_mem_oddCoreIn hx hy)
      (fun y hy => by
        have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hx) hy
        simpa using this)
  have hCu : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := fun x hx =>
    hnorm_of x (fun y hy => by rw [heq] at hy ⊢; exact conj_mem_oddCoreIn hx hy)
      (fun y hy => by
        rw [heq] at hy ⊢
        have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hx) hy
        simpa using this)
  have htop : Subgroup.normalizer (N : Set Y) = ⊤ := by
    rw [eq_top_iff, ← hTwo]
    exact sup_le hCu hCt
  have hNn : N.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hle : N ≤ classicalInvolutionOddCore Y := le_sSup ⟨hNn, odd_card_oddCoreIn _⟩
  rw [hC.oddFree] at hle
  exact TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn (le_bot_iff.mp hle)

end U30

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
