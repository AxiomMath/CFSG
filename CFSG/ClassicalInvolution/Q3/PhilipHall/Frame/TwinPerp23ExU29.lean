module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU28
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU27

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

section U29

open CFSG.ClassicalInvolution.Q8P.P24 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem ue_comm_u (hc : P23Cfg n Y R S t K' W u e g) :
    u * e ∈ Subgroup.centralizer ({u} : Set Y) := by
  have cue : u * e = e * u := T7K.comm_e_of_mem_W hc.data hc.data.huW
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc u * e * u = u * (e * u) := by group
    _ = u * (u * e) := by rw [← cue]

theorem ue_sq (hc : P23Cfg n Y R S t K' W u e g) : (u * e) * (u * e) = 1 := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  rw [← hc.data.hgt]
  calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    _ = 1 := by rw [hz.sq]; group

theorem ue_ne_one (hc : P23Cfg n Y R S t K' W u e g) : u * e ≠ 1 := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  intro h
  rw [← hc.data.hgt] at h
  apply hz.ne_one
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = g⁻¹ * 1 * g := by rw [h]
    _ = 1 := by group

theorem p23_movedOddFree_ue (hD4 : ModelFactD42) (hT : TwinThmE.T4Supply) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) :
    MovedOddFreeAt u (u * e) (ue_comm_u hc) := by
  have hC := CoreData.of_S hc.std.perp.core
  haveI : CFSG.ClassicalInvolution.Q8P.Asc77.CoreLike Y := CFSG.ClassicalInvolution.Q8P.coreLike_of_core hC
  have hst := CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC
  have hEIH : TwinThmE.EIHAll (Nat.card Y) := by
    rw [hC.card]; intros; exact ⟨hcit, hP⟩
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  exact movedOddFreeAt_of_outAt hst hEIH h2 (p23_innerHyp_u hc)
    (twinInnerOutAt_of_perp modelFactSp62 hD4 (hT n hcit hP) hc.std.perp) (ue_comm_u hc)

theorem conj_oddCoreIn_le {a : Y} (g : Y) :
    conjSub g (oddCoreIn (Subgroup.centralizer ({a} : Set Y))) ≤
      oddCoreIn (Subgroup.centralizer ({g * a * g⁻¹} : Set Y)) := by
  refine le_oddCoreIn_of_normalizes ?_ ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    have hya : y ∈ Subgroup.centralizer ({a} : Set Y) := oddCoreIn_le _ hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hya ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [hya]
      _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
  · intro x hx
    have key : ∀ x ∈ Subgroup.centralizer ({g * a * g⁻¹} : Set Y),
        ∀ y ∈ conjSub g (oddCoreIn (Subgroup.centralizer ({a} : Set Y))),
        x * y * x⁻¹ ∈ conjSub g (oddCoreIn (Subgroup.centralizer ({a} : Set Y))) := by
      intro x hx y hy
      have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({a} : Set Y) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [hx]
          _ = a * (g⁻¹ * x * g) := by group
      rw [mem_conjSub_iff] at hy ⊢
      have := conj_mem_oddCoreIn hx' hy
      convert this using 1
      group
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key x hx y hy, fun hy => ?_⟩
    have := key x⁻¹ (Subgroup.inv_mem _ hx) _ hy
    simpa [mul_assoc] using this
  · have : Nat.card ↥(conjSub g (oddCoreIn (Subgroup.centralizer ({a} : Set Y)))) =
        Nat.card ↥(oddCoreIn (Subgroup.centralizer ({a} : Set Y))) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [this]
    exact odd_card_oddCoreIn _

end U29
