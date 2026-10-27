module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AZ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYFrame
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYGrp
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYModel
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Path

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AY

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
open CFSG.ClassicalInvolution.Q3.AE

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem exists_y (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5) :
    ∃ y ∈ rLayer (Om R) u, y * t = t * y ∧ IsPGroup 3 (Subgroup.zpowers y) ∧
      ∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), y * e * y⁻¹ ≠ o * e * o⁻¹ := by
  classical
  obtain ⟨x, vH, v', ψ, p, ι, hvx, hxx, hvH, hzv, hvH2, hψinj, hrange, hψx, hιr, hψv⟩ :=
    frame_psi hc hA5
  obtain ⟨w, hwA, hw3, hwv, hwx, hwxc⟩ := exists_three_elt hιr
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) u) with hN
  have hNodd : Odd (Nat.card N) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull (Om R) u)
  obtain ⟨q, hq⟩ := hrange (mkQ 5 w) (Subgroup.mem_map_of_mem _ hwA)
  have hq3 : q ^ 3 = 1 := hψinj (by rw [map_pow, hq, hw3, map_one])
  have hqv : q * (QuotientGroup.mk vH : ↥(coreHull (Om R) u) ⧸ N) =
      QuotientGroup.mk vH * q :=
    hψinj (by rw [map_mul, map_mul, hq, hψv]; exact hwv)
  have hqx : q * (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) ≠ QuotientGroup.mk x * q := by
    intro h
    apply hwx
    have := congrArg ψ h
    rwa [map_mul, map_mul, hq, hψx] at this
  have hqxc : (q * (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) * q⁻¹) * QuotientGroup.mk x =
      QuotientGroup.mk x * (q * QuotientGroup.mk x * q⁻¹) := by
    apply hψinj
    simp only [map_mul, map_inv, hq]
    rw [hψx]
    exact hwxc
  have hxq : (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) * QuotientGroup.mk x = 1 := by
    rw [← QuotientGroup.mk_mul, hxx, QuotientGroup.mk_one]
  obtain ⟨y₁, hy₁q, hy₁v, a, hy₁a⟩ := exists_pow_three_lift hNodd hvH2 hq3 hqv
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  set y := hcoeHom (Om R) u y₁ with hy
  have hyL : y ∈ rLayer (Om R) u :=
    TwinDisc.coreHull_map_le_rLayer hΩ hc2 ⟨(y₁ : ↥(Subgroup.centralizer ({u} : Set Y))), y₁.2, rfl⟩
  have hyu : y * u = u * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (hcoeHom_mem_centralizer (Om R) u y₁)
  have hyv : y * v' = v' * y := by
    rw [← hvH, hy, ← map_mul, ← map_mul, hy₁v]
  have hyt : y * t = t * y := by
    rcases hzv with ht | ht
    · rw [ht]; exact hyv
    · rw [ht]
      calc y * (u * v') = (y * u) * v' := by group
        _ = (u * y) * v' := by rw [hyu]
        _ = u * (y * v') := by group
        _ = u * (v' * y) := by rw [hyv]
        _ = (u * v') * y := by group
  have hy3 : IsPGroup 3 (Subgroup.zpowers y) := by
    refine isPGroup_zpowers_of_pow_eq_one Nat.prime_three (a := a) ?_
    rw [hy, ← map_pow, hy₁a, map_one]
  refine ⟨y, hyL, hyt, hy3, fun o ho hyo => ?_⟩
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have het : e * t = t * e := hWab _ heW _ hd.hzW
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr het
  have heO : ∀ g ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)),
      e * g * e⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf _ heC) g).mp hg
  have hpow := commutator_pow_card hyu heO ho hyo
  have hpow' : (y₁ * x * y₁⁻¹ * x⁻¹) ^ Nat.card ↥(oddCoreOf (Subgroup.centralizer ({t} : Set Y))) =
      1 := by
    apply hcoeHom_injective (Om R) u
    rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_inv, hvx, map_one]
    exact hpow
  have hq' := congrArg (QuotientGroup.mk' N) hpow'
  simp only [map_pow, map_mul, map_inv, QuotientGroup.mk'_apply, hy₁q] at hq'
  exact commutator_pow_ne_one hxq hqx hqxc (oddCoreOf_odd_natCard _) hq'

theorem p23E8AY_proved : P23E8AY n := by
  intro _ _ Y _ _ R S t K' W u e g hc _ hA5 _
  exact exists_y hc hA5

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AY
