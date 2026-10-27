module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Refl

variable {Y : Type} [Group Y] [Finite Y]

theorem refl_mem {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {W : Subgroup Y} (hW : W ∈ WSet Ω)
    {Rm : Subgroup Y} (hRm : Rm ∈ DSet Ω W) (hRmΩ : Rm ∈ Ω) (hRm2 : IsPGroup 2 ↥Rm)
    {r : Y} (hr : r ∈ Rm) {w : Y} (hw : w ∈ W) : r * w * r⁻¹ * w⁻¹ ∈ Rm ⊓ W := by
  classical
  have hab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hrN : r ∈ Subgroup.normalizer (W : Set Y) := hRm.2 hr
  have hconjW : ∀ x ∈ W, r * x * r⁻¹ ∈ W := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hrN x).mp hx
  have hsyl : IsSylow2In Rm Rm := ⟨le_rfl, hRm2, fun V' hV' _ hKV' => le_antisymm hV' hKV'⟩
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hRmΩ
  have hzW : z ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hRmΩ hRm hsyl hz).2
  let P : Subgroup Y :=
    { carrier := {x | x ∈ W ∧ r * x * r⁻¹ * x⁻¹ ∈ Rm ⊓ W}
      mul_mem' := by
        rintro a b ⟨haW, ha⟩ ⟨hbW, hb⟩
        refine ⟨W.mul_mem haW hbW, ?_⟩
        have hA : r * a * r⁻¹ ∈ W := hconjW a haW
        have hcomm : (r * a * r⁻¹) * (r * b * r⁻¹ * b⁻¹) = (r * b * r⁻¹ * b⁻¹) * (r * a * r⁻¹) :=
          hab _ hA _ hb.2
        have e : r * (a * b) * r⁻¹ * (a * b)⁻¹ =
            (r * b * r⁻¹ * b⁻¹) * (r * a * r⁻¹ * a⁻¹) := by
          calc r * (a * b) * r⁻¹ * (a * b)⁻¹
              = (r * a * r⁻¹) * (r * b * r⁻¹ * b⁻¹) * a⁻¹ := by group
            _ = (r * b * r⁻¹ * b⁻¹) * (r * a * r⁻¹) * a⁻¹ := by rw [hcomm]
            _ = (r * b * r⁻¹ * b⁻¹) * (r * a * r⁻¹ * a⁻¹) := by group
        rw [e]
        exact (Rm ⊓ W).mul_mem hb ha
      one_mem' := ⟨W.one_mem, by simpa using (Rm ⊓ W).one_mem⟩
      inv_mem' := by
        rintro a ⟨haW, ha⟩
        refine ⟨W.inv_mem haW, ?_⟩
        have hA : r * a⁻¹ * r⁻¹ ∈ W := hconjW a⁻¹ (W.inv_mem haW)
        have hcomm : (r * a⁻¹ * r⁻¹) * a = a * (r * a⁻¹ * r⁻¹) := hab _ hA _ haW
        have e : r * a⁻¹ * r⁻¹ * (a⁻¹)⁻¹ = (r * a * r⁻¹ * a⁻¹)⁻¹ := by
          calc r * a⁻¹ * r⁻¹ * (a⁻¹)⁻¹ = (r * a⁻¹ * r⁻¹) * a := by group
            _ = a * (r * a⁻¹ * r⁻¹) := hcomm
            _ = (r * a * r⁻¹ * a⁻¹)⁻¹ := by group
        rw [e]
        exact (Rm ⊓ W).inv_mem ha }
  obtain ⟨η, hη, hWη⟩ := hW
  obtain ⟨S, hηS, -⟩ := hη
  have hUle : ∀ U ∈ η, U ≤ P := by
    intro U hUη x hx
    have hUW : U ≤ W := hWη ▸ le_iSup₂ (f := fun V (_ : V ∈ η) => V) U hUη
    have hxW : x ∈ W := hUW hx
    have hUU : U ∈ USet Ω := (hηS.1 hUη).1
    obtain ⟨R₀, -, J, hJ, hSyl, hUR₀, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hUU
    have hUN : U ≤ Subgroup.normalizer (Rm : Set Y) := by
      by_cases hJR : J = Rm
      · subst hJR
        exact (hUR₀.trans hSyl.1).trans Subgroup.le_normalizer
      · refine Sec6Gen.le_normalizer_of_le_centralizer hΩ hRmΩ hJ (Ne.symm hJR) hz
          (hUR₀.trans hSyl.1) (Sec6Gen.isPGroup_of_mem_USet hΩ hUU) (by omega) ?_
        intro u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hab _ (hUW hu) _ hzW
    refine ⟨hxW, ?_, hconjW x hxW |> fun h => W.mul_mem h (W.inv_mem hxW)⟩
    have hxr : x * r⁻¹ * x⁻¹ ∈ Rm :=
      (Subgroup.mem_normalizer_iff.mp (hUN hx) r⁻¹).mp (Rm.inv_mem hr)
    have : r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
    rw [this]
    exact Rm.mul_mem hr hxr
  have hWP : W ≤ P := by
    rw [hWη]
    exact iSup₂_le fun U hU => hUle U hU
  exact (hWP hw).2

end Refl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
