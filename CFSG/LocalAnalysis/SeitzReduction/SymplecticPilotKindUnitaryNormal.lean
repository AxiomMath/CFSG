module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective statedSpCongr spProjEquiv)

section SpAut

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem exists_eq_conj_statedSpMap_of_three_le {r : ℕ} (hr : 3 ≤ r)
    (δ : MulAut (StatedSp r k)) :
    ∃ (s : StatedSp r k) (ρ : k ≃+* k), ∀ g, δ g = s * statedSpMap (ρ : k →+* k) r g * s⁻¹ := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨A, ρ, hA⟩ := (SymplecticHigher.automorphism_generation (K := k) hr).2
    (MulAut.congr (spProjEquiv r k) δ)
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  have hδ : δ = MulAut.conj s * SymplecticHigher.fieldSp r k ρ := by
    apply (MulAut.congr (spProjEquiv r k)).injective
    rw [hA, hs, map_mul, F4Pilot.mulAutCongr_spProjEquiv_conj,
      F4Pilot.mulAutCongr_spProjEquiv_fieldSp]
  refine ⟨s, ρ, fun g => ?_⟩
  rw [hδ, MulAut.mul_apply, MulAut.conj_apply, F4Pilot.fieldSp_eq_statedSpMap]

end SpAut

theorem nonempty_ringEquiv_of_natCard_eq' {A B : Type} [Field A] [Field B] [Finite A] [Finite B]
    (h : Nat.card A = Nat.card B) : Nonempty (A ≃+* B) := by
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  exact ⟨FiniteField.ringEquivOfCardEq (by rwa [← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card])⟩

section Abstract

theorem exists_conj_eq_of_range_eq_fixedSubgroup {k K₀ : Type} [Field k] [Finite k] [CharP k 2]
    [Field K₀] [Finite K₀] {r : ℕ} (hr : 3 ≤ r) (hcard : Nat.card K₀ = Nat.card k)
    {P : Type*} [Group P] {θ : MulAut P} (υ : StatedSp r k →* P) (hυ : Function.Injective υ)
    (hυr : υ.range = fixedSubgroup θ) (ε : StatedSp r K₀ →* P) (hε : Function.Injective ε)
    (hfix : ∀ x, θ (ε x) = ε x) :
    ∃ (y : P) (ι : K₀ ≃+* k), θ y = y ∧
      ∀ x, y * ε x * y⁻¹ = υ (statedSpMap (ι : K₀ →+* k) r x) := by
  obtain ⟨ι₀⟩ := nonempty_ringEquiv_of_natCard_eq' (A := K₀) (B := k) hcard
  have hle : ε.range ≤ υ.range := by
    rw [hυr]
    rintro _ ⟨x, rfl⟩
    exact hfix x
  have : Finite υ.range := Finite.of_surjective _ υ.rangeRestrict_surjective
  have hrange : ε.range = υ.range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hε).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hυ).toEquiv,
      Nat.card_congr (statedSpCongr ι₀ r).toEquiv]
  set δ₀ : StatedSp r K₀ ≃* StatedSp r k :=
    ((MonoidHom.ofInjective hε).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective hυ).symm with hδ₀def
  have hδ₀ : ∀ x, υ (δ₀ x) = ε x := by
    intro x
    have h1 := (MonoidHom.ofInjective hυ).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, ρ, hsρ⟩ := exists_eq_conj_statedSpMap_of_three_le hr
    ((statedSpCongr ι₀ r).symm.trans δ₀)
  have hδ₀' : ∀ x, δ₀ x = s * statedSpMap ((ι₀.trans ρ : K₀ ≃+* k) : K₀ →+* k) r x * s⁻¹ := by
    intro x
    have h1 := hsρ (statedSpCongr ι₀ r x)
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    rw [h1, F4Pilot.coe_statedSpCongr, F4Pilot.statedSpMap_comp]
    rfl
  have hsfix : θ (υ s) = υ s := by
    have : υ s ∈ fixedSubgroup θ := hυr ▸ ⟨s, rfl⟩
    exact this
  refine ⟨(υ s)⁻¹, ι₀.trans ρ, ?_, fun x => ?_⟩
  · rw [map_inv, hsfix]
  · rw [← hδ₀, hδ₀', map_mul, map_mul, map_inv]
    group

end Abstract

end CFSG.SeitzReduction.SymplecticPilot
