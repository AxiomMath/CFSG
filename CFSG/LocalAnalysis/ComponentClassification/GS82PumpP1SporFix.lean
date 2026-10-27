module

public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.GH74.Generic.S45.LSporMathB
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.S45.LSporJ3
public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.GS82PumpInputs.SporFix

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (transportAut transportAut_mul_self
  fixSubTransportEquiv)

theorem mul_self_and_ne_one {S : Type} [Group S] {σ : MulAut S} (hσ : orderOf σ = 2) :
    σ * σ = 1 ∧ σ ≠ 1 := by
  refine ⟨by rw [← sq, ← hσ, pow_orderOf_eq_one], ?_⟩
  rintro rfl
  rw [orderOf_one] at hσ
  exact absurd hσ (by norm_num)

theorem card_fixedSubgroup_eq {S T : Type} [Group S] [Group T] (e : S ≃* T) (σ : MulAut S) :
    Nat.card (fixedSubgroup σ) = Nat.card {x : T // (MulAut.congr e σ) x = x} := by
  rw [show Nat.card (fixedSubgroup σ) = Nat.card ↥(CFSG.GH74.Uniqueness.Bender.autFixed σ)
      from rfl, ← CFSG.GH74.Generic.S45.card_fixed_congr' e σ]

theorem congr_mul_self_and_ne_one {S T : Type} [Group S] [Group T] (e : S ≃* T) {σ : MulAut S}
    (hσ : orderOf σ = 2) :
    MulAut.congr e σ * MulAut.congr e σ = 1 ∧ MulAut.congr e σ ≠ 1 := by
  obtain ⟨h2, h1⟩ := mul_self_and_ne_one hσ
  refine ⟨by rw [← map_mul, h2, map_one], fun h => h1 ?_⟩
  exact (MulAut.congr e).injective (by rw [map_one]; exact h)

section M22

theorem card_fixedSubgroup_m22 {S : Type} [Group S] (e : S ≃* NativeSporadic.M22)
    {σ : MulAut S} (hσ : orderOf σ = 2) :
    Nat.card (fixedSubgroup σ) = 384 ∨ Nat.card (fixedSubgroup σ) = 320 ∨
      Nat.card (fixedSubgroup σ) = 1344 := by
  obtain ⟨h2, h1⟩ := congr_mul_self_and_ne_one e hσ
  rw [card_fixedSubgroup_eq e]
  exact CFSG.GH74.Generic.S45.m22_fixed_card _ h2 h1

end M22

section M23

theorem card_fixedSubgroup_m23 {S : Type} [Group S] (e : S ≃* NativeSporadic.M23)
    {σ : MulAut S} (hσ : orderOf σ = 2) : Nat.card (fixedSubgroup σ) = 2688 := by
  obtain ⟨h2, h1⟩ := congr_mul_self_and_ne_one e hσ
  rw [card_fixedSubgroup_eq e]
  exact CFSG.GH74.Generic.S45.LAlt.m23_fixed_card _ h2 h1

end M23

section M24

theorem card_fixedSubgroup_m24 {S : Type} [Group S] (e : S ≃* NativeSporadic.M24)
    {σ : MulAut S} (hσ : orderOf σ = 2) :
    Nat.card (fixedSubgroup σ) = 21504 ∨ Nat.card (fixedSubgroup σ) = 7680 := by
  obtain ⟨h2, h1⟩ := congr_mul_self_and_ne_one e hσ
  rw [card_fixedSubgroup_eq e]
  exact CFSG.GH74.Generic.S45.LAlt.m24_fixed_card _ h2 h1

end M24

section J2

theorem card_fixedSubgroup_j2 {S : Type} [Group S] (e : S ≃* NativeSporadic.J2)
    {σ : MulAut S} (hσ : orderOf σ = 2) :
    Nat.card (fixedSubgroup σ) = 240 ∨ Nat.card (fixedSubgroup σ) = 336 ∨
      Nat.card (fixedSubgroup σ) = 1920 := by
  set θ := e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have hc : Nat.card (fixedSubgroup σ) =
      Nat.card (CFSG.Sporadic.Schreier.fixSub (transportAut θ σ)) :=
    Nat.card_congr ((MulEquiv.subgroupCongr
      (SeitzReduction.SporadicRefine.fixedSubgroup_eq_fixSub' σ)).trans
      (fixSubTransportEquiv θ σ)).toEquiv
  rw [hc]
  exact CFSG.QuasithinUnique.Id2519.Tab.j2_fixSub_card (transportAut θ σ)
    (transportAut_mul_self θ (mul_self_and_ne_one hσ).1)
    (SeitzReduction.SporadicRefine.transportAut_ne_one θ hσ)

end J2

section J1

theorem exists_conj_of_equiv {Y T : Type} [Group Y] [Group T] (e : Y ≃* T)
    (h : ∀ φ : MulAut T, ∃ g : T, φ = MulAut.conj g) (α : MulAut Y) :
    ∃ t : Y, α = MulAut.conj t := by
  obtain ⟨g, hg⟩ := h (MulAut.congr e α)
  refine ⟨e.symm g, ?_⟩
  ext y
  have h1 := congrArg (fun φ : MulAut T => e.symm (φ (e y))) hg
  simpa [MulAut.congr_apply] using h1

theorem card_fixedSubgroup_j1 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.J1) {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P) : Nat.card (fixedSubgroup σ) = 120 := by
  obtain ⟨t, ht⟩ := exists_conj_of_equiv e Sporadic.Schreier.at_j1_schreier.2.1 σ
  obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
  have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
    rw [ht]
    ext x
    rw [mem_centralizer_singleton_iff]
    change t * x * t⁻¹ = x ↔ x * t = t * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  rw [hfix]
  exact (Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free ⟨e⟩ t ht2).1

end J1

end CFSG.ComponentClassification.GS82PumpInputs.SporFix
