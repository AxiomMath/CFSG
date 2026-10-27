module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalSubfield
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalDescent

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.Quasithin (perfectCore)

section Normalize

variable {n : ℕ} {K F : Type} [Field K] [Finite K] [Field F] [Finite F]

omit [Finite K] in
theorem natCard_eq_two_pow_of_fixedField {f : ℕ} (hK : Nat.card K = 2 ^ f) (ι : K →+* F)
    {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nat.card F = 2 ^ (2 * f) := by
  have hσ2 : σ ^ 2 = 1 := by rw [sq, hσσ]
  rw [CatalogueBHigherLinearField.fixedField_card_square F σ hσ2 hσ1]
  have hfixcard : Nat.card (CatalogueBHigherLinearField.fixedField F σ) = Nat.card K := by
    rw [← Nat.card_range_of_injective ι.injective]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (CatalogueBHigherLinearField.mem_fixedField F σ x).trans (hfix x))
  rw [hfixcard, hK, ← pow_mul, mul_comm]

theorem exists_mulEquiv_projMap_eq_of_isComponent (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {M : Type} [Group M]
    (ψ₀ : M ≃* projectiveSL n F) {θ : MulAut M} (hθ : θ * θ = 1) (ε : projectiveSL n K →* M)
    (hε : Function.Injective ε) (hεθ : ε.range ≤ fixedSubgroup θ)
    (hcomp : IsComponent (ε.range.subgroupOf (fixedSubgroup θ))) :
    ∃ ψ : M ≃* projectiveSL n F, (∀ x, ψ (ε x) = projMap n ι x) ∧
      ∀ y, ψ (θ y) = fieldAut n F σ (ψ y) := by
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hK ι hσ1 hσσ hfix
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite M := Finite.of_equiv _ ψ₀.symm.toEquiv
  have hσι : ∀ c, σ (ι c) = ι c := fun c => (hfix _).mpr ⟨c, rfl⟩
  set β₀ := MulAut.congr ψ₀ θ with hβ₀def
  have hβ₀ : β₀ * β₀ = 1 := by rw [hβ₀def, ← map_mul, hθ, map_one]
  set Fx := fixedSubgroup θ with hFx
  let eD₀ : projectiveSL n K ≃* ε.range.subgroupOf Fx :=
    (MonoidHom.ofInjective hε).trans (subgroupOfEquivOfLe hεθ).symm
  have hm : LieModel (ε.range.subgroupOf Fx) .PSL n 2 f :=
    lieModel_of_mulEquiv_projectiveSL hn hf hK eD₀.symm
  let Ψ := fixedSubgroupCongrEquiv ψ₀ θ
  obtain ⟨H, hH⟩ := eq_conj_fieldAut_conj_inv_of_isComponent hn hf hF hσ1 hσσ hβ₀
    (CFSG.LocalCores.isComponent_map_mulEquiv Ψ hcomp)
    (LieType.CurtisTits.lieModel_of_mulEquiv
      ((ε.range.subgroupOf Fx).equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hm)
  set ψ₁ : M ≃* projectiveSL n F := ψ₀.trans (conjAut n F H)⁻¹ with hψ₁
  have hψ₁θ : ∀ y, ψ₁ (θ y) = fieldAut n F σ (ψ₁ y) := by
    intro y
    have h1 : ψ₀ (θ y) = β₀ (ψ₀ y) := by
      rw [hβ₀def]
      change ψ₀ (θ y) = ψ₀ (θ (ψ₀.symm (ψ₀ y)))
      rw [MulEquiv.symm_apply_apply]
    calc ψ₁ (θ y) = ((conjAut n F H)⁻¹ * β₀) (ψ₀ y) := by
          rw [hψ₁, MulEquiv.trans_apply, h1]
          rfl
      _ = (fieldAut n F σ * (conjAut n F H)⁻¹) (ψ₀ y) := by
          congr 1
          rw [hH]
          group
      _ = fieldAut n F σ (ψ₁ y) := rfl
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp ε) := ψ₁.injective.comp hε
  have hinj₂ : Function.Injective (projMap n ι) := projMap_injective (by omega) ι
  have hle : (ψ₁.toMonoidHom.comp ε).range ≤ (projMap n ι).range := by
    rw [← perfectCore_fixedSubgroup_fieldAut hn ι hfix]
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
    · rintro _ ⟨x, rfl⟩
      change fieldAut n F σ (ψ₁ (ε x)) = ψ₁ (ε x)
      rw [← hψ₁θ]
      exact congrArg ψ₁ (hεθ ⟨x, rfl⟩)
    · rw [MonoidHom.range_eq_map, ← map_commutator, commutator_projectiveSL_eq_top hn]
  have hrange : (ψ₁.toMonoidHom.comp ε).range = (projMap n ι).range := by
    refine eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj₂).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hinj₁).toEquiv]
  set δ : MulAut (projectiveSL n K) := ((MonoidHom.ofInjective hinj₁).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₂).symm with hδdef
  have hδ : ∀ x, projMap n ι (δ x) = ψ₁ (ε x) := by
    intro x
    have h1 := (MonoidHom.ofInjective hinj₂).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hinj₁ x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hcomm⟩ := exists_mulAut_projMap_comm hn ι hσι δ
  refine ⟨ψ₁.trans δ'⁻¹, fun x => ?_, fun y => ?_⟩
  · rw [MulEquiv.trans_apply, ← hδ, ← hδ']
    exact MulAut.inv_apply_self _ _ _
  · show δ'⁻¹ (ψ₁ (θ y)) = fieldAut n F σ (δ'⁻¹ (ψ₁ y))
    rw [hψ₁θ]
    exact congrArg (fun φ : MulAut (projectiveSL n F) => φ (ψ₁ y)) hcomm.inv_left.eq

end Normalize

end CFSG.SeitzReduction.LinearPilot
