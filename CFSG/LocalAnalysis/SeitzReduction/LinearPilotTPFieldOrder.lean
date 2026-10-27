module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRecenterCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.RankThree.PartOne (linearSubfieldInclusion linearSubfieldInclusion_injective)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (fixedField)

theorem card_eq_of_map_eq {A B Γ : Type*} [Group A] [Group B] [Group Γ] {φ₁ : A →* Γ}
    {φ₂ : B →* Γ} (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    {X : Subgroup A} {Y : Subgroup B} (hXY : X.map φ₁ = Y.map φ₂) : Nat.card X = Nat.card Y := by
  rw [← Subgroup.card_map_of_injective hφ₁, hXY, Subgroup.card_map_of_injective hφ₂]

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem card_perfectCore_fieldAut {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : σ ^ 2 = 1) :
    Nat.card (perfectCore (autFixSubgroup (fieldAut n K σ))) =
      Nat.card (projectiveSL n (fixedField K σ)) := by
  rw [perfectCore_autFixSubgroup_fieldAut hK hn σ hσ]
  exact Nat.card_congr
    (MonoidHom.ofInjective (linearSubfieldInclusion_injective (by omega) _)).toEquiv.symm

theorem card_sylow_perfectCore_fieldAut {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : σ ^ 2 = 1) (S : Sylow 2 (perfectCore (autFixSubgroup (fieldAut n K σ)))) :
    Nat.card S = Nat.card (fixedField K σ) ^ (n * (n - 1) / 2) := by
  have := charP_two_of_card_eq_two_pow hK
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := fixedField K σ) 2 (by omega : 1 ≤ n)
  rw [Sylow.card_eq_multiplicity, card_perfectCore_fieldAut hK hn hσ,
    ← Sylow.card_eq_multiplicity U₀, hU₀, card_projUnitriangular]

theorem map_perfectCore_fieldAut_ne_of_card_ne {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : σ ^ 2 = 1) {Γ : Type*} [Group Γ] {φ₁ φ₂ : projectiveSL n K →* Γ}
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂) {Y : Subgroup (projectiveSL n K)}
    (h : Nat.card Y ≠ Nat.card (projectiveSL n (fixedField K σ))) :
    (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠ Y.map φ₂ := fun hXY =>
  h ((card_eq_of_map_eq hφ₁ hφ₂ hXY).symm.trans (card_perfectCore_fieldAut hK hn hσ))

theorem map_perfectCore_fieldAut_ne_of_lt_card {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : σ ^ 2 = 1) {Γ : Type*} [Group Γ] {φ₁ φ₂ : projectiveSL n K →* Γ}
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    {Y T : Subgroup (projectiveSL n K)} (hTY : T ≤ Y) (hT : IsPGroup 2 T)
    (hlt : Nat.card (fixedField K σ) ^ (n * (n - 1) / 2) < Nat.card T) :
    (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠ Y.map φ₂ := by
  intro hXY
  have hcard := card_eq_of_map_eq hφ₁ hφ₂ hXY
  have hT' : IsPGroup 2 (T.subgroupOf Y) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  have h1 : Nat.card T ≤ Nat.card Q := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv]
    exact Subgroup.card_le_of_le hQ
  obtain ⟨S⟩ : Nonempty (Sylow 2 (perfectCore (autFixSubgroup (fieldAut n K σ)))) :=
    inferInstance
  have h2 : Nat.card Q = Nat.card (fixedField K σ) ^ (n * (n - 1) / 2) := by
    rw [Sylow.card_eq_multiplicity, ← hcard, ← Sylow.card_eq_multiplicity S,
      card_sylow_perfectCore_fieldAut hK hn hσ S]
  omega

theorem map_perfectCore_fieldAut_ne_of_not_dvd {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : σ ^ 2 = 1) {Γ : Type*} [Group Γ] {φ₁ φ₂ : projectiveSL n K →* Γ}
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    {Y Z : Subgroup (projectiveSL n K)} (hYZ : Y ≤ Z)
    (hdvd : ¬ Nat.card (fixedField K σ) ^ (n * (n - 1) / 2) ∣ Nat.card Z) :
    (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠ Y.map φ₂ := by
  intro hXY
  apply hdvd
  obtain ⟨S⟩ : Nonempty (Sylow 2 (perfectCore (autFixSubgroup (fieldAut n K σ)))) :=
    inferInstance
  have h1 : Nat.card (fixedField K σ) ^ (n * (n - 1) / 2) ∣
      Nat.card (perfectCore (autFixSubgroup (fieldAut n K σ))) := by
    rw [← card_sylow_perfectCore_fieldAut hK hn hσ S]
    exact Subgroup.card_subgroup_dvd_card _
  rw [card_eq_of_map_eq hφ₁ hφ₂ hXY] at h1
  exact h1.trans (Subgroup.card_dvd_of_le hYZ)

end CFSG.SeitzReduction.LinearPilot
