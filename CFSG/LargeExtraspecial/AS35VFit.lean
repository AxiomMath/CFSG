module

public import CFSG.LargeExtraspecial.AS35VEleven
public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup
open Setting (mem_normalizer_of_conj_le)

namespace AS35V

theorem conj_mem_map_of_characteristic {Γ : Type*} [Group Γ] {H : Subgroup Γ} (C : Subgroup H)
    [hC : C.Characteristic] {p : Γ} (hp : p ∈ normalizer (H : Set Γ)) {x : Γ}
    (hx : x ∈ C.map H.subtype) : p * x * p⁻¹ ∈ C.map H.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := H.normalizerMonoidHom ⟨p, hp⟩
  have h1 : φ y ∈ C := (characteristic_iff_le_comap.mp hC φ) hy
  exact ⟨φ y, h1, rfl⟩

theorem layer_layer_eq_top (K : Type*) [Group K] : CFSG.layer (CFSG.layer K) = ⊤ :=
  CFSG.WholeGroup.layer_layer_eq_top

theorem mul_comm_of_card_le_three {K : Type*} [Group K] [Finite K] (h : Nat.card K ≤ 3)
    (a b : K) : a * b = b * a := by
  have hpos : 0 < Nat.card K := Nat.card_pos
  interval_cases hK : Nat.card K
  · have : Subsingleton K := (Nat.card_eq_one_iff_unique.mp hK).1
    exact Subsingleton.elim _ _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isCyclic_of_prime_card hK
    exact @mul_comm _ (IsCyclic.commGroup.toCommMagma) a b
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have := isCyclic_of_prime_card hK
    exact @mul_comm _ (IsCyclic.commGroup.toCommMagma) a b

theorem layer_eq_bot_of_card_le {K : Type*} [Group K] [Finite K]
    (h : Nat.card (CFSG.layer K) ≤ 3) : CFSG.layer K = ⊥ := by
  refine CFSG.LocalCores.layer_eq_bot_of_forall fun C hC => ?_
  obtain ⟨-, -, a, b, hab⟩ := hC.1
  have hCE := CFSG.LocalCores.component_le_layer hC
  have hC3 : Nat.card C ≤ 3 := (card_le_of_le hCE).trans h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm_of_card_le_three hC3 a b]

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem pCore_two_eq_bot {H : Subgroup S.O} (hN2 : S12NoNormalTwo H) :
    CFSG.pCore 2 H = ⊥ := by
  have hn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hconj : ∀ g : H, ∀ x : S.O, x ∈ (CFSG.pCore 2 H).map H.subtype →
      (g : S.O) * x * (g : S.O)⁻¹ ∈ (CFSG.pCore 2 H).map H.subtype := by
    rintro g _ ⟨y, hy, rfl⟩
    refine ⟨g * y * g⁻¹, hn.conj_mem y hy g, ?_⟩
    simp only [subtype_apply, coe_mul, coe_inv]
  have hQ := hN2 ((CFSG.pCore 2 H).map H.subtype) (map_subtype_le _)
    (CFSG.pCore_isPGroup.map H.subtype) (fun h hh => mem_normalizer_of_conj_le
      (hconj ⟨h, hh⟩) (by simpa using hconj ⟨h, hh⟩⁻¹))
  exact (map_eq_bot_iff_of_injective _ (subtype_injective H)).mp hQ

theorem odd_card_fitting {H : Subgroup S.O} (hN2 : S12NoNormalTwo H) :
    Odd (Nat.card (CFSG.fittingSubgroup H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨P₂⟩ : Nonempty (Sylow 2 (CFSG.fittingSubgroup H)) := inferInstance
  have hle := _root_.Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent 2 P₂
  rw [pCore_two_eq_bot hN2, le_bot_iff,
    map_eq_bot_iff_of_injective _ (subtype_injective _)] at hle
  exact P₂.ne_bot_of_dvd_card h2 hle

theorem fitting_of_fiveEight {τ : S.O} {P : Subgroup S.O}
    (h58 : ∀ Y : Subgroup S.O, Y ≤ S.Mbar → (∀ y ∈ Y, y * τ = τ * y) →
      (∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y) → CFSG.oddCore Y ⊔ CFSG.layer Y = ⊤ → Nat.card Y ≤ 3)
    {H : Subgroup S.O} (hHM : H ≤ S.Mbar) (hHτ : ∀ y ∈ H, y * τ = τ * y)
    (hPH : ∀ p ∈ P, ∀ y ∈ H, p * y * p⁻¹ ∈ H) (hN2 : S12NoNormalTwo H) :
    CFSG.layer H = ⊥ ∧ Odd (Nat.card (CFSG.fittingSubgroup H)) ∧
      Nat.card (CFSG.fittingSubgroup H) ≤ 3 ∧
      CFSG.generalizedFitting H = CFSG.fittingSubgroup H := by
  have hPN : ∀ p ∈ P, p ∈ normalizer (H : Set S.O) := fun p hp =>
    mem_normalizer_of_conj_le (hPH p hp) (hPH p⁻¹ (P.inv_mem hp))
  have hmapM : ∀ C : Subgroup H, C.map H.subtype ≤ S.Mbar := fun C =>
    (map_subtype_le C).trans hHM
  have hmapτ : ∀ C : Subgroup H, ∀ y ∈ C.map H.subtype, y * τ = τ * y := fun C y hy =>
    hHτ y (map_subtype_le C hy)
  have hE : CFSG.layer H = ⊥ := by
    have : (CFSG.layer H).Characteristic := CFSG.LocalCores.layer_characteristic
    let e := (CFSG.layer H).equivMapOfInjective H.subtype (subtype_injective H)
    have hEE : CFSG.layer ((CFSG.layer H).map H.subtype) = ⊤ :=
      CFSG.LocalCores.layer_eq_top_of_surjective (layer_layer_eq_top H) e.toMonoidHom
        e.surjective
    have h3 := h58 _ (hmapM _) (hmapτ _)
      (fun p hp y hy => conj_mem_map_of_characteristic _ (hPN p hp) hy)
      (by rw [hEE, sup_top_eq])
    rw [card_map_of_injective (subtype_injective H)] at h3
    exact layer_eq_bot_of_card_le h3
  have hodd := odd_card_fitting hN2
  have hF3 : Nat.card (CFSG.fittingSubgroup H) ≤ 3 := by
    have hodd' : Odd (Nat.card ((CFSG.fittingSubgroup H).map H.subtype)) := by
      rwa [card_map_of_injective (subtype_injective H)]
    have h3 := h58 _ (hmapM _) (hmapτ _)
      (fun p hp y hy => conj_mem_map_of_characteristic _ (hPN p hp) hy)
      (by rw [oddCore_eq_top_of_odd hodd', top_sup_eq])
    rwa [card_map_of_injective (subtype_injective H)] at h3
  refine ⟨hE, hodd, hF3, ?_⟩
  rw [CFSG.generalizedFitting, hE, sup_bot_eq]

end AS35V

end CFSG.LargeExtraspecial
