module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JTr

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec12J_layerNb_le (V : Subgroup G) : secLayerNb V ≤ secNb V :=
  Subgroup.map_subtype_le _

theorem sec12J_alt2_data [Finite G] {V : Subgroup G} (h : Sec128Alt2 V) :
    ∃ φ : Sec12SL × Sec12SL →* ↥(secNb V), Sec12Act (secNb V).subtype φ ∧
      (MonoidHom.range φ).Normal ∧
      ((MonoidHom.range φ).index = 2 ∨ (MonoidHom.range φ).index = 6) := by
  obtain ⟨h1, hcard⟩ := h
  obtain ⟨e, φ0, hinj0, hrange0, hact0⟩ := sec12_natOmega4_model h1
  have hmem : ∀ p, φ0 p ∈ secNb V := fun p =>
    sec12J_layerNb_le V (hrange0 ▸ MonoidHom.mem_range.mpr ⟨p, rfl⟩)
  let φ : Sec12SL × Sec12SL →* ↥(secNb V) := φ0.codRestrict (secNb V) hmem
  have hcomp : (secNb V).subtype.comp φ = φ0 := MonoidHom.ext fun _ => rfl
  have hφinj : Function.Injective φ := fun a b hab => hinj0 (congrArg Subtype.val hab)
  have hS : Sec12Act (secNb V).subtype φ :=
    sec12Act_of_model (secNb V).subtype φ e hφinj (fun A B w => hact0 A B w)
  have hmap : (MonoidHom.range φ).map (secNb V).subtype = secLayerNb V := by
    rw [← hrange0, ← hcomp, MonoidHom.range_comp]
  have hrange : MonoidHom.range φ = CFSG.layer ↥(secNb V) := by
    apply Subgroup.map_injective (secNb V).subtype_injective
    rw [hmap]
    rfl
  have hnormal : (MonoidHom.range φ).Normal := by
    rw [hrange]
    haveI : (CFSG.layer ↥(secNb V)).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  refine ⟨φ, hS, hnormal, ?_⟩
  have hcE : Nat.card (secLayerNb V) = Nat.card (MonoidHom.range φ) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (secNb V).subtype_injective
  have hmul := Subgroup.card_mul_index (MonoidHom.range φ)
  have hpos : 0 < Nat.card (MonoidHom.range φ) := Nat.card_pos
  rcases hcard with h2 | h6
  · left
    rw [hcE] at h2
    rw [h2] at hmul
    have : Nat.card (MonoidHom.range φ) * (MonoidHom.range φ).index =
        Nat.card (MonoidHom.range φ) * 2 := by rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  · right
    rw [hcE] at h6
    rw [h6] at hmul
    have : Nat.card (MonoidHom.range φ) * (MonoidHom.range φ).index =
        Nat.card (MonoidHom.range φ) * 6 := by rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this

end CFSG.OddStandard.SmallF3.Omega
