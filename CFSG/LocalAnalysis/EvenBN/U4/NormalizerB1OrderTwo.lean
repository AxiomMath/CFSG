module

public import CFSG.LocalAnalysis.EvenBN.U4.NormalizerB1Order

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem map_conj_inv_le_centralizer {G : Type*} [Group G] {t g : G} {Y : Subgroup G}
    (hY : Y ≤ centralizer ({g * t * g⁻¹} : Set G)) :
    Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  have hyt := mem_centralizer_singleton_iff.1 (hY hy)
  rw [mem_centralizer_singleton_iff]
  change g⁻¹ * y * g⁻¹⁻¹ * t = t * (g⁻¹ * y * g⁻¹⁻¹)
  rw [inv_inv]
  calc g⁻¹ * y * g * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * t * g⁻¹) * y) * g := by rw [hyt]
    _ = t * (g⁻¹ * y * g) := by group

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem card_le_of_le_centralizer_conj (hS : Setting h L η t Q T) (g : G) {X : Subgroup G}
    (hXC : X ≤ centralizer ({g * t * g⁻¹} : Set G)) (hX : CFSG.IsElementaryAbelian 2 X) :
    Nat.card X ≤ 2 * (2 ^ f) ^ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX' : CFSG.IsElementaryAbelian 2 (X.map (MulAut.conj g⁻¹).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  have := hS.card_le_of_le_centralizer (map_conj_inv_le_centralizer hXC) hX'
  rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at this

theorem not_sq_dvd_card_of_le_normalizer_of_conj (hS : Setting h L η t Q T) (g : G)
    {X Y : Subgroup G} (hXC : X ≤ centralizer ({g * t * g⁻¹} : Set G))
    (hX : CFSG.IsElementaryAbelian 2 X) (hcard : Nat.card X = 2 * (2 ^ f) ^ 4)
    (hYC : Y ≤ centralizer ({g * t * g⁻¹} : Set G)) (hYX : Y ≤ normalizer (X : Set G)) :
    ¬(2 ^ f + 1) ^ 2 ∣ Nat.card Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hX'e : CFSG.IsElementaryAbelian 2 (X.map φ) := CFSG.IsElementaryAbelian.map _
  have hX'c : Nat.card (X.map φ) = 2 * (2 ^ f) ^ 4 := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  obtain ⟨c, hcC, hc⟩ := hS.exists_conj_eq_B1 (map_conj_inv_le_centralizer hXC) hX'e hX'c
  set ψ := (MulAut.conj c⁻¹).toMonoidHom with hψ
  have hYC' : (Y.map φ).map ψ ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyt := mem_centralizer_singleton_iff.1 (map_conj_inv_le_centralizer hYC hy)
    have hct := mem_centralizer_singleton_iff.1 hcC
    rw [mem_centralizer_singleton_iff]
    change c⁻¹ * y * c⁻¹⁻¹ * t = t * (c⁻¹ * y * c⁻¹⁻¹)
    rw [inv_inv]
    calc c⁻¹ * y * c * t = c⁻¹ * (y * (c * t)) := by group
      _ = c⁻¹ * (y * t * c) := by rw [hct, mul_assoc]
      _ = c⁻¹ * (t * y * c) := by rw [hyt]
      _ = c⁻¹ * (t * c) * (c⁻¹ * y * c) := by group
      _ = c⁻¹ * (c * t) * (c⁻¹ * y * c) := by rw [hct]
      _ = t * (c⁻¹ * y * c) := by group
  have hYN : (Y.map φ).map ψ ≤ normalizer (miyamotoB1 h L η t : Set G) := by
    rw [← hc]
    exact (map_mono ((map_mono hYX).trans (le_normalizer_map φ))).trans (le_normalizer_map ψ)
  have hcardY : Nat.card ((Y.map φ).map ψ) = Nat.card Y := by
    rw [card_map_of_injective (MulAut.conj c⁻¹).injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
  intro hdvd
  apply hS.not_sq_dvd_card_normalizer_B1_inf_C
  rw [← hcardY] at hdvd
  exact hdvd.trans (card_dvd_of_le (le_inf hYN hYC'))

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
