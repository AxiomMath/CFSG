module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Dat
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1PtsB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Stab

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_mem_zpowers_conj (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x a : G}
    (hx : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) :
    x * a * x⁻¹ ∈ zpowers z ↔ a ∈ zpowers z := by
  have hcommz : Commute x z := by
    rw [commute_iff_eq]
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [y7a_fix_z h hx]
  have hcomm_inv : Commute x⁻¹ z := hcommz.inv_left
  constructor
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hae : a = x⁻¹ * z ^ k * x := by
      calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
        _ = x⁻¹ * z ^ k * x := by rw [← hk]
    rw [hae]
    rw [(hcomm_inv.zpow_right k).eq, mul_assoc, inv_mul_cancel, mul_one]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hk]
    rw [(hcommz.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem y7a_S_iff (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {w : G} :
    w ∈ y7aS A V t ↔ ∃ a ∈ A, a ^ 2 = 1 ∧ a ∉ zpowers z ∧ ∃ v ∈ V, w = a * t * v := by
  constructor
  · intro hw
    simp only [y7aS, Set.mem_setOf_eq] at hw
    obtain ⟨⟨a, ha, ha2, v, hv, rfl⟩, hnot⟩ := hw
    refine ⟨a, ha, ha2, ?_, v, hv, rfl⟩
    intro haz
    have hcomm : Commute a t := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp haz
      exact (show Commute z t from h.cfg.t_cent z (y7a_z_mem_A h)).zpow_left k
    have heq : t⁻¹ * (a * t * v) = a * v := by
      rw [hcomm.eq]; group
    apply hnot
    rw [heq]
    exact V.mul_mem (Subgroup.zpowers_le.mpr (y7a_z_mem_V h) haz) hv
  · rintro ⟨a, ha, ha2, haz, v, hv, rfl⟩
    simp only [y7aS, Set.mem_setOf_eq]
    refine ⟨⟨a, ha, ha2, v, hv, rfl⟩, ?_⟩
    intro hmem
    have hcomm : Commute a t := h.cfg.t_cent a ha
    have heq : t⁻¹ * (a * t * v) = a * v := by
      rw [hcomm.eq]; group
    rw [heq] at hmem
    apply haz
    have haV : a ∈ V := by
      have hae : a = (a * v) * v⁻¹ := by group
      rw [hae]
      exact V.mul_mem hmem (V.inv_mem hv)
    have hazA : a ∈ A ⊓ V := ⟨ha, haV⟩
    rwa [y7a_A_inf_V h] at hazA

theorem y7a_S_sub (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ w ∈ y7aS A V t, w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V := by
  intro w hw
  simp only [y7aS, Set.mem_setOf_eq] at hw
  exact y7a_Up_sub h w hw.1

theorem y7a_S_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ w ∈ y7aS A V t, ∀ v ∈ V, w * v ∈ y7aS A V t := by
  intro w hw v hv
  obtain ⟨a, ha, ha2, haz, v₀, hv₀, rfl⟩ := (y7a_S_iff h).mp hw
  exact (y7a_S_iff h).mpr ⟨a, ha, ha2, haz, v₀ * v, mul_mem hv₀ hv, by group⟩

theorem y7a_S_card [Finite G] (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    Nat.card ↥(y7aS A V t) = 9 * Nat.card ↥V := by
  classical
  have hTsub : ({w : G | t⁻¹ * w ∈ V} : Set G) ⊆ (y6Up A V t : Set G) := by
    intro w hw
    exact ⟨1, one_mem A, by simp, t⁻¹ * w, hw, by group⟩
  have hTeq : Nat.card ↥{w : G | t⁻¹ * w ∈ V} = Nat.card ↥V := by
    refine Nat.card_congr ?_
    refine ⟨fun w => ⟨t⁻¹ * w.1, w.2⟩, fun v => ⟨t * v.1, ?_⟩, ?_, ?_⟩
    · show t⁻¹ * (t * v.1) ∈ V
      rw [← mul_assoc, inv_mul_cancel, one_mul]
      exact v.2
    · intro w; ext; group
    · intro v; ext; group
  have hSeq : y7aS A V t = (y6Up A V t : Set G) \ {w : G | t⁻¹ * w ∈ V} := by
    ext w; simp only [y7aS, y6Up, Set.mem_setOf_eq, Set.mem_diff]
  have hsplit : (y7aS A V t).ncard =
      (y6Up A V t : Set G).ncard - ({w : G | t⁻¹ * w ∈ V} : Set G).ncard := by
    rw [hSeq, Set.ncard_sdiff hTsub]
  have hUpn : (y6Up A V t : Set G).ncard = 10 * Nat.card ↥V := by
    rw [← Nat.card_coe_set_eq]; exact y7a_card_Up h
  have hTn : ({w : G | t⁻¹ * w ∈ V} : Set G).ncard = Nat.card ↥V := by
    rw [← Nat.card_coe_set_eq]; exact hTeq
  rw [Nat.card_coe_set_eq (y7aS A V t), hsplit, hUpn, hTn, y7a_card_V h]

theorem y7a_S_conj (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (hxC1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G))
    (hxV : x ∈ normalizer (V : Set G))
    (hxY : x ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G)) :
    ∀ w ∈ y7aS A V t, x * w * x⁻¹ ∈ y7aS A V t := by
  intro w hw
  obtain ⟨a, ha, ha2, haz, v, hv, rfl⟩ := (y7a_S_iff h).mp hw
  have hxt : x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t :=
    (y7a_mem_NAt_iff h hxC1).mp hxY
  have hxaA : x * a * x⁻¹ ∈ A := (Subgroup.mem_set_normalizer_iff.mp hxA a).mp ha
  have hxvV : x * v * x⁻¹ ∈ V := (Subgroup.mem_set_normalizer_iff.mp hxV v).mp hv
  have hxaI2 : (x * a * x⁻¹) ^ 2 = 1 := by
    have : (x * a * x⁻¹) ^ 2 = x * a ^ 2 * x⁻¹ := by rw [pow_two, pow_two]; group
    rw [this, ha2]; group
  have hconj : x * (a * t * v) * x⁻¹
      = (x * a * x⁻¹) * (x * t * x⁻¹) * (x * v * x⁻¹) := by group
  rcases hxt with hxt | hxt
  · refine (y7a_S_iff h).mpr
      ⟨x * a * x⁻¹, hxaA, hxaI2,
        fun hh => haz ((y7a_mem_zpowers_conj h hxC1).mp hh), x * v * x⁻¹, hxvV, ?_⟩
    calc x * (a * t * v) * x⁻¹ = (x * a * x⁻¹) * (x * t * x⁻¹) * (x * v * x⁻¹) := hconj
      _ = (x * a * x⁻¹) * t * (x * v * x⁻¹) := by rw [hxt]
  · have hza : Commute (x * a * x⁻¹) z :=
      y6q8_z_central h.cfg.rel (x * a * x⁻¹) (by rwa [h.cfg.hA] at hxaA)
    have hza2 : (x * a * x⁻¹ * z) ^ 2 = 1 := by
      calc (x * a * x⁻¹ * z) ^ 2 = (x * a * x⁻¹) ^ 2 * z ^ 2 := hza.mul_pow 2
        _ = 1 := by rw [hxaI2, pow_two, y7a_z_sq h, mul_one]
    have hzaz : x * a * x⁻¹ * z ∉ zpowers z := by
      intro hh
      apply haz
      have hp : x * a * x⁻¹ ∈ zpowers z := by
        have hmem := Subgroup.mul_mem (zpowers z) hh
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers z))
        rwa [show (x * a * x⁻¹ * z) * z⁻¹ = x * a * x⁻¹ by group] at hmem
      exact (y7a_mem_zpowers_conj h hxC1).mp hp
    have hzaA : x * a * x⁻¹ * z ∈ A := A.mul_mem hxaA (y7a_z_mem_A h)
    refine (y7a_S_iff h).mpr
      ⟨x * a * x⁻¹ * z, hzaA, hza2, hzaz, x * v * x⁻¹, hxvV, ?_⟩
    calc x * (a * t * v) * x⁻¹ = (x * a * x⁻¹) * (x * t * x⁻¹) * (x * v * x⁻¹) := hconj
      _ = (x * a * x⁻¹) * (z * t) * (x * v * x⁻¹) := by rw [hxt]
      _ = (x * a * x⁻¹ * z) * t * (x * v * x⁻¹) := by group

end CFSG.OddStandard.HigherRank.YamadaG23
