module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Mod

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Pointwise

variable {G : Type} [Group G]

theorem sec122_conj_complement {V B Y Yc W : Subgroup G} {x : G} (hx : x ∈ Yc)
    (hYcV : Yc ≤ normalizer (V : Set G)) (hYcB : Yc ≤ normalizer (B : Set G))
    (hYcY : Yc ≤ normalizer (Y : Set G)) (hWV : W ≤ V) (hWB : W ⊓ B = ⊥)
    (hWsup : ∀ v ∈ V, ∃ w ∈ W, ∃ b ∈ B, v = w * b)
    (hWY : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W) :
    ∃ W' : Subgroup G, (∀ g, g ∈ W' ↔ ∃ w ∈ W, g = x * w * x⁻¹) ∧ W' ≤ V ∧ W' ⊓ B = ⊥ ∧
      (∀ v ∈ V, ∃ w ∈ W', ∃ b ∈ B, v = w * b) ∧
      (∀ y ∈ Y, ∀ w ∈ W', y * w * y⁻¹ ∈ W') := by
  have hVx : ∀ h, h ∈ (V : Set G) ↔ x * h * x⁻¹ ∈ (V : Set G) :=
    Subgroup.mem_set_normalizer_iff.mp (hYcV hx)
  have hVx_inv : ∀ h, h ∈ (V : Set G) ↔ x⁻¹ * h * x ∈ (V : Set G) :=
    Subgroup.mem_set_normalizer_iff''.mp (hYcV hx)
  have hBx : ∀ h, h ∈ (B : Set G) ↔ x * h * x⁻¹ ∈ (B : Set G) :=
    Subgroup.mem_set_normalizer_iff.mp (hYcB hx)
  have hYx_inv : ∀ h, h ∈ (Y : Set G) ↔ x⁻¹ * h * x ∈ (Y : Set G) :=
    Subgroup.mem_set_normalizer_iff''.mp (hYcY hx)
  let W' : Subgroup G := W.map (MulAut.conj x).toMonoidHom
  have hW'mem : ∀ g, g ∈ W' ↔ ∃ w ∈ W, g = x * w * x⁻¹ := by
    intro g
    change g ∈ W.map (MulAut.conj x).toMonoidHom ↔ ∃ w ∈ W, g = x * w * x⁻¹
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    constructor
    · intro hg
      exact ⟨x⁻¹ * g * x, hg, by group⟩
    · rintro ⟨w, hw, rfl⟩
      rwa [show x⁻¹ * (x * w * x⁻¹) * x = w from by group]
  refine ⟨W', hW'mem, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨w, hw, rfl⟩ := (hW'mem g).mp hg
    exact (hVx w).mp (hWV hw)
  · rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgW, hgB⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨w, hw, rfl⟩ := (hW'mem g).mp hgW
    have hwB : w ∈ B := (hBx w).mpr hgB
    have hw1 : w = 1 := by
      have hbot : w ∈ (⊥ : Subgroup G) := by
        rw [← hWB]
        exact ⟨hw, hwB⟩
      simpa using hbot
    rw [hw1]
    group
  · intro v hv
    have hv' : x⁻¹ * v * x ∈ V := (hVx_inv v).mp hv
    obtain ⟨w, hw, b, hb, hvwb⟩ := hWsup (x⁻¹ * v * x) hv'
    refine ⟨x * w * x⁻¹, (hW'mem _).mpr ⟨w, hw, rfl⟩, x * b * x⁻¹, (hBx b).mp hb, ?_⟩
    calc v = x * (x⁻¹ * v * x) * x⁻¹ := by group
      _ = x * (w * b) * x⁻¹ := by rw [hvwb]
      _ = (x * w * x⁻¹) * (x * b * x⁻¹) := by group
  · intro y hy g hg
    obtain ⟨w, hw, rfl⟩ := (hW'mem g).mp hg
    refine (hW'mem _).mpr ⟨(x⁻¹ * y * x) * w * (x⁻¹ * y * x)⁻¹,
      hWY (x⁻¹ * y * x) ((hYx_inv y).mp hy) w hw, ?_⟩
    group

theorem sec122_dichotomy {t : G} {V B Y Yc W : Subgroup G} {φ s : (Fin 5 → ZMod 2) → G}
    (hM : Sec122Mod t V B Y W φ s) {x : G} (hx : x ∈ Yc)
    (hYcV : Yc ≤ normalizer (V : Set G)) (hYcB : Yc ≤ normalizer (B : Set G))
    (hYcY : Yc ≤ normalizer (Y : Set G)) {b₀ : G} (hb₀ : b₀ ∈ B) :
    x ∈ normalizer (W : Set G) ∨ (t * b₀)⁻¹ * x ∈ normalizer (W : Set G) := by
  obtain ⟨W', hW'mem, hW'V, hW'B, hW'sup, hW'Y⟩ :=
    sec122_conj_complement hx hYcV hYcB hYcY hM.W_le_V hM.W_inf_B hM.V_eq_mul hM.W_inv
  rcases sec122_complements hM.comm hM.sq hM.BV hM.perm hM.fB hM.fmul hM.fker hM.sV hM.sadd
      hM.sf hM.sY hW'V hW'B hW'sup hW'Y with hcase | hcase
  · left
    have hW'W : W' = W := by
      ext g
      rw [hcase g, hM.hW g]
    rw [Subgroup.mem_set_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact hW'W ▸ (hW'mem _).mpr ⟨g, hg, rfl⟩
    · intro hg
      have hgW' : x * g * x⁻¹ ∈ W' := hW'W.symm ▸ hg
      obtain ⟨w, hw, heq⟩ := (hW'mem _).mp hgW'
      have hgw : g = w := mul_left_cancel (mul_right_cancel heq)
      rw [hgw]
      exact hw
  · right
    rw [Subgroup.mem_set_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgW' : x * g * x⁻¹ ∈ W' := (hW'mem _).mpr ⟨g, hg, rfl⟩
      obtain ⟨n, hn, hsnφ⟩ := (hcase _).mp hgW'
      have htb : (t * b₀) * s n * (t * b₀)⁻¹ = s n * φ n := hM.tb_conj hb₀ hn
      rw [show ((t * b₀)⁻¹ * x) * g * ((t * b₀)⁻¹ * x)⁻¹
          = (t * b₀)⁻¹ * (x * g * x⁻¹) * (t * b₀) from by group,
        hsnφ, ← htb]
      exact (hM.hW _).mpr ⟨n, hn, by group⟩
    · intro hg
      have hg' : (t * b₀)⁻¹ * (x * g * x⁻¹) * (t * b₀) ∈ W := by
        rw [show (t * b₀)⁻¹ * (x * g * x⁻¹) * (t * b₀)
            = ((t * b₀)⁻¹ * x) * g * ((t * b₀)⁻¹ * x)⁻¹ from by group]
        exact hg
      obtain ⟨n, hn, heq⟩ := (hM.hW _).mp hg'
      have htb : (t * b₀) * s n * (t * b₀)⁻¹ = s n * φ n := hM.tb_conj hb₀ hn
      have hxW' : x * g * x⁻¹ ∈ W' :=
        (hcase _).mpr ⟨n, hn, by rw [← htb, ← heq]; group⟩
      obtain ⟨w, hw, hgw⟩ := (hW'mem _).mp hxW'
      have hgw' : g = w := mul_left_cancel (mul_right_cancel hgw)
      rw [hgw']
      exact hw

theorem sec122_exists_X {t : G} {V B Y Yc A W X0 : Subgroup G} {φ s : (Fin 5 → ZMod 2) → G}
    (hM : Sec122Mod t V B Y W φ s) (hYcV : Yc ≤ normalizer (V : Set G))
    (hYcB : Yc ≤ normalizer (B : Set G)) (hYcY : Yc ≤ normalizer (Y : Set G))
    (hBA : B ≤ A) (hAYc : A ≤ Yc) (htA : t ∈ A)
    (hA : ∀ a ∈ A, a ∈ B ∨ ∃ b ∈ B, a = t * b) (htB : ∀ b ∈ B, t * b = b * t)
    (hX0B : X0 ⊓ B = ⊥) (hX0sup : X0 ⊔ B = Yc) :
    ∃ X : Subgroup G, X ≤ X0 ∧ X ≤ normalizer (W : Set G) ∧ X ⊓ A = ⊥ ∧ X ⊔ A = Yc := by
  have hX0Yc : X0 ≤ Yc := le_trans le_sup_left (le_of_eq hX0sup)
  have hX0N : X0 ≤ normalizer (B : Set G) := le_trans hX0Yc hYcB
  have htX0B : t ∈ (X0 ⊔ B : Subgroup G) := by
    rw [hX0sup]
    exact hAYc htA
  have ht_mul : t ∈ (X0 : Set G) * (B : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right X0 B hX0N]
    exact htX0B
  rw [Set.mem_mul] at ht_mul
  obtain ⟨xt, hxtX0, b, hbB, ht_eq⟩ := ht_mul
  have hxt_eq : xt = t * b⁻¹ := by rw [← ht_eq]; group
  have hbinv : b⁻¹ ∈ B := B.inv_mem hbB
  have hxtN : xt ∉ normalizer (W : Set G) := by
    rw [hxt_eq]
    exact hM.tb_not_mem_normalizer hbinv
  have hXYc : X0 ⊓ normalizer (W : Set G) ≤ Yc := le_trans inf_le_left hX0Yc
  refine ⟨X0 ⊓ normalizer (W : Set G), inf_le_left, inf_le_right, ?_, ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨haX, haA⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨haX0, haN⟩ := Subgroup.mem_inf.mp haX
    rcases hA a haA with haB | ⟨b', hb', rfl⟩
    · have hbot : a ∈ (⊥ : Subgroup G) := by
        rw [← hX0B]
        exact ⟨haX0, haB⟩
      exact hbot
    · have hmemB : (t * b') * xt⁻¹ ∈ B := by
        rw [hxt_eq]
        have h1 : (t * b') * (t * b⁻¹)⁻¹ = b' * b := by
          rw [htB b' hb', htB b⁻¹ hbinv]
          group
        rw [h1]
        exact B.mul_mem hb' hbB
      have hmemX0 : (t * b') * xt⁻¹ ∈ X0 := X0.mul_mem haX0 (X0.inv_mem hxtX0)
      have hbot : (t * b') * xt⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hX0B]
        exact ⟨hmemX0, hmemB⟩
      have hone : (t * b') * xt⁻¹ = 1 := by simpa using hbot
      have hxt_eq' : t * b' = xt := mul_inv_eq_one.mp hone
      exact absurd (hxt_eq' ▸ haN) hxtN
  · refine le_antisymm ?_ ?_
    · exact sup_le hXYc hAYc
    · rw [← hX0sup]
      refine sup_le ?_ ?_
      · intro x hxX0
        have hxYc : x ∈ Yc := hX0Yc hxX0
        rcases sec122_dichotomy hM hxYc hYcV hYcB hYcY hbinv with hxN | hdxN
        · exact le_sup_left (a := X0 ⊓ normalizer (W : Set G)) ⟨hxX0, hxN⟩
        · have hdxX : (t * b⁻¹)⁻¹ * x ∈ X0 ⊓ normalizer (W : Set G) :=
            ⟨hxt_eq ▸ X0.mul_mem (X0.inv_mem hxtX0) hxX0, hdxN⟩
          have hmem : (t * b⁻¹) * ((t * b⁻¹)⁻¹ * x)
              ∈ A ⊔ (X0 ⊓ normalizer (W : Set G)) :=
            Subgroup.mul_mem_sup (A.mul_mem htA (hBA hbinv)) hdxX
          rw [sup_comm A (X0 ⊓ normalizer (W : Set G))] at hmem
          rw [show x = (t * b⁻¹) * ((t * b⁻¹)⁻¹ * x) from by group]
          exact hmem
      · intro b' hb'
        exact le_sup_right (a := X0 ⊓ normalizer (W : Set G)) (hBA hb')

end CFSG.OddStandard.SmallF3.Omega
