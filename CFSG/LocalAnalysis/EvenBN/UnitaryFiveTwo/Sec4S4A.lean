module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3E

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem S₃_inf_centralizer_commutator_S (h : d.Hyp) :
    d.S₃ ⊓ centralizer ((⁅d.S, d.S⁆ : Subgroup G) : Set G) = d.Y := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxS₃, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxN : x ∈ normalizer (d.R₂ : Set G) := oTwo_le _ (S₃_le_R₃ hxS₃)
    have hθ := h.crossed_mem_of_mem_normalizer_R₂ hxN
    have hS'A₂ : d.X₄ ⊔ d.F ≤ d.A₂ := sup_le (d.pull_mono X₄sub_le_A₂sub) d.F_le_A₂
    obtain ⟨k, hk, v, hv, hkv⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (A := d.X₄ ⊔ d.F) (B := d.V₂)
      (fun k hk v hv => (Y_comm_D₀ (h.V₂_le_Y hv) (h.A₂_le_D₀ (hS'A₂ hk))).symm) hθ
    have hθc : ∀ s ∈ ⁅d.S, d.S⁆, (x * d.t * x⁻¹ * d.t) * s = s * (x * d.t * x⁻¹ * d.t) :=
      fun s hs => by
        have hsA : s ∈ d.A₂ := commutator_S_le_A₂ hs
        have hsL : s ∈ d.L := d.pull_le_L _ (d.A₂_le_S hsA)
        have hts : d.t * s = s * d.t := (h.t_comm_of_mem_L hsL).symm
        have hsx : s * x = x * s := mem_centralizer_iff.1 hxC s hs
        have hxinv : x⁻¹ * s = s * x⁻¹ := by
          calc x⁻¹ * s = x⁻¹ * (s * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * s) * x⁻¹ := by rw [hsx]
            _ = s * x⁻¹ := by group
        calc (x * d.t * x⁻¹ * d.t) * s = x * d.t * x⁻¹ * (d.t * s) := by group
          _ = x * d.t * x⁻¹ * (s * d.t) := by rw [hts]
          _ = x * d.t * (x⁻¹ * s) * d.t := by group
          _ = x * d.t * (s * x⁻¹) * d.t := by rw [hxinv]
          _ = x * (d.t * s) * x⁻¹ * d.t := by group
          _ = x * (s * d.t) * x⁻¹ * d.t := by rw [hts]
          _ = (x * s) * d.t * x⁻¹ * d.t := by group
          _ = (s * x) * d.t * x⁻¹ * d.t := by rw [← hsx]
          _ = s * (x * d.t * x⁻¹ * d.t) := by group
    have hkc : ∀ s ∈ ⁅d.S, d.S⁆, k * s = s * k := fun s hs => by
      have hsA : s ∈ d.A₂ := commutator_S_le_A₂ hs
      have hvs : v * s = s * v := Y_comm_D₀ (h.V₂_le_Y hv) (h.A₂_le_D₀ hsA)
      have : (k * s) * v = (s * k) * v := by
        calc (k * s) * v = k * (s * v) := by group
          _ = k * (v * s) := by rw [← hvs]
          _ = (k * v) * s := by group
          _ = (x * d.t * x⁻¹ * d.t) * s := by rw [hkv]
          _ = s * (x * d.t * x⁻¹ * d.t) := hθc s hs
          _ = s * (k * v) := by rw [hkv]
          _ = (s * k) * v := by group
      exact mul_right_cancel this
    have hkF : k ∈ d.F := mem_F_of_comm_commutator_S (d.A₂_le_S (hS'A₂ hk)) hkc
    have hθY : x * d.t * x⁻¹ * d.t ∈ d.Y := by
      rw [← hkv]
      exact mul_mem (h.F_le_Y hkF) (h.V₂_le_Y hv)
    have hxX : x ∈ d.XC₀ := h.R₃_le_XC₀ (S₃_le_R₃ hxS₃)
    have hxNY := h.mem_NHA₂Y_of_crossed_mem hxX hθY
    have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.A₂ : Set G) ⊓ d.H) d.Y
      h.NHA₂_le_normalizer_Y
    obtain ⟨n, hn, y, hy, rfl⟩ : x ∈ ((normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) : Set G) *
        (d.Y : Set G) := by
      rw [← hset]
      exact hxNY
    have hnS₃ : n ∈ d.S₃ := by
      have := mul_mem hxS₃ (inv_mem (h.Y_le_S₃ hy))
      rwa [mul_inv_cancel_right] at this
    have hnS : n ∈ d.S := by
      have : n ∈ d.S₃ ⊓ d.H := Subgroup.mem_inf.2 ⟨hnS₃, hn.2⟩
      rwa [h.S₃_inf_H] at this
    have hnc : ∀ s ∈ ⁅d.S, d.S⁆, n * s = s * n := fun s hs => by
      have hsA : s ∈ d.A₂ := commutator_S_le_A₂ hs
      have hys : y * s = s * y := Y_comm_D₀ hy (h.A₂_le_D₀ hsA)
      have hxs : s * (n * y) = (n * y) * s := mem_centralizer_iff.1 hxC s hs
      have : (n * s) * y = (s * n) * y := by
        calc (n * s) * y = n * (s * y) := by group
          _ = n * (y * s) := by rw [← hys]
          _ = (n * y) * s := by group
          _ = s * (n * y) := hxs.symm
          _ = (s * n) * y := by group
      exact mul_right_cancel this
    exact mul_mem (h.F_le_Y (mem_F_of_comm_commutator_S hnS hnc)) hy
  · exact fun y hy => Subgroup.mem_inf.2 ⟨h.Y_le_S₃ hy, mem_centralizer_iff.2 fun s hs =>
      (Y_comm_D₀ hy (h.A₂_le_D₀ (commutator_S_le_A₂ hs))).symm⟩

theorem conj_t_cases {D : Subgroup G} {t : G} (ht : t * t = 1) (htD : ∀ k ∈ D, t * k * t ∈ D)
    {g : G} (hg : g ∈ normalizer ((D ⊔ zpowers t : Subgroup G) : Set G)) :
    g * t * g⁻¹ ∈ D ∨ ∃ e ∈ D, g * t * g⁻¹ = e * t ∧ e * t * e * t = 1 := by
  have hm : g * t * g⁻¹ ∈ D ⊔ zpowers t :=
    (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
  rcases (mem_sup_zpowers_iff ht htD).1 hm with h1 | h1
  · exact Or.inl h1
  · have hett : (g * t * g⁻¹ * t) * t = g * t * g⁻¹ := by rw [mul_assoc _ t t, ht, mul_one]
    refine Or.inr ⟨g * t * g⁻¹ * t, h1, hett.symm, ?_⟩
    calc g * t * g⁻¹ * t * t * (g * t * g⁻¹ * t) * t
        = ((g * t * g⁻¹ * t) * t) * ((g * t * g⁻¹ * t) * t) := by group
      _ = (g * t * g⁻¹) * (g * t * g⁻¹) := by rw [hett]
      _ = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht]; group

theorem crossed_eq_mul_self (h : d.Hyp) {x : G} (hx : x * d.t * x * d.t = 1) :
    x * d.t * x⁻¹ * d.t = x * x := by
  have e1 : d.t * x * d.t = x⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← hx]; group)
  have e2 : d.t * x⁻¹ * d.t = x := by
    calc d.t * x⁻¹ * d.t = d.t * (d.t * x * d.t) * d.t := by rw [e1]
      _ = (d.t * d.t) * x * (d.t * d.t) := by group
      _ = x := by rw [h.t_mul_t]; group
  calc x * d.t * x⁻¹ * d.t = x * (d.t * x⁻¹ * d.t) := by group
    _ = x * x := by rw [e2]

theorem mem_normalizer_withT_of_comm {D : Subgroup G} {t n : G} (hn : n ∈ normalizer (D : Set G))
    (hnt : n * t = t * n) : n ∈ normalizer ((D ⊔ zpowers t : Subgroup G) : Set G) := by
  refine mem_normalizer_sup hn (mem_normalizer_fintype fun x hx => ?_)
  obtain ⟨k, rfl⟩ := hx
  have : n * t * n⁻¹ = t := by rw [hnt, mul_inv_cancel_right]
  rw [← conj_zpow, this]
  exact ⟨k, rfl⟩

theorem t_not_mem_centralizer_Y (h : d.Hyp) : d.t ∉ centralizer (d.Y : Set G) := fun hc => by
  have hYF : d.Y ≤ d.F := fun y hy => (h.mem_F_iff_Y y).2 ⟨hy, mem_centralizer_iff.1 hc y hy⟩
  have := Subgroup.card_le_of_le hYF
  rw [h.card_Y', d.card_F] at this
  omega

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
