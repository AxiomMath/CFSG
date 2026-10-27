module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S1C

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer

theorem K₂sub_fixed_a₂Coord {a : SU52} (ha : a ∈ A₂sub)
    (h : ∀ n ∈ K₂sub, a⁻¹ * (n * a * n⁻¹) ∈ Fsub) : a ∈ Fsub := by
  by_contra haF
  obtain ⟨c', hc'0, hc'⟩ : ∃ c' : Fin 2 → F4, c' ≠ 0 ∧ c' ≠ a₂Coord (mat a) := by
    by_cases h1 : a₂Coord (mat a) = ![1, 0]
    · refine ⟨![0, 1], fun e => ?_, fun e => ?_⟩
      · have := congrFun e 1
        simp at this
      · rw [h1] at e
        have := congrFun e 0
        simp at this
    · refine ⟨![1, 0], fun e => ?_, fun e => h1 e.symm⟩
      have := congrFun e 0
      simp at this
  have ha' : nfA₂ c' ∈ A₂sub := nfA₂_mem c'
  have ha'F : nfA₂ c' ∉ Fsub := fun hF => hc'0 (by
    have := (mem_Fsub_iff_a₂Coord ha').1 hF
    rwa [a₂Coord_nfA₂] at this)
  obtain ⟨n, hn, hF⟩ := exists_K₂sub_conj_mem ha haF ha' ha'F
  have e : (nfA₂ c')⁻¹ * a = ((nfA₂ c')⁻¹ * (n * a * n⁻¹)) * (a⁻¹ * (n * a * n⁻¹))⁻¹ := by
    group
  have hF2 : (nfA₂ c')⁻¹ * a ∈ Fsub := by
    rw [e]
    exact mul_mem hF (inv_mem (h n hn))
  have e2 := (inv_mul_mem_Fsub_iff_a₂Coord ha' ha).1 hF2
  rw [a₂Coord_nfA₂] at e2
  exact hc' e2

section Fixed

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}
variable (h : d.Hyp)

theorem fixed_A₂_F (h : d.Hyp) {a : G} (ha : a ∈ d.A₂)
    (hk : ∀ k ∈ d.K₂, a⁻¹ * (k * a * k⁻¹) ∈ d.F) : a ∈ d.F := by
  obtain ⟨α, hα, rfl⟩ := ha
  have key : ∀ n ∈ K₂sub, α⁻¹ * (n * α * n⁻¹) ∈ Fsub := by
    intro n hn
    have hmem := hk (d.ι n) ⟨n, hn, rfl⟩
    have e : d.ι (α⁻¹ * (n * α * n⁻¹)) = (d.ι α)⁻¹ * (d.ι n * d.ι α * (d.ι n)⁻¹) := by
      simp only [map_mul, map_inv]
    rw [← e] at hmem
    exact (d.ι_mem_pull_iff (M := Fsub)).1 hmem
  exact (d.ι_mem_pull_iff (M := Fsub)).2 (K₂sub_fixed_a₂Coord hα key)

theorem K₂_le_NHA₂ (h : d.Hyp) {k : G} (hk : k ∈ d.K₂) :
    k ∈ normalizer (d.A₂ : Set G) ⊓ d.H := by
  obtain ⟨n, hn, rfl⟩ := hk
  exact ⟨ι_mem_normalizer_pull (d := d) (K₂sub_le_normalizer_A₂sub hn), h.L_le_H (d.ι_mem n)⟩

theorem fixed_D₀_Y (h : d.Hyp) {z : G} (hz : z ∈ d.D₀)
    (hk : ∀ k ∈ d.K₂, z⁻¹ * (k * z * k⁻¹) ∈ d.Y) : z ∈ d.Y := by
  rw [h.D₀_eq] at hz
  obtain ⟨a, ha, e, he, rfl⟩ := (h.mem_A₂E₂_iff).1 hz
  have heY : e ∈ d.Y := by
    rw [h.Y_eq_E₂]
    exact he
  have hF : ∀ k ∈ d.K₂, a⁻¹ * (k * a * k⁻¹) ∈ d.F := by
    intro k hkK
    have hkN : k ∈ normalizer (d.A₂ : Set G) ⊓ d.H := h.K₂_le_NHA₂ hkK
    have hcA : a⁻¹ * (k * a * k⁻¹) ∈ d.A₂ :=
      mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (Subgroup.mem_inf.1 hkN).1 a).1 ha)
    have huY : k * e * k⁻¹ ∈ d.Y :=
      (mem_normalizer_iff.1 (h.NHA₂_le_normalizer_Y hkN) e).1 heY
    have hcomm : (a⁻¹ * (k * a * k⁻¹)) * e⁻¹ = e⁻¹ * (a⁻¹ * (k * a * k⁻¹)) :=
      h.Y_comm_A₂ (inv_mem heY) hcA
    have hmem : (a⁻¹ * (k * a * k⁻¹)) * (e⁻¹ * (k * e * k⁻¹)) ∈ d.Y := by
      have e2 : (a⁻¹ * (k * a * k⁻¹)) * (e⁻¹ * (k * e * k⁻¹)) =
          (a * e)⁻¹ * (k * (a * e) * k⁻¹) := by
        calc (a⁻¹ * (k * a * k⁻¹)) * (e⁻¹ * (k * e * k⁻¹))
            = ((a⁻¹ * (k * a * k⁻¹)) * e⁻¹) * (k * e * k⁻¹) := (mul_assoc _ _ _).symm
          _ = (e⁻¹ * (a⁻¹ * (k * a * k⁻¹))) * (k * e * k⁻¹) := by rw [hcomm]
          _ = (a * e)⁻¹ * (k * (a * e) * k⁻¹) := by group
      rw [e2]
      exact hk k hkK
    have hcY : a⁻¹ * (k * a * k⁻¹) ∈ d.Y := by
      have h2 := mul_mem hmem (inv_mem (mul_mem (inv_mem heY) huY))
      rwa [mul_inv_cancel_right] at h2
    rw [← h.A₂_inf_Y]
    exact Subgroup.mem_inf.2 ⟨hcA, hcY⟩
  exact mul_mem (h.F_le_Y (h.fixed_A₂_F ha hF)) heY

theorem fixed_D₂_Y (h : d.Hyp) {x : G} (hx : x ∈ d.D₂)
    (hk : ∀ k ∈ d.K₂, x⁻¹ * (k * x * k⁻¹) ∈ d.Y) : x ∈ d.Y := by
  obtain ⟨h1, -, h3, h4, h5, -, -⟩ := h.sec4_15_2
  have hTD : x * d.t * x⁻¹ * d.t ∈ d.D₀ := h1 x hx
  have hTL : ∀ k ∈ d.K₂,
      (x * d.t * x⁻¹ * d.t)⁻¹ * (k * (x * d.t * x⁻¹ * d.t) * k⁻¹) ∈ d.Y := by
    intro k hkK
    have hkN : k ∈ normalizer (d.A₂ : Set G) ⊓ d.H := h.K₂_le_NHA₂ hkK
    obtain ⟨y, hy⟩ : ∃ y : G, y = x⁻¹ * (k * x * k⁻¹) := ⟨_, rfl⟩
    have hyY : y ∈ d.Y := by
      rw [hy]
      exact hk k hkK
    have hxy : k * x * k⁻¹ = x * y := by
      rw [hy]
      group
    have hθy : y * d.t * y⁻¹ * d.t ∈ d.Y := h.crossed_mem_Y_of_mem_D₀ (Y_le_D₀ hyY)
    obtain ⟨w, hwY, hw⟩ := h4 x hx y (h.Y_le_D₂ hyY)
    have hconj : k * (x * d.t * x⁻¹ * d.t) * k⁻¹ =
        (y * d.t * y⁻¹ * d.t) * (x * d.t * x⁻¹ * d.t) * w := by
      rw [← h5 k hkN x, hxy, hw]
    have hTcomm : (y * d.t * y⁻¹ * d.t) * (x * d.t * x⁻¹ * d.t) =
        (x * d.t * x⁻¹ * d.t) * (y * d.t * y⁻¹ * d.t) :=
      Y_comm_D₀ hθy hTD
    have heq : (x * d.t * x⁻¹ * d.t)⁻¹ * (k * (x * d.t * x⁻¹ * d.t) * k⁻¹) =
        (y * d.t * y⁻¹ * d.t) * w := by
      calc (x * d.t * x⁻¹ * d.t)⁻¹ * (k * (x * d.t * x⁻¹ * d.t) * k⁻¹)
          = (x * d.t * x⁻¹ * d.t)⁻¹ *
              ((y * d.t * y⁻¹ * d.t) * (x * d.t * x⁻¹ * d.t) * w) := by rw [hconj]
        _ = ((x * d.t * x⁻¹ * d.t)⁻¹ * ((y * d.t * y⁻¹ * d.t) * (x * d.t * x⁻¹ * d.t))) * w := by
              group
        _ = ((x * d.t * x⁻¹ * d.t)⁻¹ * ((x * d.t * x⁻¹ * d.t) * (y * d.t * y⁻¹ * d.t))) * w := by
              rw [hTcomm]
        _ = (y * d.t * y⁻¹ * d.t) * w := by group
    rw [heq]
    exact mul_mem hθy hwY
  have hTY : x * d.t * x⁻¹ * d.t ∈ d.Y := h.fixed_D₀_Y hTD hTL
  exact h.fixed_D₀_Y ((h3 x hx).1 hTY) hk

end Data.Hyp

end Fixed

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
