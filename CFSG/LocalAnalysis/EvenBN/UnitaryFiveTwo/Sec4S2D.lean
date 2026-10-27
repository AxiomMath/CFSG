module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S2C
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSSeven
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S2Def

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem mem_map_conj_iff {G : Type*} [Group G] (S : Subgroup G) (g x : G) :
    x ∈ S.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ S := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    change g⁻¹ * (g * r * g⁻¹) * g ∈ S
    rwa [show g⁻¹ * (g * r * g⁻¹) * g = r by group]
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by change g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem v_mem_NHA₂ (h : d.Hyp) : d.v ∈ normalizer (d.A₂ : Set G) ⊓ d.H :=
  Subgroup.mem_inf.2 ⟨ι_mem_normalizer_pull
    (mem_normalizer_fintype fun _ ha => vSU_conj_mem_A₂sub ha), h.L_le_H (d.ι_mem vSU)⟩

theorem v_mem_XC₀ (h : d.Hyp) : d.v ∈ d.XC₀ := h.NHA₂_le_XC₀ h.v_mem_NHA₂

theorem crossed_inv_conj_of_mem_H (h : d.Hyp) {g : G} (hg : g ∈ d.H) (x : G) :
    (g⁻¹ * x * g) * d.t * (g⁻¹ * x * g)⁻¹ * d.t = g⁻¹ * (x * d.t * x⁻¹ * d.t) * g := by
  have e2 : g * d.t = d.t * g := mem_centralizer_singleton_iff.1 hg
  have e1 : g * d.t * g⁻¹ = d.t := by rw [e2]; group
  calc (g⁻¹ * x * g) * d.t * (g⁻¹ * x * g)⁻¹ * d.t
      = g⁻¹ * x * (g * d.t * g⁻¹) * x⁻¹ * (g * d.t) := by group
    _ = g⁻¹ * x * d.t * x⁻¹ * (d.t * g) := by rw [e1, e2]
    _ = _ := by group

theorem mem_X₄F_of_mul_mem (h : d.Hyp) {α y : G} (hα : α ∈ d.A₂) (hy : y ∈ d.Y)
    (hαy : α * y ∈ d.X₄ ⊔ d.Y) : α ∈ d.X₄ ⊔ d.F := by
  obtain ⟨a, ha, y', hy', hay⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha y hy => (Y_comm_D₀ hy (h.A₂_le_D₀ (d.pull_mono X₄sub_le_A₂sub ha))).symm) hαy
  have haA : a ∈ d.A₂ := d.pull_mono X₄sub_le_A₂sub ha
  have hα' : α = a * y' * y⁻¹ := by rw [hay]; group
  have hq : a⁻¹ * α = y' * y⁻¹ := by rw [hα']; group
  have hF : a⁻¹ * α ∈ d.F := by
    rw [← h.A₂_inf_Y]
    exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem haA) hα, hq ▸ mul_mem hy' (inv_mem hy)⟩
  rw [show α = a * (a⁻¹ * α) by group]
  exact mul_mem (mem_sup_left ha) (mem_sup_right hF)

theorem mem_F_of_mem_X₄F_of_conj_v (h : d.Hyp) {α : G} (hα : α ∈ d.A₂) (h1 : α ∈ d.X₄ ⊔ d.F)
    (h2 : d.v⁻¹ * α * d.v ∈ d.X₄ ⊔ d.F) : α ∈ d.F := by
  obtain ⟨α₀, hα₀, rfl⟩ := hα
  have h1' : α₀ ∈ X₄sub ⊔ Fsub := by
    have : d.ι α₀ ∈ d.pull (X₄sub ⊔ Fsub) := by
      rw [d.pull_sup]
      exact h1
    exact d.ι_mem_pull_iff.1 this
  have h2' : vSU⁻¹ * α₀ * vSU ∈ X₄sub ⊔ Fsub := by
    have e : d.v⁻¹ * d.ι α₀ * d.v = d.ι (vSU⁻¹ * α₀ * vSU) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [e] at h2
    have : d.ι (vSU⁻¹ * α₀ * vSU) ∈ d.pull (X₄sub ⊔ Fsub) := by
      rw [d.pull_sup]
      exact h2
    exact d.ι_mem_pull_iff.1 this
  rw [← commutator_Ssub_eq_X₄sub_sup_Fsub] at h1' h2'
  have hmem : α₀ ∈ (⁅Ssub, Ssub⁆ : Subgroup SU52) ⊓
      (⁅Ssub, Ssub⁆ : Subgroup SU52).map (MulAut.conj vSU).toMonoidHom :=
    Subgroup.mem_inf.2 ⟨h1', (mem_map_conj_iff _ _ _).2 h2'⟩
  rw [commutator_Ssub_inf_map_vSU] at hmem
  exact d.ι_mem_pull_iff.2 hmem

theorem D₀_le_R₃ (h : d.Hyp) : d.D₀ ≤ d.R₃ := fun x hx =>
  h.mem_R₃_of_mem_D₂_of_crossed_mem (h.D₀_le_D₂ hx)
    (mem_sup_right (h.crossed_mem_Y_of_mem_D₀ hx))

theorem conj_v_mem_D₀ (h : d.Hyp) {x : G} (hx : x ∈ d.D₀) : d.v⁻¹ * x * d.v ∈ d.D₀ := by
  have := (mem_normalizer_iff.1 (inv_mem (h.normalizer_C₀_le_normalizer_D₀ h.v_mem_XC₀)) x).1 hx
  rwa [inv_inv] at this

theorem R₃_inf_conj_inf_D₂ (h : d.Hyp) :
    d.R₃ ⊓ d.R₃.map (MulAut.conj d.v).toMonoidHom ⊓ d.D₂ = d.D₀ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxRRv, hxD⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxR, hxRv⟩ := Subgroup.mem_inf.1 hxRRv
    have hxv : d.v⁻¹ * x * d.v ∈ d.R₃ := (mem_map_conj_iff _ _ _).1 hxRv
    have hvD : d.v⁻¹ * x * d.v ∈ d.D₂ := by
      have := h.conj_mem_D₂ (inv_mem h.v_mem_XC₀) hxD
      rwa [inv_inv] at this
    have hθ1 : x * d.t * x⁻¹ * d.t ∈ d.X₄ ⊔ d.Y := (h.mem_R₃_iff_of_mem_D₂ hxD).1 hxR
    have hθ2 : d.v⁻¹ * (x * d.t * x⁻¹ * d.t) * d.v ∈ d.X₄ ⊔ d.Y := by
      rw [← h.crossed_inv_conj_of_mem_H h.v_mem_NHA₂.2 x]
      exact (h.mem_R₃_iff_of_mem_D₂ hvD).1 hxv
    have hD₀ : x * d.t * x⁻¹ * d.t ∈ d.D₀ := h.crossed_mem_D₀ (D₂_le_XC₀ hxD)
    rw [h.D₀_eq] at hD₀
    obtain ⟨α, hα, e, he, hαe⟩ := (h.mem_A₂E₂_iff).1 hD₀
    have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
    rw [hαe] at hθ1 hθ2
    have hαF1 : α ∈ d.X₄ ⊔ d.F := h.mem_X₄F_of_mul_mem hα heY hθ1
    have hαF2 : d.v⁻¹ * α * d.v ∈ d.X₄ ⊔ d.F := by
      have hvα : d.v⁻¹ * α * d.v ∈ d.A₂ := by
        have := (mem_normalizer_iff.1 (inv_mem h.v_mem_NHA₂.1) α).1 hα
        rwa [inv_inv] at this
      have hvY : d.v⁻¹ * e * d.v ∈ d.Y := by
        have := (mem_normalizer_iff.1 (inv_mem (h.NHA₂_le_normalizer_Y h.v_mem_NHA₂)) e).1 heY
        rwa [inv_inv] at this
      refine h.mem_X₄F_of_mul_mem hvα hvY ?_
      rw [show d.v⁻¹ * α * d.v * (d.v⁻¹ * e * d.v) = d.v⁻¹ * (α * e) * d.v by group]
      exact hθ2
    have hαF : α ∈ d.F := h.mem_F_of_mem_X₄F_of_conj_v hα hαF1 hαF2
    exact h.mem_D₀_of_mem_D₂_of_crossed_mem hxD
      (by rw [hαe]; exact mul_mem (h.F_le_Y hαF) heY)
  · intro x hx
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨h.D₀_le_R₃ hx, ?_⟩, h.D₀_le_D₂ hx⟩
    rw [mem_map_conj_iff]
    exact h.D₀_le_R₃ (h.conj_v_mem_D₀ hx)

theorem D₂_le_centralizer_W (h : d.Hyp) : d.D₂ ≤ centralizer (d.W : Set G) := fun e he =>
  mem_centralizer_iff.2 fun w hw => (mem_D₂_iff.1 he).2 w (d.W_le_Y hw)

theorem S₃_le_S_sup_D₂ (h : d.Hyp) : d.S₃ ≤ d.S ⊔ d.D₂ := by
  intro x hx
  obtain ⟨r, hr, e, he, rfl⟩ := h.exists_eq_mul_of_mem_R₃ (S₃_le_R₃ hx)
  have hSt : ∀ k ∈ d.S, d.t * k * d.t ∈ d.S := fun k hk => by
    have : k * d.t = d.t * k := mem_centralizer_singleton_iff.1 (h.L_le_H (d.pull_le_L _ hk))
    rw [← this, mul_assoc, h.t_mul_t, mul_one]
    exact hk
  rcases (mem_sup_zpowers_iff h.t_mul_t hSt).1 hr with hrS | hrt
  · exact mul_mem (mem_sup_left hrS) (mem_sup_right he)
  · exfalso
    apply h.t_not_mem_centralizer_W
    have hxc : r * e ∈ centralizer (d.W : Set G) := S₃_le_centralizer_W hx
    have hrc : r ∈ centralizer (d.W : Set G) := by
      have := mul_mem hxc (inv_mem (h.D₂_le_centralizer_W he))
      rwa [mul_inv_cancel_right] at this
    have := mul_mem (inv_mem hrc) (S_le_centralizer_W hrt)
    rwa [inv_mul_cancel_left] at this

theorem D₂_le_normalizer_S₃ (h : d.Hyp) : d.D₂ ≤ normalizer (d.S₃ : Set G) := fun u hu =>
  mem_normalizer_fintype fun x hx => by
    obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.1 hx
    have huc := h.D₂_le_centralizer_W hu
    refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (h.D₂_le_normalizer_R₃ hu) x).1 hxR,
      mul_mem (mul_mem huc hxc) (inv_mem huc)⟩

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
