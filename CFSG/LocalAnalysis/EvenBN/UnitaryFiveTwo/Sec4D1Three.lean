module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4D1Two
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckS

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

@[expose] def Data.X₃WT {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.withT (d.X₃ ⊔ d.W)

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem commutator_S_eq : ⁅d.S, d.S⁆ = d.X₄ ⊔ d.F := by
  rw [Data.S, Data.pull, ← map_commutator, commutator_Ssub_eq_X₄sub_sup_Fsub, Subgroup.map_sup]
  rfl

omit [Finite G] in
theorem conj_mem_commutator_S {g : G} (hg : g ∈ normalizer (d.S : Set G)) {x : G}
    (hx : x ∈ ⁅d.S, d.S⁆) : g * x * g⁻¹ ∈ ⁅d.S, d.S⁆ := by
  have hle : ⁅d.S, d.S⁆ ≤ ⁅d.S, d.S⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    change g * ⁅a, b⁆ * g⁻¹ ∈ ⁅d.S, d.S⁆
    rw [show g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ by
      simp only [commutatorElement_def]
      group]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hg a).1 ha)
      ((mem_normalizer_iff.1 hg b).1 hb)
  exact hle hx

omit [Finite G] in
theorem F_comm_X₄F {f x : G} (hf : f ∈ d.F) (hx : x ∈ d.X₄ ⊔ d.F) : f * x = x * f := by
  have hxA : x ∈ d.A₂ := (sup_le (d.pull_mono X₄sub_le_A₂sub) d.F_le_A₂) hx
  obtain ⟨φ, hφ, rfl⟩ := hf
  obtain ⟨α, hα, rfl⟩ := hxA
  rw [← map_mul, ← map_mul, Fsub_comm_A₂ hα hφ]

theorem normalizer_S_le_normalizer_F :
    normalizer (d.S : Set G) ≤ normalizer (d.F : Set G) := fun g hg => by
  refine mem_normalizer_fintype fun f hf => ?_
  have hfS : f ∈ d.S := d.pull_mono (Fsub_le_A₂sub.trans A₂sub_le_Ssub) hf
  obtain ⟨σ, hσ, hσe⟩ := (mem_normalizer_iff.1 hg f).1 hfS
  have hcomm : ∀ x ∈ d.X₄ ⊔ d.F, g * f * g⁻¹ * x = x * (g * f * g⁻¹) := fun x hx => by
    rw [← commutator_S_eq] at hx
    have hx' := conj_mem_commutator_S (inv_mem hg) hx
    rw [inv_inv, commutator_S_eq] at hx'
    have e := F_comm_X₄F hf hx'
    calc g * f * g⁻¹ * x = g * (f * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * f) * g⁻¹ := by rw [e]
      _ = x * (g * f * g⁻¹) := by group
  refine ⟨σ, mem_Fsub_of_comm_commutator_Ssub hσ fun s hs => d.ι_injective ?_, hσe⟩
  rw [map_mul, map_mul, hσe]
  have hsX : d.ι s ∈ d.pull (X₄sub ⊔ Fsub) := ⟨s, commutator_Ssub_eq_X₄sub_sup_Fsub ▸ hs, rfl⟩
  rw [d.pull_sup] at hsX
  exact hcomm _ hsX

theorem normalizer_S_le_normalizer_A₂ :
    normalizer (d.S : Set G) ≤ normalizer (d.A₂ : Set G) := fun g hg => by
  have hgF := normalizer_S_le_normalizer_F hg
  refine mem_normalizer_fintype fun a ha => ?_
  obtain ⟨σ, hσ, hσe⟩ := (mem_normalizer_iff.1 hg a).1 (d.A₂_le_S ha)
  have hcomm : ∀ f ∈ d.F, g * a * g⁻¹ * f = f * (g * a * g⁻¹) := fun f hf => by
    have hf' : g⁻¹ * f * g ∈ d.F := by
      have := (mem_normalizer_iff.1 (inv_mem hgF) f).1 hf
      rwa [inv_inv] at this
    obtain ⟨φ, hφ, hφe⟩ := hf'
    obtain ⟨α, hα, rfl⟩ := ha
    have e : d.ι α * (g⁻¹ * f * g) = (g⁻¹ * f * g) * d.ι α := by
      rw [← hφe, ← map_mul, ← map_mul, Fsub_comm_A₂ hα hφ]
    calc g * d.ι α * g⁻¹ * f = g * (d.ι α * (g⁻¹ * f * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * f * g) * d.ι α) * g⁻¹ := by rw [e]
      _ = f * (g * d.ι α * g⁻¹) := by group
  refine ⟨σ, mem_A₂sub_of_comm_Fsub hσ fun z hz => d.ι_injective ?_, hσe⟩
  rw [map_mul, map_mul, hσe]
  exact hcomm _ ⟨z, hz, rfl⟩

theorem NHS_le_normalizer_Y
    (h : d.Hyp) :
    normalizer (d.S : Set G) ⊓ d.H ≤ normalizer (d.Y : Set G) := fun _ hg =>
  h.NHA₂_le_normalizer_Y (Subgroup.mem_inf.2
    ⟨normalizer_S_le_normalizer_A₂ (Subgroup.mem_inf.1 hg).1, (Subgroup.mem_inf.1 hg).2⟩)

theorem mem_Z₂_of_mem_F_of_mem_AW
    (h : d.Hyp) {f : G} (hf : f ∈ d.F) (hfk : f ∈ d.AW) :
    f ∈ d.Z₂ := by
  obtain ⟨a, ha, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_AW hfk
  have hwL : w ∈ d.L := by
    rw [show w = a⁻¹ * (a * w) by group]
    exact mul_mem (inv_mem (d.pull_le_L _ ha)) (h.F_le_L hf)
  have hwZ : w ∈ d.ZX₄ := by
    rw [← h.W_inf_H]
    exact Subgroup.mem_inf.2 ⟨hw, h.L_le_H hwL⟩
  rw [Z₂_eq]
  exact Subgroup.mem_inf.2 ⟨hf, mul_mem ha (ZX₄_le_A₁ hwZ)⟩

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem mem_A₁V₂_of_crossed_mem
    (h : d.Hyp) {x : G} (hx : x ∈ d.D₁)
    (hθ : x * d.t * x⁻¹ * d.t ∈ d.Z₂ ⊔ d.W) : x ∈ d.A₁ ⊔ d.V₂ := by
  obtain ⟨g, hg, w, hw, e⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun g hg w hw => h.Y_comm (h.F_le_Y (Z₂_le_F hg)) (d.W_le_Y hw)) hθ
  obtain ⟨v, hv, hvt⟩ := h.exists_V₂_crossed_eq hg
  have hvD := h.V₂_le_D₁ hv
  obtain ⟨w', hw', e'⟩ := h.crossed_mul_mem (Subgroup.mem_inf.1 (inv_mem hvD)).1 (D₁_le_XW hx)
  have hθv : v⁻¹ * d.t * v⁻¹⁻¹ * d.t = g := by rw [inv_inv]; exact hvt
  rw [← e, hθv] at e'
  have hgg : g * g = 1 := h.F_sq (Z₂_le_F hg)
  have hgw : g * w = w * g := h.Y_comm (h.F_le_Y (Z₂_le_F hg)) (d.W_le_Y hw)
  have hk : v⁻¹ * x * d.t * (v⁻¹ * x)⁻¹ * d.t ∈ d.W := by
    rw [e', mul_assoc g w g, ← hgw, ← mul_assoc, hgg, one_mul]
    exact mul_mem hw hw'
  have hAW := (h.crossed_mem_W_iff_of_mem_D₁ (mul_mem (inv_mem hvD) hx)).1 hk
  have := mul_mem (mem_sup_right hv : v ∈ d.A₁ ⊔ d.V₂)
    ((sup_le le_sup_left (h.W_le_V₂.trans le_sup_right) : d.AW ≤ d.A₁ ⊔ d.V₂) hAW)
  rwa [mul_inv_cancel_left] at this

theorem sec4_11_4
    (h : d.Hyp) :
    d.D₁ ⊓ ((normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y) = d.A₁ ⊔ d.V₂ ∧
      normalizer (d.X₃WT : Set G) ⊓ d.D₁ = d.A₁ ⊔ d.V₂ := by
  have hA₁N : d.A₁ ≤ normalizer (d.S : Set G) ⊓ d.H := fun a ha => Subgroup.mem_inf.2
    ⟨(d.S).le_normalizer (d.A₁_le_S ha), h.L_le_H (d.pull_le_L _ ha)⟩
  have hAV : d.A₁ ⊔ d.V₂ ≤ d.D₁ := sup_le h.A₁_le_D₁ h.V₂_le_D₁
  refine ⟨le_antisymm (fun x hx => ?_) (le_inf hAV (sup_le (hA₁N.trans le_sup_left)
    (h.V₂_le_Y.trans le_sup_right))), le_antisymm (fun x hx => ?_) (le_inf ?_ hAV)⟩
  ·
    obtain ⟨hxD, hxNY⟩ := Subgroup.mem_inf.1 hx
    have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.S : Set G) ⊓ d.H) d.Y
      (h.NHS_le_normalizer_Y)
    obtain ⟨n, hn, y, hy, rfl⟩ : x ∈ ((normalizer (d.S : Set G) ⊓ d.H : Subgroup G) :
        Set G) * (d.Y : Set G) := by
      rw [← hset]
      exact hxNY
    refine h.mem_A₁V₂_of_crossed_mem hxD (mem_sup_left (h.mem_Z₂_of_mem_F_of_mem_AW ?_
      (h.conj_t_mul_t_mem_AW (D₁_le_XW hxD))))
    have hnF := normalizer_S_le_normalizer_F (Subgroup.mem_inf.1 hn).1
    have hyF : y * d.t * y⁻¹ * d.t ∈ d.F := by
      have := h.U_crossed_mem_F (h.E₂_le_U (h.Y_eq_E₂ ▸ inv_mem hy))
      rwa [inv_inv] at this
    have hnt : n⁻¹ * d.t = d.t * n⁻¹ :=
      mem_centralizer_singleton_iff.1 (inv_mem (Subgroup.mem_inf.1 hn).2)
    rw [show n * y * d.t * (n * y)⁻¹ * d.t = n * y * d.t * y⁻¹ * (n⁻¹ * d.t) by group, hnt,
      show n * y * d.t * y⁻¹ * (d.t * n⁻¹) = n * (y * d.t * y⁻¹ * d.t) * n⁻¹ by group]
    exact (mem_normalizer_iff.1 hnF _).1 hyF
  ·
    obtain ⟨hxN, hxD⟩ := Subgroup.mem_inf.1 hx
    refine h.mem_A₁V₂_of_crossed_mem hxD ?_
    have hk := h.conj_t_mul_t_mem_AW (D₁_le_XW hxD)
    have hm : x * d.t * x⁻¹ ∈ d.X₃WT := (mem_normalizer_iff.1 hxN _).1 (mem_sup_right
      (mem_zpowers _))
    have hX₃W : d.X₃ ⊔ d.W ≤ d.Z₂ ⊔ d.W := sup_le_sup_right
      (by rw [Z₂_eq_sup]; exact le_sup_left) _
    have htn : ∀ k ∈ d.X₃ ⊔ d.W, d.t * k * d.t ∈ d.X₃ ⊔ d.W := by
      have hle : d.X₃ ⊔ d.W ≤ (d.X₃ ⊔ d.W).comap (MulAut.conj d.t).toMonoidHom := by
        refine sup_le (fun b hb => ?_) fun w hw => ?_
        · change d.t * b * d.t⁻¹ ∈ d.X₃ ⊔ d.W
          rw [← h.t_comm_of_mem_L (d.pull_le_L _ hb), mul_inv_cancel_right]
          exact mem_sup_left hb
        · change d.t * w * d.t⁻¹ ∈ d.X₃ ⊔ d.W
          rw [h.t_inv]
          exact mem_sup_right (h.t_conj_mem_W hw)
      intro k hk
      have := hle hk
      change d.t * k * d.t⁻¹ ∈ d.X₃ ⊔ d.W at this
      rwa [h.t_inv] at this
    rcases (mem_sup_zpowers_iff h.t_mul_t htn).1 hm with hk' | hk'
    · exfalso
      apply h.t_not_mem_AW_of_elem
      have hkAW : x * d.t * x⁻¹ ∈ d.AW :=
        (sup_le_sup_right (d.pull_mono X₃sub_le_A₁sub) _ : d.X₃ ⊔ d.W ≤ d.AW) hk'
      have := h.conj_mem_AW_of_mem_XW_of_elem (inv_mem (D₁_le_XW hxD)) hkAW
      rwa [show x⁻¹ * (x * d.t * x⁻¹) * x⁻¹⁻¹ = d.t by group] at this
    · exact hX₃W hk'
  ·
    refine sup_le (fun a ha => mem_normalizer_fintype fun k hk => ?_)
      fun v hv => mem_normalizer_fintype fun k hk => ?_
    · have hle : d.X₃WT ≤ d.X₃WT.comap (MulAut.conj a).toMonoidHom := by
        refine sup_le (sup_le (fun b hb => ?_) fun w hw => ?_) ?_
        · change a * b * a⁻¹ ∈ d.X₃WT
          have hbA : b ∈ d.A₁ := d.pull_mono X₃sub_le_A₁sub hb
          obtain ⟨α, hα, rfl⟩ := ha
          obtain ⟨β, hβ, rfl⟩ := hbA
          have hc := commutator_mem_ZX₄sub_of_A₁ hα hβ
          rw [show d.ι α * d.ι β * (d.ι α)⁻¹ = d.ι β * d.ι (β⁻¹ * α * β * α⁻¹) by
            simp only [map_mul, map_inv]; group]
          exact mul_mem (mem_sup_left (mem_sup_left hb))
            (mem_sup_left (mem_sup_right (h.ZX₄_le_W ⟨_, hc, rfl⟩)))
        · change a * w * a⁻¹ ∈ d.X₃WT
          rw [h.A₁_comm_W ha hw, mul_inv_cancel_right]
          exact mem_sup_left (mem_sup_right hw)
        · rw [zpowers_le]
          change a * d.t * a⁻¹ ∈ d.X₃WT
          rw [h.t_comm_of_mem_L (d.pull_le_L _ ha), mul_inv_cancel_right]
          exact mem_sup_right (mem_zpowers _)
      exact hle hk
    · have hvY := h.V₂_le_Y hv
      have hle : d.X₃WT ≤ d.X₃WT.comap (MulAut.conj v).toMonoidHom := by
        refine sup_le (sup_le (fun b hb => ?_) fun w hw => ?_) ?_
        · change v * b * v⁻¹ ∈ d.X₃WT
          have hbY : b ∈ d.Y := h.F_le_Y (d.pull_mono (le_sup_right.trans le_sup_left :
            X₃sub ≤ Fsub) hb)
          rw [h.Y_comm hvY hbY, mul_inv_cancel_right]
          exact mem_sup_left (mem_sup_left hb)
        · change v * w * v⁻¹ ∈ d.X₃WT
          rw [h.Y_comm hvY (d.W_le_Y hw), mul_inv_cancel_right]
          exact mem_sup_left (mem_sup_right hw)
        · rw [zpowers_le]
          change v * d.t * v⁻¹ ∈ d.X₃WT
          have hz := h.crossed_mem_Z₂_of_mem_V₂ hv
          rw [show v * d.t * v⁻¹ = (v⁻¹ * d.t * v * d.t) * d.t by
            rw [inv_eq_of_mul_eq_one_right (h.Y_sq hvY), mul_assoc _ d.t d.t, h.t_mul_t,
              mul_one]]
          rw [Z₂_eq_sup] at hz
          refine mul_mem (mem_sup_left ((sup_le_sup_left h.ZX₄_le_W _) hz))
            (mem_sup_right (mem_zpowers _))
      exact hle hk

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
