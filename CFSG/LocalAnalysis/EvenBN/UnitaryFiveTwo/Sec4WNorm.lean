module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4YNorm

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem ZX₄_le_A₁ : d.ZX₄ ≤ d.A₁ := d.pull_mono (ZX₄sub_le_X₄sub.trans X₄sub_le_A₁sub')

omit [Finite G] in
theorem ZX₄_comm_A₁ {a b : G} (ha : a ∈ d.ZX₄) (hb : b ∈ d.A₁) : a * b = b * a := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  rw [← map_mul, ← map_mul, ZX₄sub_comm hα (A₁sub_le_Ssub hβ)]

omit [Finite G] in
theorem mem_ZX₄_of_central {a : G} (ha : a ∈ d.A₁) (hc : ∀ b ∈ d.A₁, a * b = b * a) :
    a ∈ d.ZX₄ := by
  obtain ⟨α, hα, rfl⟩ := ha
  exact ⟨α, mem_ZX₄sub_of_comm_A₁ fun β hβ => d.ι_injective (by
    rw [map_mul, map_mul]
    exact hc _ ⟨β, hβ, rfl⟩), rfl⟩

omit [Finite G] in
theorem comm_z_of_mem_NHA₁ {g : G} (hg : g ∈ normalizer (d.A₁ : Set G)) :
    g * d.z = d.z * g := by
  have hm : g * d.z * g⁻¹ ∈ d.A₁ := (mem_normalizer_iff.1 hg _).1 (ZX₄_le_A₁ z_mem_ZX₄)
  have hcen : ∀ b ∈ d.A₁, g * d.z * g⁻¹ * b = b * (g * d.z * g⁻¹) := by
    have := conj_central_of_mem_normalizer (inv_mem hg) fun b hb => ZX₄_comm_A₁ z_mem_ZX₄ hb
    simpa using this
  rcases eq_one_or_eq_z (mem_ZX₄_of_central hm hcen) with e | e
  · exfalso
    apply z_ne_one (d := d)
    calc d.z = g⁻¹ * (g * d.z * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  · calc g * d.z = g * d.z * g⁻¹ * g := by group
      _ = d.z * g := by rw [e]

theorem normalizer_ZR_eq_sup
    (h : d.Hyp) :
    normalizer (d.ZR : Set G) = (normalizer (d.A₁ : Set G) ⊓ d.H) ⊔ d.W := by
  refine le_antisymm (fun g hg => ?_) (sup_le (fun g hg => ?_) fun w hw =>
    h.mem_normalizer_ZR_of_mem_W hw)
  · obtain ⟨c, hcH, hcz, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_normalizer_ZR hg
    have hcA : c ∈ normalizer (d.A₁ : Set G) :=
      mem_normalizer_fintype fun a ha => h.conj_mem_A₁_of_comm_z hcH hcz ha
    exact mul_mem (mem_sup_left (Subgroup.mem_inf.2 ⟨hcA, hcH⟩)) (mem_sup_right hw)
  · obtain ⟨hgA, hgH⟩ := Subgroup.mem_inf.1 hg
    exact h.mem_normalizer_ZR_of_comm_z hgH (comm_z_of_mem_NHA₁ hgA)

omit [Finite G] in
theorem ZR_le_withT_A₁ : d.ZR ≤ d.withT d.A₁ := sup_le_sup_right ZX₄_le_A₁ _

theorem withT_A₁_le_centralizer_ZR (h : d.Hyp) :
    d.withT d.A₁ ≤ centralizer (d.ZR : Set G) := by
  have hZH : d.ZR ≤ d.H := sup_le (fun a ha => h.L_le_H (d.pull_le_L _ ha))
    (zpowers_le.2 h.t_mem_H)
  refine sup_le (fun b hb => mem_centralizer_iff.2 fun r hr => ?_)
    (zpowers_le.2 (mem_centralizer_iff.2 fun r hr => mem_centralizer_singleton_iff.1 (hZH hr)))
  have hle : d.ZR ≤ centralizer ({b} : Set G) := sup_le
    (fun a ha => mem_centralizer_singleton_iff.2 (ZX₄_comm_A₁ ha hb))
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 (h.t_comm_of_mem_L (d.pull_le_L _ hb)).symm))
  exact mem_centralizer_singleton_iff.1 (hle hr)

theorem normalizer_withT_A₁_le_normalizer_ZR
    (h : d.Hyp) :
    normalizer ((d.withT d.A₁ : Subgroup G) : Set G) ≤ normalizer (d.ZR : Set G) := by
  intro g hg
  refine mem_normalizer_fintype fun r hr => ?_
  have hm : g * r * g⁻¹ ∈ d.withT d.A₁ := (mem_normalizer_iff.1 hg r).1 (ZR_le_withT_A₁ hr)
  have hcen : ∀ x ∈ d.withT d.A₁, g * r * g⁻¹ * x = x * (g * r * g⁻¹) := by
    have := conj_central_of_mem_normalizer (inv_mem hg) fun x hx =>
      mem_centralizer_iff.1 (h.withT_A₁_le_centralizer_ZR hx) r hr
    simpa using this
  refine h.mem_ZR_of_comm_A₁ (mem_centralizer_singleton_iff.2 ?_) fun a ha =>
    hcen a (mem_sup_left ha)
  exact hcen d.t (mem_sup_right (mem_zpowers _))

theorem normalizer_ZR_le_normalizer_withT_A₁
    (h : d.Hyp) :
    normalizer (d.ZR : Set G) ≤ normalizer ((d.withT d.A₁ : Subgroup G) : Set G) := by
  intro g hg
  have hle : d.withT d.A₁ ≤ (d.withT d.A₁).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun a ha => mem_sup_left (h.conj_mem_A₁_of_mem_normalizer_ZR hg ha)) ?_
    rw [zpowers_le]
    change g * d.t * g⁻¹ ∈ d.withT d.A₁
    have hc := (h.conj_of_mem_normalizer_ZR (inv_mem hg)).1
    rw [inv_inv] at hc
    rw [show g * d.t * g⁻¹ = g * d.t * g⁻¹ * d.t * d.t by
      rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
    exact mul_mem (mem_sup_left (ZX₄_le_A₁ hc)) (mem_sup_right (mem_zpowers _))
  exact mem_normalizer_fintype fun x hx => hle hx

theorem normalizer_ZR_eq_normalizer_withT_A₁
    (h : d.Hyp) :
    normalizer (d.ZR : Set G) = normalizer ((d.withT d.A₁ : Subgroup G) : Set G) :=
  le_antisymm h.normalizer_ZR_le_normalizer_withT_A₁ h.normalizer_withT_A₁_le_normalizer_ZR

theorem ZX₄_le_W
    (h : d.Hyp) :
    d.ZX₄ ≤ d.W := by
  rw [← h.W_inf_H]
  exact inf_le_left

theorem mem_ZX₄_iff_W
    (h : d.Hyp) (v : G) :
    v ∈ d.ZX₄ ↔ v ∈ d.W ∧ v * d.t = d.t * v := by
  rw [← h.W_inf_H, Subgroup.mem_inf, Data.H, mem_centralizer_singleton_iff]

theorem t_conj_mem_W
    (h : d.Hyp) {w : G}
    (hw : w ∈ d.W) : d.t * w * d.t ∈ d.W := by
  rw [show d.t * w * d.t = w * (w⁻¹ * d.t * w * d.t) by group]
  exact mul_mem hw (h.ZX₄_le_W (h.W_crossed_mem_ZX₄ hw))

theorem card_ZR_eq_four
    (h : d.Hyp) : Nat.card d.ZR = 4 := by
  have e := h.card_sup_kernel (X := d.ZX₄) (d.pull_le_L _)
  have h2 : Nat.card d.ZX₄ = 2 := by rw [Data.ZX₄, d.card_pull, card_ZX₄sub]
  rw [h.centralizer_inf_H_eq, h.card_zpowers_t, h2] at e
  exact e

theorem normalizer_ZR_le_normalizer_withT_W
    (h : d.Hyp) :
    normalizer (d.ZR : Set G) ≤ normalizer ((d.withT d.W : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_fintype fun _ hx => h.conj_mem_withT_W hg hx

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem W_sq
    (h : d.Hyp) {w : G}
    (hw : w ∈ d.W) : w * w = 1 :=
  h.Y_sq (d.W_le_Y hw)

theorem le_W_or_le_ZR
    (h : d.Hyp)
    {E : Subgroup G} (hE : E ≤ d.withT d.W) (hsq : ∀ x ∈ E, x * x = 1) :
    E ≤ d.W ∨ E ≤ d.ZR :=
  le_or_le_sup_zpowers_of_elem h.t_mul_t (fun _ hv => h.t_conj_mem_W hv) (fun _ hv => h.W_sq hv)
    h.mem_ZX₄_iff_W hE hsq

theorem normalizer_withT_W_le_normalizer_W
    (h : d.Hyp) :
    normalizer ((d.withT d.W : Subgroup G) : Set G) ≤ normalizer (d.W : Set G) := by
  intro g hg
  have hE : d.W.map (MulAut.conj g).toMonoidHom ≤ d.withT d.W := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 (mem_sup_left hx)
  have hsq : ∀ x ∈ d.W.map (MulAut.conj g).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change g * x * g⁻¹ * (g * x * g⁻¹) = 1
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, h.W_sq hx, mul_one,
      mul_inv_cancel]
  rcases h.le_W_or_le_ZR hE hsq with hle | hle
  · exact mem_normalizer_fintype fun w hw => hle ⟨w, hw, rfl⟩
  · exfalso
    have hEq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h.sec4_9_W.1,
        h.card_ZR_eq_four])
    have ht : d.t ∈ d.W.map (MulAut.conj g).toMonoidHom := by
      rw [hEq]
      exact mem_sup_right (mem_zpowers _)
    obtain ⟨x, hx, hxt⟩ := ht
    apply h.conj_t_not_mem_Y g
    have e : g⁻¹ * d.t * g = x := by
      rw [← hxt]
      change g⁻¹ * (g * x * g⁻¹) * g = x
      group
    rw [e]
    exact d.W_le_Y hx

theorem normalizer_withT_W_le_normalizer_ZR
    (h : d.Hyp) :
    normalizer ((d.withT d.W : Subgroup G) : Set G) ≤ normalizer (d.ZR : Set G) := fun _ hg =>
  mem_normalizer_sup_zpowers_of_elem h.t_mul_t h.t_not_mem_W (fun _ hv => h.t_conj_mem_W hv)
    (fun _ hv => h.W_sq hv) h.mem_ZX₄_iff_W hg (h.normalizer_withT_W_le_normalizer_W hg)

theorem normalizer_withT_W_eq_normalizer_ZR
    (h : d.Hyp) :
    normalizer ((d.withT d.W : Subgroup G) : Set G) = normalizer (d.ZR : Set G) :=
  le_antisymm h.normalizer_withT_W_le_normalizer_ZR h.normalizer_ZR_le_normalizer_withT_W

theorem sec4_9
    (h : d.Hyp) :
    normalizer (d.ZR : Set G) = normalizer ((d.withT d.A₁ : Subgroup G) : Set G) ∧
      normalizer ((d.withT d.A₁ : Subgroup G) : Set G) =
        normalizer ((d.withT d.W : Subgroup G) : Set G) ∧
      normalizer ((d.withT d.W : Subgroup G) : Set G) =
        (normalizer (d.A₁ : Set G) ⊓ d.H) ⊔ d.W ∧
      normalizer ((d.withT d.W : Subgroup G) : Set G) ≤ normalizer (d.W : Set G) ∧
      d.W ⊓ d.H = d.ZX₄ ∧ Nat.card d.W = 4 := by
  have e1 := h.normalizer_ZR_eq_normalizer_withT_A₁
  have e2 := h.normalizer_withT_W_eq_normalizer_ZR
  refine ⟨e1, by rw [← e1, e2], by rw [e2, h.normalizer_ZR_eq_sup],
    h.normalizer_withT_W_le_normalizer_W, h.sec4_9_W.2.1, h.sec4_9_W.1⟩

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
