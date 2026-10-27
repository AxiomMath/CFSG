module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119C

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G} (c : OI13Ctx L z t T E B β S α σ)

include c

theorem Zs_E0_comm {y : G} (hy : OYFacts c y) {a e : G} (ha : a ∈ c.Zs) (he : e ∈ c.E0 hy) :
    a * e = e * a :=
  c.Zs_comm_Qs ha (c.E0_le_Qs hy he)

theorem t_mem_Y0 {y : G} (hy : OYFacts c y) : t ∈ Y0 y α := by
  have hy_mem : y ∈ Y0 y α := subset_closure (by simp)
  have hα_mem : α ∈ Y0 y α := subset_closure (by simp)
  rw [← sq_yα c hy]
  exact mul_mem (mul_mem hy_mem hα_mem) (mul_mem hy_mem hα_mem)

theorem Zs_le_Y0 {y : G} (hy : OYFacts c y) : c.Zs ≤ Y0 y α := by
  intro a ha
  have hα_mem : α ∈ Y0 y α := subset_closure (by simp)
  rcases c.mem_Zs.1 ha with h | h | h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact t_mem_Y0 c hy
  · rw [h]
    exact hα_mem
  · rw [h]
    exact mul_mem hα_mem (t_mem_Y0 c hy)

@[expose] def PQ {y : G} (hy : OYFacts c y) (q : G) : Prop :=
  (∀ e ∈ c.E0 hy, ∃ e' ∈ c.E0 hy, ∃ a ∈ c.Zs, q * e * q⁻¹ = e' * a) ∧
    (∃ e' ∈ c.E0 hy, ∃ a ∈ c.Zs, q * y * q⁻¹ = e' * a * y)

theorem PQ_mul {y : G} (hy : OYFacts c y) {q₁ q₂ : G} (hq₁ : q₁ ∈ c.Qs)
    (h₁ : PQ c hy q₁) (h₂ : PQ c hy q₂) : PQ c hy (q₁ * q₂) := by
  obtain ⟨hE₁, hY₁⟩ := h₁
  obtain ⟨hE₂, hY₂⟩ := h₂
  have hcomm : ∀ a ∈ c.Zs, q₁ * a * q₁⁻¹ = a := fun a ha => by
    rw [← c.Zs_comm_Qs ha hq₁]
    group
  constructor
  · intro e he
    obtain ⟨e₂, he₂, a₂, ha₂, h2⟩ := hE₂ e he
    obtain ⟨e₁, he₁, a₁, ha₁, h1⟩ := hE₁ e₂ he₂
    refine ⟨e₁, he₁, a₁ * a₂, mul_mem ha₁ ha₂, ?_⟩
    calc q₁ * q₂ * e * (q₁ * q₂)⁻¹ = q₁ * (q₂ * e * q₂⁻¹) * q₁⁻¹ := by group
      _ = q₁ * (e₂ * a₂) * q₁⁻¹ := by rw [h2]
      _ = (q₁ * e₂ * q₁⁻¹) * (q₁ * a₂ * q₁⁻¹) := by group
      _ = (e₁ * a₁) * a₂ := by rw [h1, hcomm a₂ ha₂]
      _ = e₁ * (a₁ * a₂) := by group
  · obtain ⟨e₂, he₂, a₂, ha₂, h2⟩ := hY₂
    obtain ⟨e₃, he₃, a₃, ha₃, h3⟩ := hE₁ e₂ he₂
    obtain ⟨e₁, he₁, a₁, ha₁, h1⟩ := hY₁
    have s1 : a₂ * e₁ = e₁ * a₂ := Zs_E0_comm c hy ha₂ he₁
    have s2 : a₃ * e₁ = e₁ * a₃ := Zs_E0_comm c hy ha₃ he₁
    refine ⟨e₃ * e₁, mul_mem he₃ he₁, a₃ * a₂ * a₁, mul_mem (mul_mem ha₃ ha₂) ha₁, ?_⟩
    calc q₁ * q₂ * y * (q₁ * q₂)⁻¹ = q₁ * (q₂ * y * q₂⁻¹) * q₁⁻¹ := by group
      _ = q₁ * (e₂ * a₂ * y) * q₁⁻¹ := by rw [h2]
      _ = (q₁ * e₂ * q₁⁻¹) * (q₁ * a₂ * q₁⁻¹) * (q₁ * y * q₁⁻¹) := by group
      _ = (e₃ * a₃) * a₂ * (e₁ * a₁ * y) := by rw [h3, hcomm a₂ ha₂, h1]
      _ = e₃ * (a₃ * (a₂ * e₁)) * a₁ * y := by group
      _ = e₃ * (a₃ * (e₁ * a₂)) * a₁ * y := by rw [s1]
      _ = e₃ * ((a₃ * e₁) * a₂) * a₁ * y := by group
      _ = e₃ * ((e₁ * a₃) * a₂) * a₁ * y := by rw [s2]
      _ = (e₃ * e₁) * (a₃ * a₂ * a₁) * y := by group

theorem PQ_W1 {y : G} (hy : OYFacts c y) {w : G} (hw : w ∈ c.W1) : PQ c hy w := by
  constructor
  · intro e he
    obtain ⟨v, rfl⟩ := (c.mem_E0 hy).1 he
    have hb : y * (v : G) * y⁻¹ ∈ c.W2 := hy.conjW1 _ v.2
    have hbw : w * (y * (v : G) * y⁻¹) * w⁻¹ = y * (v : G) * y⁻¹ := by
      rw [c.W1_comm_W2 hw hb]
      group
    have hvb : (v : G) * (y * (v : G) * y⁻¹) ∈ c.E0 hy := (c.mem_E0 hy).2 ⟨v, rfl⟩
    have ha : w * (v : G) * w⁻¹ * (v : G)⁻¹ ∈ c.Zs := c.comm_W1_mem hw v.2
    refine ⟨(v : G) * (y * (v : G) * y⁻¹), hvb, w * (v : G) * w⁻¹ * (v : G)⁻¹, ha, ?_⟩
    calc w * ((v : G) * (y * (v : G) * y⁻¹)) * w⁻¹
        = (w * (v : G) * w⁻¹) * (w * (y * (v : G) * y⁻¹) * w⁻¹) := by group
      _ = (w * (v : G) * w⁻¹ * (v : G)⁻¹ * (v : G)) * (y * (v : G) * y⁻¹) := by
          rw [hbw]
          group
      _ = (w * (v : G) * w⁻¹ * (v : G)⁻¹) * ((v : G) * (y * (v : G) * y⁻¹)) := by group
      _ = ((v : G) * (y * (v : G) * y⁻¹)) * (w * (v : G) * w⁻¹ * (v : G)⁻¹) :=
          Zs_E0_comm c hy ha hvb
  · have hu : y * w * y⁻¹ ∈ c.W2 := hy.conjW1 w hw
    have hyw : w * (y * w * y⁻¹) ∈ c.E0 hy := (c.mem_E0 hy).2 ⟨⟨w, hw⟩, rfl⟩
    refine ⟨w * (y * w * y⁻¹), hyw, (y * w * y⁻¹ * (y * w * y⁻¹))⁻¹,
      Subgroup.inv_mem c.Zs (c.sq_W2_mem hu), ?_⟩
    group

theorem PQ_W2 {y : G} (hy : OYFacts c y) {w : G} (hw : w ∈ c.W2) : PQ c hy w := by
  constructor
  · intro e he
    obtain ⟨v, rfl⟩ := (c.mem_E0 hy).1 he
    have hb : y * (v : G) * y⁻¹ ∈ c.W2 := hy.conjW1 _ v.2
    have hbQ : y * (v : G) * y⁻¹ ∈ c.Qs := c.W2_le_Qs hb
    have hwv : w * (v : G) * w⁻¹ = (v : G) := by
      rw [← c.W1_comm_W2 v.2 hw]
      group
    have hc' : w * (y * (v : G) * y⁻¹) * w⁻¹ * (y * (v : G) * y⁻¹)⁻¹ ∈ c.Zs :=
      c.comm_W2_mem hw hb
    have hvb : (v : G) * (y * (v : G) * y⁻¹) ∈ c.E0 hy := (c.mem_E0 hy).2 ⟨v, rfl⟩
    refine ⟨(v : G) * (y * (v : G) * y⁻¹), hvb,
      w * (y * (v : G) * y⁻¹) * w⁻¹ * (y * (v : G) * y⁻¹)⁻¹, hc', ?_⟩
    calc w * ((v : G) * (y * (v : G) * y⁻¹)) * w⁻¹
        = (w * (v : G) * w⁻¹) * (w * (y * (v : G) * y⁻¹) * w⁻¹) := by group
      _ = (v : G) * (w * (y * (v : G) * y⁻¹) * w⁻¹) := by rw [hwv]
      _ = (v : G) * ((w * (y * (v : G) * y⁻¹) * w⁻¹ * (y * (v : G) * y⁻¹)⁻¹) *
            (y * (v : G) * y⁻¹)) := by group
      _ = (v : G) * ((y * (v : G) * y⁻¹) * (w * (y * (v : G) * y⁻¹) * w⁻¹ *
            (y * (v : G) * y⁻¹)⁻¹)) := by
          rw [c.Zs_comm_Qs hc' hbQ]
      _ = ((v : G) * (y * (v : G) * y⁻¹)) * (w * (y * (v : G) * y⁻¹) * w⁻¹ *
            (y * (v : G) * y⁻¹)⁻¹) := by group
  · have hu : y * w * y⁻¹ ∈ c.W1 := hy.conjW2 w hw
    have hcomm : (y * w * y⁻¹) * w = w * (y * w * y⁻¹) := c.W1_comm_W2 hu hw
    have hyuy : y * (y * w * y⁻¹) * y⁻¹ = w := by
      calc y * (y * w * y⁻¹) * y⁻¹ = (y * y) * w * (y * y)⁻¹ := by group
        _ = w := by rw [hy.sq]; group
    have hE0 : (y * w * y⁻¹) * (y * (y * w * y⁻¹) * y⁻¹) ∈ c.E0 hy :=
      (c.mem_E0 hy).2 ⟨⟨y * w * y⁻¹, hu⟩, rfl⟩
    refine ⟨(y * w * y⁻¹) * (y * (y * w * y⁻¹) * y⁻¹), hE0,
      ((y * w * y⁻¹) * (y * w * y⁻¹))⁻¹, Subgroup.inv_mem c.Zs (c.sq_W1_mem hu), ?_⟩
    rw [hyuy]
    calc w * y * w⁻¹ = w * (y * w * y⁻¹)⁻¹ * y := by group
      _ = (y * w * y⁻¹ * w) * (y * w * y⁻¹ * (y * w * y⁻¹))⁻¹ * y := by
          rw [hcomm]
          group

theorem PQ_Qs {y : G} (hy : OYFacts c y) {q : G} (hq : q ∈ c.Qs) : PQ c hy q := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := c.Qs_eq_prod hq
  exact PQ_mul c hy (c.W1_le_Qs hw₁) (PQ_W1 c hy hw₁) (PQ_W2 c hy hw₂)

theorem Qs_normalizes_U {y : G} (hy : OYFacts c y) {q : G} (hq : q ∈ c.Qs) :
    ∀ u ∈ Y0 y α ⊔ c.E0 hy, q * u * q⁻¹ ∈ Y0 y α ⊔ c.E0 hy := by
  obtain ⟨hE, hY⟩ := PQ_Qs c hy hq
  have hyY : y ∈ Y0 y α := subset_closure (by simp)
  have hαY : α ∈ Y0 y α := subset_closure (by simp)
  let K : Subgroup G := (Y0 y α ⊔ c.E0 hy).comap (MulAut.conj q).toMonoidHom
  have hK_E : c.E0 hy ≤ K := by
    intro e he
    obtain ⟨e', he', a, ha, eq⟩ := hE e he
    show q * e * q⁻¹ ∈ Y0 y α ⊔ c.E0 hy
    rw [eq]
    exact mul_mem (Subgroup.mem_sup_right he') (Subgroup.mem_sup_left (Zs_le_Y0 c hy ha))
  have hK_Y : Y0 y α ≤ K := by
    unfold Y0
    refine (Subgroup.closure_le K).2 ?_
    intro v hv
    rcases Set.mem_insert_iff.1 hv with hv' | hv'
    · rw [hv']
      obtain ⟨e', he', a, ha, eq⟩ := hY
      show q * y * q⁻¹ ∈ Y0 y α ⊔ c.E0 hy
      rw [eq]
      exact mul_mem (mul_mem (Subgroup.mem_sup_right he')
        (Subgroup.mem_sup_left (Zs_le_Y0 c hy ha))) (Subgroup.mem_sup_left hyY)
    · rw [Set.mem_singleton_iff.1 hv']
      show q * α * q⁻¹ ∈ Y0 y α ⊔ c.E0 hy
      have hc : q * α = α * q := (c.Zs_comm_Qs c.alpha_mem_Zs hq).symm
      have e : q * α * q⁻¹ = α := by
        rw [hc]
        group
      rw [e]
      exact Subgroup.mem_sup_left hαY
  have hU : Y0 y α ⊔ c.E0 hy ≤ K := sup_le hK_Y hK_E
  intro u hu
  exact hU hu

theorem Qs_normalizes_U_iff {y : G} (hy : OYFacts c y) {q : G} (hq : q ∈ c.Qs) (u : G) :
    u ∈ Y0 y α ⊔ c.E0 hy ↔ q * u * q⁻¹ ∈ Y0 y α ⊔ c.E0 hy := by
  constructor
  · exact Qs_normalizes_U c hy hq u
  · intro hu
    have h1 := Qs_normalizes_U c hy (Subgroup.inv_mem c.Qs hq) _ hu
    have e : q⁻¹ * (q * u * q⁻¹) * q⁻¹⁻¹ = u := by group
    rwa [e] at h1

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
