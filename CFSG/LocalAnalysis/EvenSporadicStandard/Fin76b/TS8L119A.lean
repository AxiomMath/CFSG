module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13R

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

structure OYFacts {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
    {B : Subgroup G} {β : G} {S : Subgroup G} {α σ : G} (c : OI13Ctx L z t T E B β S α σ)
    (y : G) : Prop where
  sq : y * y = 1
  conjT : y * t * y⁻¹ = t
  conjA : y * α * y⁻¹ = α * t
  conjW1 : ∀ w ∈ c.W1, y * w * y⁻¹ ∈ c.W2
  conjW2 : ∀ w ∈ c.W2, y * w * y⁻¹ ∈ c.W1
  notQ : y ∉ c.Qs

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G} (c : OI13Ctx L z t T E B β S α σ)

theorem W1_inf_W2_eq : c.W1 ⊓ c.W2 = c.Zs := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := c.cl
  exact h9

theorem Qs_eq_prod {q : G} (hq : q ∈ c.Qs) : ∃ w₁ ∈ c.W1, ∃ w₂ ∈ c.W2, q = w₁ * w₂ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := c.cl
  exact h10 q hq

theorem comm_W1_mem {w w' : G} (hw : w ∈ c.W1) (hw' : w' ∈ c.W1) :
    w * w' * w⁻¹ * w'⁻¹ ∈ c.Zs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := c.cl
  rcases h12 w hw w' hw' with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact c.alpha_mem_Zs

theorem comm_W2_mem {w w' : G} (hw : w ∈ c.W2) (hw' : w' ∈ c.W2) :
    w * w' * w⁻¹ * w'⁻¹ ∈ c.Zs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14, -⟩ := c.cl
  rcases h14 w hw w' hw' with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact c.alpha_t_mem_Zs

theorem sq_W1_mem {w : G} (hw : w ∈ c.W1) : w * w ∈ c.Zs := by
  rcases c.h.sq_W1 c.hF c.hM c.hα c.cl w hw with h | h <;> rw [h]
  · exact one_mem _
  · exact c.alpha_mem_Zs

theorem sq_W2_mem {w : G} (hw : w ∈ c.W2) : w * w ∈ c.Zs := by
  rcases c.h.sq_W2 c.hF c.hM c.hα c.cl w hw with h | h <;> rw [h]
  · exact one_mem _
  · exact c.alpha_t_mem_Zs

variable {c} in
@[expose] noncomputable def thetaY {y : G} (hy : OYFacts c y) : ↥c.W1 →* G where
  toFun w := (w : G) * (y * (w : G) * y⁻¹)
  map_one' := by simp
  map_mul' w w' := by
    have hc : (w' : G) * (y * (w : G) * y⁻¹) = (y * (w : G) * y⁻¹) * (w' : G) :=
      c.W1_comm_W2 w'.2 (hy.conjW1 _ w.2)
    calc ((w : G) * (w' : G)) * (y * ((w : G) * (w' : G)) * y⁻¹)
        = (w : G) * (w' : G) * ((y * (w : G) * y⁻¹) * (y * (w' : G) * y⁻¹)) := by group
      _ = (w : G) * ((w' : G) * (y * (w : G) * y⁻¹)) * (y * (w' : G) * y⁻¹) := by group
      _ = (w : G) * ((y * (w : G) * y⁻¹) * (w' : G)) * (y * (w' : G) * y⁻¹) := by rw [hc]
      _ = ((w : G) * (y * (w : G) * y⁻¹)) * ((w' : G) * (y * (w' : G) * y⁻¹)) := by group

variable {c} in
@[simp] theorem thetaY_apply {y : G} (hy : OYFacts c y) (w : ↥c.W1) :
    c.thetaY hy w = (w : G) * (y * (w : G) * y⁻¹) := rfl

variable {c} in
theorem thetaY_mem {y : G} (hy : OYFacts c y) (w : ↥c.W1) :
    c.thetaY hy w ∈ c.Qs := by
  rw [thetaY_apply]
  exact mul_mem (c.W1_le_Qs w.2) (c.W2_le_Qs (hy.conjW1 _ w.2))

variable {c} in
theorem thetaY_eq_one {y : G} (hy : OYFacts c y) {w : ↥c.W1} :
    c.thetaY hy w = 1 ↔ (w : G) = 1 ∨ (w : G) = t := by
  constructor
  · intro h1
    rw [thetaY_apply] at h1
    have hv : y * (w : G) * y⁻¹ = (w : G)⁻¹ := (mul_eq_one_iff_inv_eq.1 h1).symm
    have hw2 : (w : G)⁻¹ ∈ c.W2 := hv ▸ hy.conjW1 _ w.2
    have hZ : (w : G)⁻¹ ∈ c.Zs := by
      have hmem : (w : G)⁻¹ ∈ c.W1 ⊓ c.W2 := Subgroup.mem_inf.2 ⟨Subgroup.inv_mem c.W1 w.2, hw2⟩
      rw [c.W1_inf_W2_eq] at hmem
      exact hmem
    have hZ' : (w : G) ∈ c.Zs := by
      have h' : ((w : G)⁻¹)⁻¹ ∈ c.Zs := Subgroup.inv_mem c.Zs hZ
      rwa [inv_inv] at h'
    rcases (c.mem_Zs).1 hZ' with e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exfalso
      have hαinv : (w : G)⁻¹ = (w : G) := by
        rw [e]; exact inv_eq_of_mul_eq_one_right c.hα.sq
      rw [hαinv, e, hy.conjA] at hv
      exact c.h.t_ne (mul_eq_left.1 hv)
    · exfalso
      have hinv : (w : G)⁻¹ = (w : G) := by
        rw [e]; exact inv_eq_of_mul_eq_one_right (c.Zs_sq c.alpha_t_mem_Zs)
      have h3 : y * (α * t) * y⁻¹ = α := by
        calc y * (α * t) * y⁻¹ = (y * α * y⁻¹) * (y * t * y⁻¹) := by group
          _ = (α * t) * t := by rw [hy.conjA, hy.conjT]
          _ = α := by rw [mul_assoc, c.h.t_sq, mul_one]
      rw [hinv, e, h3] at hv
      exact c.h.t_ne (mul_eq_left.1 hv.symm)
  · rintro (e | e)
    · rw [thetaY_apply, e]; simp
    · rw [thetaY_apply, e, hy.conjT]; exact c.h.t_sq

variable {c} in
@[expose] noncomputable def E0 {y : G} (hy : OYFacts c y) : Subgroup G := (c.thetaY hy).range

variable {c} in
theorem mem_E0 {y : G} (hy : OYFacts c y) {e : G} :
    e ∈ c.E0 hy ↔ ∃ w : ↥c.W1, (w : G) * (y * (w : G) * y⁻¹) = e := by
  unfold E0
  rw [MonoidHom.mem_range]
  simp only [thetaY_apply]

variable {c} in
theorem E0_le_Qs {y : G} (hy : OYFacts c y) : c.E0 hy ≤ c.Qs := by
  intro e he
  obtain ⟨w, rfl⟩ := (MonoidHom.mem_range).1 he
  exact thetaY_mem hy w

variable {c} in
theorem E0_pgroup {y : G} (hy : OYFacts c y) : IsPGroup 2 (c.E0 hy) :=
  c.Qs_pgroup.to_le (c.E0_le_Qs hy)

variable {c} in
theorem y_comm_E0 {y : G} (hy : OYFacts c y) {e : G} (he : e ∈ c.E0 hy) : y * e = e * y := by
  obtain ⟨w, rfl⟩ := (c.mem_E0 hy).1 he
  have hv : y * (w : G) * y⁻¹ ∈ c.W2 := hy.conjW1 _ w.2
  have hc : (w : G) * (y * (w : G) * y⁻¹) = (y * (w : G) * y⁻¹) * (w : G) :=
    c.W1_comm_W2 w.2 hv
  have hyv : y * (y * (w : G) * y⁻¹) * y⁻¹ = (w : G) := by
    have : y * (y * (w : G) * y⁻¹) * y⁻¹ = (y * y) * (w : G) * (y * y)⁻¹ := by group
    rw [this, hy.sq]; group
  have key : y * ((w : G) * (y * (w : G) * y⁻¹)) * y⁻¹ = (w : G) * (y * (w : G) * y⁻¹) := by
    calc y * ((w : G) * (y * (w : G) * y⁻¹)) * y⁻¹
        = (y * (w : G) * y⁻¹) * (y * (y * (w : G) * y⁻¹) * y⁻¹) := by group
      _ = (y * (w : G) * y⁻¹) * (w : G) := by rw [hyv]
      _ = (w : G) * (y * (w : G) * y⁻¹) := hc.symm
  calc y * ((w : G) * (y * (w : G) * y⁻¹))
      = (y * ((w : G) * (y * (w : G) * y⁻¹)) * y⁻¹) * y := by group
    _ = ((w : G) * (y * (w : G) * y⁻¹)) * y := by rw [key]

variable {c} in
theorem alpha_comm_E0 {y : G} (hy : OYFacts c y) {e : G} (he : e ∈ c.E0 hy) :
    α * e = e * α :=
  c.Zs_comm_Qs c.alpha_mem_Zs (c.E0_le_Qs hy he)

variable {c} in
theorem E0_iso {y : G} (hy : OYFacts c y) : Nonempty (↥E ≃* ↥(c.E0 hy)) := by
  have hker : c.thetaHom.ker = (c.thetaY hy).rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    ext w
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, c.thetaHom_eq_one, thetaY_eq_one hy]
  let e₁ : ↥c.W1 ⧸ c.thetaHom.ker ≃* ↥E :=
    QuotientGroup.quotientKerEquivOfSurjective _ c.thetaHom_surjective
  let e₂ : ↥c.W1 ⧸ (c.thetaY hy).rangeRestrict.ker ≃* ↥(c.E0 hy) :=
    QuotientGroup.quotientKerEquivOfSurjective _ (MonoidHom.rangeRestrict_surjective _)
  exact ⟨e₁.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans e₂)⟩

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
