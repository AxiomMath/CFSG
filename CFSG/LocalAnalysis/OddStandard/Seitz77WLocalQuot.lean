module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WLocalDef
public import CFSG.LocalAnalysis.OddStandard.Seitz77WLocalStep4

public section

namespace CFSG.OddStandard.Seitz77

open CFSG.ComponentClassification.PSL3Four CFSG.Open Subgroup
open scoped commutatorElement

namespace Config25

variable {Q : Type} [Group Q] [Finite Q] {V : Subgroup Q} {t : Q} (c : Config25 Q V t)

theorem V_le_ker_delta : V ≤ c.delta.ker := by
  intro v hv
  rw [MonoidHom.mem_ker, c.delta_apply]
  have : (⟨⁅t, v⁆, c.comm_mem v⟩ : V) = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm]
    exact (c.V_comm hv t).symm
  rw [this, map_one]

variable [V.Normal]

@[expose] def deltaQ : Q ⧸ V →* Multiplicative F4V :=
  QuotientGroup.lift V c.delta c.V_le_ker_delta

theorem deltaQ_mk (x : Q) : c.deltaQ (QuotientGroup.mk x) = c.delta x := rfl

theorem deltaQ_eq_one_iff (h : Q ⧸ V) :
    c.deltaQ h = 1 ↔ (h = 1 ∨ h = QuotientGroup.mk t) := by
  induction h using QuotientGroup.induction_on with
  | H x =>
    rw [c.deltaQ_mk, c.delta_eq_one_iff, c.mem_sup_iff]
    constructor
    · rintro (hx | ⟨v, hv, rfl⟩)
      · left; exact (QuotientGroup.eq_one_iff x).mpr hx
      · right
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff v).mpr hv, one_mul]
    · rintro (hx | hx)
      · left; exact (QuotientGroup.eq_one_iff x).mp hx
      · right
        refine ⟨x * t⁻¹, ?_, by group⟩
        rw [QuotientGroup.eq_iff_div_mem] at hx
        simpa [div_eq_mul_inv] using hx

variable {c} {φ : MulAut Q} {f : F4V → F4V}

omit [V.Normal] in
theorem Acts.map_V (h : c.Acts φ f) : V.map φ.toMonoidHom = V := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨v, hv, rfl⟩
    exact h.mem_V hv
  · rw [Subgroup.card_map_of_injective φ.injective]

@[expose] def Acts.quot (h : c.Acts φ f) : Q ⧸ V ≃* Q ⧸ V :=
  QuotientGroup.congr V V φ h.map_V

theorem Acts.quot_mk (h : c.Acts φ f) (x : Q) :
    h.quot (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
  QuotientGroup.congr_mk V V φ h.map_V x

theorem Acts.deltaQ_quot (h : c.Acts φ f) (y : Q ⧸ V) :
    c.deltaQ (h.quot y) = Multiplicative.ofAdd (f (Multiplicative.toAdd (c.deltaQ y))) := by
  induction y using QuotientGroup.induction_on with
  | H x => rw [h.quot_mk, c.deltaQ_mk, c.deltaQ_mk, h.delta_apply]

theorem Acts.quot_t (h : c.Acts φ f) : h.quot (QuotientGroup.mk t) = QuotientGroup.mk t := by
  rw [h.quot_mk, h.fix]

variable (c)

include c

theorem mk_t_comm (y : Q ⧸ V) : QuotientGroup.mk t * y = y * QuotientGroup.mk t := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    have := c.comm_mem x
    simpa [commutatorElement_def, div_eq_mul_inv, mul_assoc] using this

theorem deltaQ_surjective : Function.Surjective c.deltaQ := by
  intro y
  obtain ⟨x, rfl⟩ := c.delta_surjective y
  exact ⟨QuotientGroup.mk x, c.deltaQ_mk x⟩

theorem exponent_two_quot : ∀ y : Q ⧸ V, y * y = 1 := by
  refine exponent_two (QuotientGroup.mk t) c.mk_t_comm ?_ ?_ c.deltaQ c.deltaQ_surjective
    c.deltaQ_eq_one_iff (fun γ => (c.acts_up γ).quot) (fun γ => (c.acts_low γ).quot)
    (fun γ y => (c.acts_up γ).deltaQ_quot y) (fun γ y => (c.acts_low γ).deltaQ_quot y)
    (fun γ => (c.acts_up γ).quot_t) (fun γ => (c.acts_low γ).quot_t)
  · rw [← QuotientGroup.mk_mul, c.t_sq, QuotientGroup.mk_one]
  · rw [Ne, QuotientGroup.eq_one_iff]; exact c.t_not_mem

theorem sq_mem_V (x : Q) : x * x ∈ V := by
  have := c.exponent_two_quot (QuotientGroup.mk x)
  rwa [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at this

theorem mk_comm (a b : Q ⧸ V) : a * b = b * a := by
  have hinv : ∀ g : Q ⧸ V, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (c.exponent_two_quot g)
  calc a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv, hinv]

theorem comm_mem_V (x y : Q) : ⁅x, y⁆ ∈ V := by
  have h := c.mk_comm (QuotientGroup.mk x) (QuotientGroup.mk y)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem] at h
  simpa [commutatorElement_def, div_eq_mul_inv, mul_assoc] using h

end Config25

end CFSG.OddStandard.Seitz77
