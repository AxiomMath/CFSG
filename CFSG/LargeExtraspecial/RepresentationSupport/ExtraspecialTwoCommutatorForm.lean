module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCommutatorForm

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction

open scoped commutatorElement

variable {E : Type*} [Group E] [Finite E] [h : Fact (CFSG.IsExtraspecialPGroup 2 E)]

@[expose] noncomputable def commVal (ζ : Subgroup.center E ≃* Multiplicative (ZMod 2)) (a b : E) : ZMod 2 :=
  Multiplicative.toAdd (ζ ⟨⁅a, b⁆, comm_mem_center h.out a b⟩)

variable (ζ : Subgroup.center E ≃* Multiplicative (ZMod 2))

theorem commVal_mul_left (a b c : E) :
    commVal ζ (a * b) c = commVal ζ a c + commVal ζ b c := by
  unfold commVal
  rw [← toAdd_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  have hz : ⁅b, c⁆ ∈ Subgroup.center E := comm_mem_center h.out b c
  have hz' : ⁅a, c⁆ ∈ Subgroup.center E := comm_mem_center h.out a c
  have := Subgroup.mem_center_iff.1 hz a
  have e : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by rw [this]; simp
  simp only [Subgroup.coe_mul]
  rw [commutatorElement_mul_left_eq_conj_mul, e]
  exact Subgroup.mem_center_iff.1 hz' ⁅b, c⁆

theorem commVal_mul_right (a b c : E) :
    commVal ζ a (b * c) = commVal ζ a b + commVal ζ a c := by
  unfold commVal
  rw [← toAdd_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  have hz : ⁅a, c⁆ ∈ Subgroup.center E := comm_mem_center h.out a c
  have := Subgroup.mem_center_iff.1 hz b
  simp only [Subgroup.coe_mul]
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅a, b⁆ b, this]
  simp [mul_assoc]

theorem commVal_center_left {z : E} (hz : z ∈ Subgroup.center E) (b : E) :
    commVal ζ z b = 0 := by
  unfold commVal
  have : (⟨⁅z, b⁆, comm_mem_center h.out z b⟩ : Subgroup.center E) = 1 := by
    apply Subtype.ext
    simp only [commutatorElement_def, OneMemClass.coe_one]
    rw [← Subgroup.mem_center_iff.1 hz b]; simp
  rw [this]; simp

theorem commVal_center_right (a : E) {z : E} (hz : z ∈ Subgroup.center E) :
    commVal ζ a z = 0 := by
  unfold commVal
  have : (⟨⁅a, z⁆, comm_mem_center h.out a z⟩ : Subgroup.center E) = 1 := by
    apply Subtype.ext
    have := commutatorElement_eq_one_iff_commute.2 ((Subgroup.mem_center_iff.1 hz a))
    simpa using this
  rw [this]; simp

theorem commVal_congr_left {a a' : E} (ha : a⁻¹ * a' ∈ Subgroup.center E) (b : E) :
    commVal ζ a b = commVal ζ a' b := by
  have := commVal_mul_left ζ a (a⁻¹ * a') b
  rw [mul_inv_cancel_left, commVal_center_left ζ ha] at this
  simpa using this.symm

theorem commVal_congr_right (a : E) {b b' : E} (hb : b⁻¹ * b' ∈ Subgroup.center E) :
    commVal ζ a b = commVal ζ a b' := by
  have := commVal_mul_right ζ a b (b⁻¹ * b')
  rw [mul_inv_cancel_left, commVal_center_right ζ _ hb] at this
  simpa using this.symm

@[expose] noncomputable def pair (x y : QSpace E) : ZMod 2 :=
  Quotient.liftOn₂' (s₁ := QuotientGroup.leftRel (Subgroup.center E))
    (s₂ := QuotientGroup.leftRel (Subgroup.center E))
    (Additive.toMul x : E ⧸ Subgroup.center E) (Additive.toMul y : E ⧸ Subgroup.center E)
    (commVal ζ) (by
      intro a b a' b' ha hb
      rw [QuotientGroup.leftRel_apply] at ha hb
      rw [commVal_congr_left ζ ha, commVal_congr_right ζ a' hb])

theorem pair_add_left (x x' y : QSpace E) : pair ζ (x + x') y = pair ζ x y + pair ζ x' y := by
  induction x using Additive.rec with | _ a => ?_
  induction x' using Additive.rec with | _ a' => ?_
  induction y using Additive.rec with | _ b => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  induction a' using QuotientGroup.induction_on with | _ a' => ?_
  induction b using QuotientGroup.induction_on with | _ b => ?_
  exact commVal_mul_left ζ a a' b

theorem pair_add_right (x y y' : QSpace E) : pair ζ x (y + y') = pair ζ x y + pair ζ x y' := by
  induction x using Additive.rec with | _ a => ?_
  induction y using Additive.rec with | _ b => ?_
  induction y' using Additive.rec with | _ b' => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  induction b using QuotientGroup.induction_on with | _ b => ?_
  induction b' using QuotientGroup.induction_on with | _ b' => ?_
  exact commVal_mul_right ζ a b b'

@[expose] noncomputable def form : LinearMap.BilinForm (ZMod 2) (QSpace E) :=
  LinearMap.mk₂ (ZMod 2) (pair ζ) (pair_add_left ζ)
    (fun c x y => by
      have h0 : pair ζ 0 y = 0 := by
        have := pair_add_left ζ 0 0 y
        simpa using this
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · simpa using h0
      · simp)
    (pair_add_right ζ)
    (fun c x y => by
      have h0 : pair ζ x 0 = 0 := by
        have := pair_add_right ζ x 0 0
        simpa using this
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · simpa using h0
      · simp)

theorem form_mk (a b : E) :
    form ζ (Additive.ofMul (a : E ⧸ Subgroup.center E))
      (Additive.ofMul (b : E ⧸ Subgroup.center E)) =
      Multiplicative.toAdd (ζ ⟨⁅a, b⁆, comm_mem_center h.out a b⟩) := rfl

theorem alternating : (form ζ).IsAlt := by
  intro x
  induction x using Additive.rec with | _ a => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  rw [form_mk]
  have : (⟨⁅a, a⁆, comm_mem_center h.out a a⟩ : Subgroup.center E) = 1 :=
    Subtype.ext (by simp)
  rw [this]; simp

theorem separatingLeft : (form ζ).SeparatingLeft := by
  intro x hx
  induction x using Additive.rec with | _ a => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  have hc : a ∈ Subgroup.center E := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := hx (Additive.ofMul (g : E ⧸ Subgroup.center E))
    rw [form_mk] at h1
    have h2 : (⟨⁅a, g⁆, comm_mem_center h.out a g⟩ : Subgroup.center E) = 1 := by
      apply ζ.injective
      apply Multiplicative.toAdd.injective
      simpa using h1
    have h3 : ⁅a, g⁆ = 1 := congrArg Subtype.val h2
    have := commutatorElement_eq_one_iff_commute.1 h3
    exact this.symm.eq
  have : (a : E ⧸ Subgroup.center E) = 1 := (QuotientGroup.eq_one_iff _).2 hc
  rw [this]
  rfl

theorem nondegenerate : (form ζ).Nondegenerate := by
  refine ⟨separatingLeft ζ, ?_⟩
  intro y hy
  exact separatingLeft ζ y (fun x => (alternating ζ).isRefl x y (hy x))

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCommutatorForm
