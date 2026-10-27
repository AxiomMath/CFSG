module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient.QuotientAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace ExtraspecialQuotientForm

open Quotient

open scoped commutatorElement

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
  [Fact (⁅⁅P, P⁆, P⁆ = ⊥)] [Fact (Monoid.exponent ↥P = p)]

private theorem comm_mul_left (h : ⁅⁅P, P⁆, P⁆ = ⊥) (x x' y : P) :
    ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  have hc := Subgroup.mem_center_iff.mp (commutator_mem_center h x' y) x
  have hc2 := Subgroup.mem_center_iff.mp (commutator_mem_center h x' y) ⁅x, y⁆
  have key : x' * y * x'⁻¹ = ⁅x', y⁆ * y := by simp [commutatorElement_def]
  calc ⁅x * x', y⁆ = x * (x' * y * x'⁻¹) * x⁻¹ * y⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
    _ = (x * ⁅x', y⁆) * y * x⁻¹ * y⁻¹ := by rw [key]; simp [mul_assoc]
    _ = ⁅x', y⁆ * ⁅x, y⁆ := by rw [hc]; simp [commutatorElement_def, mul_assoc]
    _ = _ := hc2.symm

private theorem comm_mul_right (h : ⁅⁅P, P⁆, P⁆ = ⊥) (x y y' : P) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have e : ∀ a b : P, ⁅a, b⁆ = ⁅b, a⁆⁻¹ := fun a b => (commutatorElement_inv b a).symm
  calc ⁅x, y * y'⁆ = ⁅y * y', x⁆⁻¹ := e _ _
    _ = (⁅y, x⁆ * ⁅y', x⁆)⁻¹ := by rw [comm_mul_left h]
    _ = ⁅y', x⁆⁻¹ * ⁅y, x⁆⁻¹ := mul_inv_rev _ _
    _ = ⁅x, y'⁆ * ⁅x, y⁆ := by rw [← e, ← e]
    _ = _ := by
      have := Subgroup.mem_center_iff.mp (commutator_mem_center h x y) ⁅x, y'⁆
      exact this

section Construction

variable (ζ : Subgroup.center ↥P ≃* Multiplicative (ZMod p))

@[expose] def cm (x y : P) : Subgroup.center ↥P :=
  ⟨⁅x, y⁆, commutator_mem_center (Fact.out : ⁅⁅P, P⁆, P⁆ = ⊥) x y⟩

theorem cm_mul_left (x x' y : P) : cm (P := P) (x * x') y = cm x y * cm x' y :=
  Subtype.ext (comm_mul_left Fact.out x x' y)

theorem cm_mul_right (x y y' : P) : cm (P := P) x (y * y') = cm x y * cm x y' :=
  Subtype.ext (comm_mul_right Fact.out x y y')

theorem cm_eq_one_of_mem_center_left {x : P} (hx : x ∈ Subgroup.center ↥P) (y : P) :
    cm x y = 1 := by
  apply Subtype.ext
  show ⁅x, y⁆ = 1
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp hx y).symm

theorem cm_eq_one_of_mem_center_right (x : P) {y : P} (hy : y ∈ Subgroup.center ↥P) :
    cm x y = 1 := by
  apply Subtype.ext
  show ⁅x, y⁆ = 1
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp hy x)

@[expose] def commHomL (y : P) : P →* Multiplicative (ZMod p) where
  toFun x := ζ (cm x y)
  map_one' := by
    rw [← map_one ζ]; congr 1; exact Subtype.ext (by simp [cm])
  map_mul' x x' := by rw [cm_mul_left, map_mul]

@[expose] def commHomQ (y : P) : Pbar P →* Multiplicative (ZMod p) :=
  QuotientGroup.lift (Subgroup.center ↥P) (commHomL ζ y) (fun z hz => by
    show ζ (cm z y) = 1
    rw [cm_eq_one_of_mem_center_left hz, map_one])

@[expose] def commHomP : P →* (Pbar P →* Multiplicative (ZMod p)) where
  toFun y := commHomQ ζ y
  map_one' := by
    ext x
    show ζ (cm x 1) = 1
    rw [← map_one ζ]; congr 1; exact Subtype.ext (by simp [cm])
  map_mul' y y' := by
    ext x
    show ζ (cm x (y * y')) = ζ (cm x y) * ζ (cm x y')
    rw [cm_mul_right, map_mul]

@[expose] def commHom : Pbar P →* (Pbar P →* Multiplicative (ZMod p)) :=
  QuotientGroup.lift (Subgroup.center ↥P) (commHomP ζ) (fun z hz => by
    ext x
    show ζ (cm x z) = 1
    rw [cm_eq_one_of_mem_center_right x hz, map_one])

@[expose] def formAdd : Additive (Pbar P) →+ Additive (Pbar P) →+ ZMod p where
  toFun a :=
    { toFun := fun b => Multiplicative.toAdd (commHom ζ (Additive.toMul b) (Additive.toMul a))
      map_zero' := by simp
      map_add' := fun b b' => by simp }
  map_zero' := by ext b; simp
  map_add' := fun a a' => by ext b; simp

end Construction
variable (ζ : Subgroup.center ↥P ≃* Multiplicative (ZMod p))

theorem addHom_smul (f : Additive (Pbar P) →+ ZMod p) (c : ZMod p) (a : Additive (Pbar P)) :
    f (c • a) = c * f a := by
  have h1 : c • a = c.val • a := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact Nat.cast_smul_eq_nsmul (ZMod p) _ a
  rw [h1, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem formAdd_smul_left (c : ZMod p) (a b : Additive (Pbar P)) :
    formAdd ζ (c • a) b = c * formAdd ζ a b :=
  addHom_smul ((formAdd ζ).flip b) c a

theorem formAdd_smul_right (c : ZMod p) (a b : Additive (Pbar P)) :
    formAdd ζ a (c • b) = c * formAdd ζ a b :=
  addHom_smul (formAdd ζ a) c b

@[expose] def form : Additive (Pbar P) →ₗ[ZMod p] Additive (Pbar P) →ₗ[ZMod p] ZMod p :=
  LinearMap.mk₂ (ZMod p) (fun a b => formAdd ζ a b)
    (fun a a' b => by simp)
    (fun c a b => formAdd_smul_left ζ c a b)
    (fun a b b' => by simp)
    (fun c a b => formAdd_smul_right ζ c a b)

theorem form_spec (x y : P) (h : ⁅x, y⁆ ∈ Subgroup.center ↥P) :
    form ζ (Additive.ofMul (QuotientGroup.mk x : Pbar P))
        (Additive.ofMul (QuotientGroup.mk y : Pbar P)) =
      Multiplicative.toAdd (ζ ⟨⁅x, y⁆, h⟩) := rfl

theorem form_alt (a : Additive (Pbar P)) : form ζ a a = 0 := by
  induction a using Additive.rec with | _ a => ?_
  induction a using QuotientGroup.induction_on with | _ x => ?_
  rw [form_spec ζ x x (by simp)]
  have : (⟨⁅x, x⁆, by simp⟩ : Subgroup.center ↥P) = 1 := Subtype.ext (by simp)
  rw [this]; simp

theorem form_nondegenerate (a : Additive (Pbar P))
    (h : ∀ b, form ζ a b = 0) : a = 0 := by
  induction a using Additive.rec with | _ a => ?_
  induction a using QuotientGroup.induction_on with | _ x => ?_
  have hx : x ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := h (Additive.ofMul (QuotientGroup.mk y : Pbar P))
    rw [form_spec ζ x y (commutator_mem_center Fact.out x y)] at h1
    have h2 : ζ ⟨⁅x, y⁆, commutator_mem_center Fact.out x y⟩ = 1 := by
      simpa using h1
    have h3 := ζ.injective (h2.trans (map_one ζ).symm)
    have h4 : ⁅x, y⁆ = 1 := congrArg Subtype.val h3
    rw [commutatorElement_eq_one_iff_mul_comm] at h4
    exact h4.symm
  show Additive.ofMul (QuotientGroup.mk x : Pbar P) = 0
  rw [(QuotientGroup.eq_one_iff x).mpr hx]
  rfl

end ExtraspecialQuotientForm
end Section5
end CFSG.LocalAnalysis.RankThreeUC
