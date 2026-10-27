module

public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

variable {G : Type*} [Group G] {P : Subgroup G} {Q : Type*} [CommGroup Q]

noncomputable def rightTransversalRepr (T : P.RightTransversal) (x : G) : G :=
  (T.2.rightQuotientEquiv (Quotient.mk'' x) : G)

lemma rightTransversalRepr_mem (T : P.RightTransversal) (x : G) :
    rightTransversalRepr T x ∈ (T : Set G) :=
  (T.2.rightQuotientEquiv (Quotient.mk'' x)).2

lemma mk''_rightTransversalRepr (T : P.RightTransversal) (x : G) :
    (Quotient.mk'' (rightTransversalRepr T x) : Quotient (rightRel P)) = Quotient.mk'' x :=
  T.2.mk''_rightQuotientEquiv _

lemma mul_inv_rightTransversalRepr_mem (T : P.RightTransversal) (x : G) :
    x * (rightTransversalRepr T x)⁻¹ ∈ P :=
  QuotientGroup.rightRel_apply.mp (Quotient.eq''.mp (mk''_rightTransversalRepr T x))

lemma rightTransversalRepr_mul_inv_mem (T : P.RightTransversal) (x : G) :
    rightTransversalRepr T x * x⁻¹ ∈ P := by
  simpa using P.inv_mem (mul_inv_rightTransversalRepr_mem T x)

lemma rightTransversalRepr_congr (T : P.RightTransversal) {x y : G} (h : y * x⁻¹ ∈ P) :
    rightTransversalRepr T x = rightTransversalRepr T y := by
  unfold rightTransversalRepr
  congr 2
  exact Quotient.eq''.mpr (QuotientGroup.rightRel_apply.mpr h)

lemma rightTransversalRepr_eq_self (T : P.RightTransversal) {t : G} (ht : t ∈ (T : Set G)) :
    rightTransversalRepr T t = t := by
  have hinj := (Subgroup.isComplement_subgroup_left_iff_bijective.mp T.2).1
  exact congrArg Subtype.val
    (hinj (a₁ := ⟨_, rightTransversalRepr_mem T t⟩) (a₂ := ⟨t, ht⟩)
      (mk''_rightTransversalRepr T t))

@[simp] lemma rightTransversalRepr_rightTransversalRepr (S T : P.RightTransversal) (x : G) :
    rightTransversalRepr S (rightTransversalRepr T x) = rightTransversalRepr S x :=
  (rightTransversalRepr_congr S (rightTransversalRepr_mul_inv_mem T x)).symm

@[simp] lemma rightTransversalRepr_mul_right (S T : P.RightTransversal) (x g : G) :
    rightTransversalRepr T (rightTransversalRepr S x * g)
      = rightTransversalRepr T (x * g) := by
  refine rightTransversalRepr_congr T ?_
  have h : x * g * (rightTransversalRepr S x * g)⁻¹ = x * (rightTransversalRepr S x)⁻¹ := by
    group
  rw [h]
  exact mul_inv_rightTransversalRepr_mem S x

instance instFiniteRightTransversal [P.FiniteIndex] (T : P.RightTransversal) :
    Finite ↥(T : Set G) := by
  have : Finite (G ⧸ P) := P.finite_quotient_of_finiteIndex
  have : Finite (Quotient (rightRel P)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel P).symm
  exact Finite.of_equiv _ T.2.rightQuotientEquiv

noncomputable def rightTransversalEquiv (S T : P.RightTransversal) (g : G) :
    (S : Set G) ≃ (T : Set G) where
  toFun s := ⟨rightTransversalRepr T (s * g), rightTransversalRepr_mem T _⟩
  invFun t := ⟨rightTransversalRepr S (t * g⁻¹), rightTransversalRepr_mem S _⟩
  left_inv s := by
    refine Subtype.ext ?_
    change rightTransversalRepr S (rightTransversalRepr T ((s : G) * g) * g⁻¹) = (s : G)
    rw [rightTransversalRepr_mul_right, mul_assoc, mul_inv_cancel, mul_one,
      rightTransversalRepr_eq_self S s.2]
  right_inv t := by
    refine Subtype.ext ?_
    change rightTransversalRepr T (rightTransversalRepr S ((t : G) * g⁻¹) * g) = (t : G)
    rw [rightTransversalRepr_mul_right, mul_assoc, inv_mul_cancel, mul_one,
      rightTransversalRepr_eq_self T t.2]

@[simp] lemma rightTransversalEquiv_apply (S T : P.RightTransversal) (g : G) (s : (S : Set G)) :
    (rightTransversalEquiv S T g s : G) = rightTransversalRepr T (s * g) := (rfl)

noncomputable def rightTransversalCocycle (T : P.RightTransversal) (g : G)
    (t : (T : Set G)) : P :=
  ⟨t * g * (rightTransversalRepr T (t * g))⁻¹, mul_inv_rightTransversalRepr_mem T _⟩

@[simp] lemma coe_rightTransversalCocycle (T : P.RightTransversal) (g : G) (t : (T : Set G)) :
    (rightTransversalCocycle T g t : G) = t * g * (rightTransversalRepr T (t * g))⁻¹ := (rfl)

lemma rightTransversalCocycle_one (T : P.RightTransversal) (t : (T : Set G)) :
    rightTransversalCocycle T 1 t = 1 := by
  refine Subtype.ext ?_
  rw [coe_rightTransversalCocycle]
  simp [rightTransversalRepr_eq_self T t.2]

lemma rightTransversalCocycle_mul (T : P.RightTransversal) (g h : G) (t : (T : Set G)) :
    rightTransversalCocycle T (g * h) t
      = rightTransversalCocycle T g t
          * rightTransversalCocycle T h (rightTransversalEquiv T T g t) := by
  refine Subtype.ext ?_
  push_cast
  simp only [rightTransversalEquiv_apply, coe_rightTransversalCocycle,
    rightTransversalRepr_mul_right]
  group

noncomputable def rightTransfer (f : P →* Q) (T : P.RightTransversal) (g : G) : Q :=
  ∏ᶠ t : (T : Set G), f (rightTransversalCocycle T g t)

lemma rightTransfer_eq_finprod (f : P →* Q) (T : P.RightTransversal) (g : G) :
    rightTransfer f T g = ∏ᶠ t : (T : Set G), f (rightTransversalCocycle T g t) := (rfl)

lemma rightTransfer_eq_prod (f : P →* Q) (T : P.RightTransversal) (g : G)
    [Fintype ↥(T : Set G)] :
    rightTransfer f T g = ∏ t : (T : Set G), f (rightTransversalCocycle T g t) :=
  finprod_eq_prod_of_fintype _

@[simp] lemma rightTransfer_one (f : P →* Q) (T : P.RightTransversal) :
    rightTransfer f T 1 = 1 := by
  rw [rightTransfer_eq_finprod]
  simp [rightTransversalCocycle_one]

lemma rightTransfer_mul (f : P →* Q) [P.FiniteIndex] (T : P.RightTransversal) (g h : G) :
    rightTransfer f T (g * h) = rightTransfer f T g * rightTransfer f T h := by
  have hfin : ∀ k : ↥(T : Set G) → Q, Function.HasFiniteMulSupport k := fun _ => Set.toFinite _
  calc rightTransfer f T (g * h)
      = ∏ᶠ t : (T : Set G), (f (rightTransversalCocycle T g t)
          * f (rightTransversalCocycle T h (rightTransversalEquiv T T g t))) := by
        rw [rightTransfer_eq_finprod]
        exact finprod_congr fun t => by rw [rightTransversalCocycle_mul, map_mul]
    _ = (∏ᶠ t : (T : Set G), f (rightTransversalCocycle T g t))
          * ∏ᶠ t : (T : Set G), f (rightTransversalCocycle T h (rightTransversalEquiv T T g t)) :=
        finprod_mul_distrib (hfin _) (hfin _)
    _ = rightTransfer f T g * rightTransfer f T h := by
        rw [finprod_comp_equiv (rightTransversalEquiv T T g)
          (f := fun t => f (rightTransversalCocycle T h t)), ← rightTransfer_eq_finprod,
          ← rightTransfer_eq_finprod]

theorem rightTransfer_indep (f : P →* Q) [P.FiniteIndex] (S T : P.RightTransversal) (g : G) :
    rightTransfer f S g = rightTransfer f T g := by
  set b : ↥(S : Set G) → P := fun s => ⟨(s : G) * (rightTransversalRepr T (s : G))⁻¹,
    mul_inv_rightTransversalRepr_mem T _⟩ with hb
  set e : (S : Set G) ≃ (T : Set G) := rightTransversalEquiv S T 1 with he
  set τ : (S : Set G) ≃ (S : Set G) := rightTransversalEquiv S S g with hτ
  have hfin : ∀ k : ↥(S : Set G) → Q, Function.HasFiniteMulSupport k := fun _ => Set.toFinite _
  have key : ∀ s : (S : Set G),
      f (rightTransversalCocycle S g s)
        = f (b s) * f (rightTransversalCocycle T g (e s)) * (f (b (τ s)))⁻¹ := by
    intro s
    have hmul : rightTransversalCocycle S g s
        = b s * rightTransversalCocycle T g (e s) * (b (τ s))⁻¹ := by
      refine Subtype.ext ?_
      push_cast [hb, he, hτ]
      simp only [rightTransversalEquiv_apply, mul_one, coe_rightTransversalCocycle,
        rightTransversalRepr_mul_right, rightTransversalRepr_rightTransversalRepr]
      group
    rw [hmul, map_mul, map_mul, map_inv]
  calc rightTransfer f S g
      = ∏ᶠ s : (S : Set G),
          (f (b s) * f (rightTransversalCocycle T g (e s)) * (f (b (τ s)))⁻¹) := by
        rw [rightTransfer_eq_finprod]; exact finprod_congr key
    _ = ((∏ᶠ s : (S : Set G), f (b s)) * ∏ᶠ s : (S : Set G),
            f (rightTransversalCocycle T g (e s))) * ∏ᶠ s : (S : Set G), (f (b (τ s)))⁻¹ := by
        rw [finprod_mul_distrib (hfin _) (hfin _), finprod_mul_distrib (hfin _) (hfin _)]
    _ = ((∏ᶠ s : (S : Set G), f (b s)) * rightTransfer f T g)
          * (∏ᶠ s : (S : Set G), f (b s))⁻¹ := by
        rw [finprod_comp_equiv e (f := fun t => f (rightTransversalCocycle T g t)),
          ← rightTransfer_eq_finprod, finprod_inv_distrib,
          finprod_comp_equiv τ (f := fun s => f (b s))]
    _ = rightTransfer f T g := by
        rw [mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.FeitThompson
