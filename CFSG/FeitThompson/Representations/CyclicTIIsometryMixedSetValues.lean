module

public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
public import CFSG.FeitThompson.Representations.OddCyclicFactorOrders
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped ComplexConjugate

theorem one_mem_classFun (X : Type*) [Group X] : (1 : X → ℂ) ∈ classFun X :=
  mem_classFun.2 fun _ _ _ => rfl

def principalClassFun (X : Type*) [Group X] : classFun X := ⟨1, one_mem_classFun X⟩

@[simp]
theorem coe_principalClassFun (X : Type*) [Group X] : (principalClassFun X : X → ℂ) = 1 := (rfl)

@[simp]
theorem principalClassFun_apply {X : Type*} [Group X] (x : X) :
    (principalClassFun X : X → ℂ) x = 1 := (rfl)

theorem single_mem_classFun {X : Type*} [Group X] [IsMulCommutative X] [DecidableEq X] (v : X)
    (c : ℂ) : (Pi.single v c : X → ℂ) ∈ classFun X := by
  refine mem_classFun.2 fun x y hxy => ?_
  obtain ⟨u, hu⟩ := isConj_iff.mp hxy
  rw [← hu, mul_comm' u x, mul_assoc, mul_inv_cancel, mul_one]

theorem cfInner_single {X : Type*} [Fintype X] [DecidableEq X] (k : X → ℂ) (v : X) :
    cfInner k (Pi.single v 1 : X → ℂ) = (Nat.card X : ℂ)⁻¹ * k v := by
  have hstep : ∀ x : X, k x * conj ((Pi.single v 1 : X → ℂ) x) = if x = v then k x else 0 := by
    intro x
    rw [Pi.single_apply]
    split <;> simp
  rw [cfInner_def, Finset.sum_congr rfl fun x _ => hstep x,
    Finset.sum_ite_eq' Finset.univ v k, if_pos (Finset.mem_univ v)]

variable {G : Type*} [Group G] [Fintype G]

structure IsCyclicTIIsometry (W W1 W2 : Subgroup G) [Fintype W]
    (σ : classFun ↥W →ₗ[ℂ] classFun G) : Prop where
  inner_eq : ∀ f h : classFun ↥W,
    cfInner (σ f : G → ℂ) (σ h : G → ℂ) = cfInner (f : ↥W → ℂ) (h : ↥W → ℂ)
  map_virtualChars : ∀ f : classFun ↥W,
    (f : ↥W → ℂ) ∈ virtualChars ↥W → (σ f : G → ℂ) ∈ virtualChars G
  map_principalClassFun : σ (principalClassFun ↥W) = principalClassFun G
  eq_indClassFun : ∀ f : classFun ↥W,
    (∀ x : ↥W, (x : G) ∉ cyclicTIDiff W W1 W2 → (f : ↥W → ℂ) x = 0) →
    (σ f : G → ℂ) = indClassFun W (f : ↥W → ℂ)

namespace IsCyclicTIIsometry

variable {W W1 W2 : Subgroup G} [Fintype W] {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem inner_self_eq (hσ : IsCyclicTIIsometry W W1 W2 σ) (f : classFun ↥W) :
    cfInner (σ f : G → ℂ) (σ f : G → ℂ) = cfInner (f : ↥W → ℂ) (f : ↥W → ℂ) :=
  hσ.inner_eq f f

theorem apply_eq_of_mem_cyclicTIDiff (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (f : classFun ↥W) {v : ↥W}
    (hv : (v : G) ∈ cyclicTIDiff W W1 W2) : (σ f : G → ℂ) (v : G) = (f : ↥W → ℂ) v := by
  classical
  have hcyc := hW.isCyclic
  set p : ↥W → ℂ := Pi.single v 1 with hp
  set pcf : classFun ↥W := ⟨p, single_mem_classFun v 1⟩ with hpcf
  have hσp : (σ pcf : G → ℂ) = indClassFun W p := by
    refine hσ.eq_indClassFun pcf fun x hx => ?_
    change p x = 0
    rw [hp, Pi.single_eq_of_ne']
    intro hxv
    exact hx (hxv ▸ hv)
  have h1 : cfInner (σ f : G → ℂ) (indClassFun W p) = cfInner (f : ↥W → ℂ) p := by
    rw [← hσp]
    exact hσ.inner_eq f pcf
  have h2 : cfInner (indClassFun W p) (σ f : G → ℂ)
      = cfInner p (resClassFun W (σ f : G → ℂ)) :=
    cfInner_indClassFun W p (σ f).2
  have h3 : cfInner (resClassFun W (σ f : G → ℂ)) p = cfInner (f : ↥W → ℂ) p := by
    rw [← h1, ← conj_cfInner, ← h2]
    exact conj_cfInner _ _
  rw [hp, cfInner_single, cfInner_single, resClassFun_apply] at h3
  have hne : (Nat.card ↥W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact mul_left_cancel₀ (inv_ne_zero hne) h3

theorem apply_eq_of_mem_cyclicTIDiff' (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (f : classFun ↥W) {v : G}
    (hv : v ∈ cyclicTIDiff W W1 W2) :
    (σ f : G → ℂ) v = (f : ↥W → ℂ) ⟨v, cyclicTIDiff_subset hv⟩ :=
  hσ.apply_eq_of_mem_cyclicTIDiff hW f (v := ⟨v, cyclicTIDiff_subset hv⟩) hv

theorem eqOn_cyclicTIDiff (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    {f h : classFun ↥W}
    (hfh : ∀ x : ↥W, (x : G) ∈ cyclicTIDiff W W1 W2 → (f : ↥W → ℂ) x = (h : ↥W → ℂ) x) :
    Set.EqOn (σ f : G → ℂ) (σ h : G → ℂ) (cyclicTIDiff W W1 W2) := by
  intro v hv
  rw [hσ.apply_eq_of_mem_cyclicTIDiff' hW f hv, hσ.apply_eq_of_mem_cyclicTIDiff' hW h hv]
  exact hfh _ hv

end IsCyclicTIIsometry

end

end CFSG.FeitThompson
