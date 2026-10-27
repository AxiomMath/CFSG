module

public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.Algebra.Module.Hom
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Module.Equiv.Defs

public section

namespace CFSG.ComponentClassification.GMS78

namespace Singer

variable {A : Type} [CommGroup A]

@[expose] def toEnd : MulAut A →* AddMonoid.End (Additive A) where
  toFun f := (MulEquiv.toAdditive f).toAddMonoidHom
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toEnd_apply (f : MulAut A) (x : Additive A) :
    toEnd f x = Additive.ofMul (f (Additive.toMul x)) := rfl

variable (s : MulAut A) (E : Set ℕ)

@[expose] def ring : Subring (AddMonoid.End (Additive A)) :=
  Subring.closure ((fun m : ℕ => toEnd (s ^ m)) '' E)

theorem pow_mem_ring {m : ℕ} (hm : m ∈ E) : toEnd (s ^ m) ∈ ring s E :=
  Subring.subset_closure ⟨m, hm, rfl⟩

theorem ring_le_centralizer : ring s E ≤ Subring.centralizer {toEnd s} := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨m, -, rfl⟩
  rw [SetLike.mem_coe, Subring.mem_centralizer_iff]
  rintro _ rfl
  rw [← map_mul, ← map_mul, ← pow_succ', pow_succ]

theorem ring_le_centralizer_of_commute {f : MulAut A} (hf : ∀ m ∈ E, f * s ^ m = s ^ m * f) :
    ring s E ≤ Subring.centralizer {toEnd f} := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, Subring.mem_centralizer_iff]
  rintro _ rfl
  rw [← map_mul, ← map_mul, hf m hm]

variable {s}

theorem injective_of_commute (hs : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ m : ℕ, (s ^ m) a = b)
    {D : AddMonoid.End (Additive A)} (hD : D * toEnd s = toEnd s * D) (hD0 : D ≠ 0) :
    Function.Injective D := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  apply hD0
  have hc : Commute D (toEnd s) := hD
  ext b
  by_cases hb : b = 0
  · rw [hb, map_zero]
    rfl
  obtain ⟨m, hm⟩ := hs (Additive.toMul a) (Additive.toMul b)
    (fun h => ha0 (by simpa using congrArg Additive.ofMul h))
    (fun h => hb (by simpa using congrArg Additive.ofMul h))
  have h1 : b = toEnd (s ^ m) a := by
    rw [toEnd_apply, hm]
    rfl
  have h2 := (hc.pow_right m).eq
  rw [← map_pow] at h2
  have h3 : D (toEnd (s ^ m) a) = toEnd (s ^ m) (D a) := congrArg (fun F => F a) h2
  rw [h1, h3, ha, map_zero]
  rfl

theorem isDomain [Nontrivial A] (hs : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ m : ℕ, (s ^ m) a = b) :
    IsDomain (ring s E) := by
  have hnt : Nontrivial (ring s E) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have h1 := congrArg (fun r : ring s E => (r : AddMonoid.End (Additive A)) (Additive.ofMul a)) h
    simp only [ZeroMemClass.coe_zero, OneMemClass.coe_one] at h1
    exact ha (by simpa using congrArg Additive.toMul h1.symm)
  have hnzd : NoZeroDivisors (ring s E) := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨hx, hy⟩ := hne
    have hx' : (x : AddMonoid.End (Additive A)) ≠ 0 := fun h => hx (Subtype.ext h)
    have hy' : (y : AddMonoid.End (Additive A)) ≠ 0 := fun h => hy (Subtype.ext h)
    have hcx := Subring.mem_centralizer_iff.mp (ring_le_centralizer s E x.2) (toEnd s) rfl
    have hinj := injective_of_commute hs hcx.symm hx'
    apply hy'
    ext a
    have h1 : (x : AddMonoid.End (Additive A)) ((y : AddMonoid.End (Additive A)) a) = 0 :=
      congrArg (fun r : ring s E => (r : AddMonoid.End (Additive A)) a) hxy
    exact hinj (h1.trans (map_zero _).symm)
  exact NoZeroDivisors.to_isDomain _

theorem isField [Finite A] [Nontrivial A]
    (hs : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ m : ℕ, (s ^ m) a = b) : IsField (ring s E) := by
  have := isDomain E hs
  have : Finite (Additive A) := inferInstanceAs (Finite A)
  have : Finite (AddMonoid.End (Additive A)) := DFunLike.finite _
  exact Finite.isDomain_to_isField _

variable (s)

@[expose] def linEquiv {f : MulAut A} (hf : ∀ m ∈ E, f * s ^ m = s ^ m * f) :
    Additive A ≃ₗ[ring s E] Additive A :=
  { MulEquiv.toAdditive f with
    map_smul' := fun r x => by
      have h1 := Subring.mem_centralizer_iff.mp (ring_le_centralizer_of_commute s E hf r.2)
        (toEnd f) rfl
      change toEnd f ((r : AddMonoid.End (Additive A)) x) =
        (r : AddMonoid.End (Additive A)) (toEnd f x)
      exact congrArg (fun F : AddMonoid.End (Additive A) => F x) h1 }

end Singer

end CFSG.ComponentClassification.GMS78
