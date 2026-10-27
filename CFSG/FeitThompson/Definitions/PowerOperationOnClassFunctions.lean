module

public import Mathlib.RepresentationTheory.Character

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} {M : Type*}

def IsClassFun [Monoid G] (f : G → M) : Prop := ∀ ⦃g h : G⦄, IsConj g h → f g = f h

section Monoid
variable [Monoid G]

theorem IsClassFun.apply_eq {f : G → M} (hf : IsClassFun f) {g h : G} (hgh : IsConj g h) :
    f g = f h := hf hgh

theorem isClassFun_const (m : M) : IsClassFun (Function.const G m) := fun _ _ _ => rfl

end Monoid

section Group
variable [Group G]

theorem isClassFun_iff {f : G → M} : IsClassFun f ↔ ∀ x g : G, f (x * g * x⁻¹) = f g := by
  refine ⟨fun hf x g => (hf (isConj_iff.2 ⟨x, rfl⟩)).symm, fun hf g h hgh => ?_⟩
  obtain ⟨x, rfl⟩ := isConj_iff.1 hgh
  exact (hf x g).symm

theorem IsClassFun.conj {f : G → M} (hf : IsClassFun f) (x g : G) : f (x * g * x⁻¹) = f g :=
  isClassFun_iff.1 hf x g

theorem isClassFun_character {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : IsClassFun ρ.character :=
  isClassFun_iff.2 fun x g => ρ.char_conj g x

theorem isClassFun_fdRep_character {k : Type*} [Field k] (V : FDRep k G) :
    IsClassFun V.character :=
  isClassFun_iff.2 fun x g => V.char_conj g x

end Group

def classFunctions (R : Type*) (M : Type*) (G : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [Monoid G] : Submodule R (G → M) where
  carrier := {f | IsClassFun f}
  add_mem' hf hg _ _ h := by simp [hf h, hg h]
  zero_mem' _ _ _ := rfl
  smul_mem' c _ hf _ _ h := by simp [hf h]

@[simp]
theorem mem_classFunctions {R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Monoid G]
    {f : G → M} : f ∈ classFunctions R M G ↔ IsClassFun f := Iff.rfl

def powOp [Monoid G] (n : ℕ) (f : G → M) : G → M := fun g => f (g ^ n)

section Monoid
variable [Monoid G]

@[simp]
theorem powOp_apply (n : ℕ) (f : G → M) (g : G) : powOp n f g = f (g ^ n) := (rfl)

@[simp]
theorem powOp_one (f : G → M) : powOp 1 f = f := by ext g; simp

theorem powOp_zero (f : G → M) : powOp 0 f = Function.const G (f 1) := by
  ext g; simp [Function.const]

theorem powOp_powOp (m n : ℕ) (f : G → M) : powOp m (powOp n f) = powOp (m * n) f := by
  ext g; simp [pow_mul]

theorem IsClassFun.powOp {f : G → M} (hf : IsClassFun f) (n : ℕ) : IsClassFun (powOp n f) :=
  fun _ _ h => hf (h.pow n)

end Monoid

def powOpₗ (R : Type*) (M : Type*) (G : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [Monoid G] (n : ℕ) : classFunctions R M G →ₗ[R] classFunctions R M G :=
  (LinearMap.funLeft R M (· ^ n)).restrict fun _ hf => (mem_classFunctions.1 hf).powOp n

@[simp]
theorem coe_powOpₗ_apply {R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Monoid G]
    (n : ℕ) (f : classFunctions R M G) :
    ((powOpₗ R M G n f : G → M)) = powOp n (f : G → M) := (rfl)

theorem powOpₗ_apply_apply {R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Monoid G]
    (n : ℕ) (f : classFunctions R M G) (g : G) :
    (powOpₗ R M G n f : G → M) g = (f : G → M) (g ^ n) := by
  simp

@[simp]
theorem powOpₗ_one (R : Type*) (M : Type*) (G : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [Monoid G] : powOpₗ R M G 1 = LinearMap.id := by
  ext f g
  simp

end CFSG.FeitThompson
