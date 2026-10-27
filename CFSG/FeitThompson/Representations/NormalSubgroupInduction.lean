module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.GroupTheory.Complement
public import Mathlib.Basic.Complex.Basic

open scoped ComplexConjugate

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace NormalInduction

variable {G : Type*} [Group G]

section ClassFunctions

def classFun (G : Type*) [Group G] : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ x g : G, f (x * g * x⁻¹) = f g}
  add_mem' {f h} hf hg := fun x g => by simp only [Pi.add_apply, hf x g, hg x g]
  zero_mem' := fun _ _ => rfl
  smul_mem' c f hf := fun x g => by simp only [Pi.smul_apply, hf x g]

lemma mem_classFun {f : G → ℂ} : f ∈ classFun G ↔ ∀ x g : G, f (x * g * x⁻¹) = f g := Iff.rfl

noncomputable def classFunInner [Fintype G] (f h : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * conj (h g)

omit [Group G] in
lemma classFunInner_def [Fintype G] (f h : G → ℂ) :
    classFunInner f h = (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * conj (h g) := (rfl)

omit [Group G] in
lemma classFunInner_conj [Fintype G] (f h : G → ℂ) :
    conj (classFunInner f h) = classFunInner h f := by
  simp only [classFunInner_def, map_mul, map_sum, map_inv₀, Complex.conj_natCast,
    Complex.conj_conj]
  ring_nf
  simp [mul_comm]

end ClassFunctions

section Irr

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [Group W]

def subrepresentationCompEquiv (ρ : Representation k G V) (e : W ≃* G) :
    Subrepresentation (ρ.comp e.toMonoidHom : Representation k W V) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    simpa using U.apply_mem_toSubmodule (e.symm g) hv⟩
  invFun U := ⟨U.toSubmodule, fun h v hv => U.apply_mem_toSubmodule (e h) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

lemma isIrreducible_comp_mulEquiv {ρ : Representation k G V} (hρ : ρ.IsIrreducible) (e : W ≃* G) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom : Representation k W V) :=
  (subrepresentationCompEquiv ρ e).isSimpleOrder

lemma character_comp_mulEquiv (ρ : Representation k G V) (e : W ≃* G) (w : W) :
    Representation.character (ρ.comp e.toMonoidHom : Representation k W V) w
      = ρ.character (e w) := (rfl)

def irrChars (G : Type*) [Group G] : Set (G → ℂ) :=
  {χ | ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ G V),
        FiniteDimensional ℂ V ∧ ρ.IsIrreducible ∧ ρ.character = χ}

lemma mem_irrChars_iff {χ : G → ℂ} :
    χ ∈ irrChars G ↔ ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ G V), FiniteDimensional ℂ V ∧ ρ.IsIrreducible ∧ ρ.character = χ :=
  Iff.rfl

lemma character_mem_irrChars {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) : ρ.character ∈ irrChars G :=
  ⟨V, _, _, ρ, ‹_›, hρ, rfl⟩

lemma irrChars_subset_classFun : irrChars G ⊆ classFun G := by
  rintro χ ⟨V, _, _, ρ, _, _, rfl⟩ x g
  exact ρ.char_conj g x

lemma mem_irrChars_comp_mulEquiv {χ : G → ℂ} (hχ : χ ∈ irrChars G) (e : W ≃* G) :
    χ ∘ e ∈ irrChars W := by
  obtain ⟨V, _, _, ρ, _, hρ, rfl⟩ := hχ
  exact ⟨V, _, _, ρ.comp e.toMonoidHom, ‹_›, isIrreducible_comp_mulEquiv hρ e, rfl⟩

end Irr

section Induction

noncomputable def extendByZero (H : Subgroup G) (f : H → ℂ) : G → ℂ :=
  Function.extend H.subtype f 0

@[simp] lemma extendByZero_apply_coe (H : Subgroup G) (f : H → ℂ) (h : H) :
    extendByZero H f (h : G) = f h := H.subtype_injective.extend_apply f 0 h

lemma extendByZero_of_notMem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∉ H) :
    extendByZero H f g = 0 := by
  rw [extendByZero, Function.extend_apply' _ _ _ (by rintro ⟨a, rfl⟩; exact hg a.2)]
  rfl

def resClassFun (H : Subgroup G) (f : G → ℂ) : H → ℂ := fun h => f (h : G)

@[simp] lemma resClassFun_apply (H : Subgroup G) (f : G → ℂ) (h : H) :
    resClassFun H f h = f (h : G) := (rfl)

lemma resClassFun_mem_classFun (H : Subgroup G) {f : G → ℂ} (hf : f ∈ classFun G) :
    resClassFun H f ∈ classFun H := fun x g => by
  simpa [resClassFun] using hf (x : G) (g : G)

noncomputable def indClassFun [Fintype G] (H : Subgroup G) (f : H → ℂ) : G → ℂ := fun g =>
  (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendByZero H f (x⁻¹ * g * x)

lemma indClassFun_apply [Fintype G] (H : Subgroup G) (f : H → ℂ) (g : G) :
    indClassFun H f g = (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendByZero H f (x⁻¹ * g * x) := (rfl)

lemma indClassFun_mem_classFun [Fintype G] (H : Subgroup G) (f : H → ℂ) :
    indClassFun H f ∈ classFun G := by
  intro y g
  rw [indClassFun_apply, indClassFun_apply]
  congr 1
  refine Fintype.sum_bijective (fun x => y⁻¹ * x) (Group.mulLeft_bijective y⁻¹) _ _ fun x => ?_
  congr 1
  group

def conjClassFun (N : Subgroup G) [N.Normal] (t : G) (f : N → ℂ) : N → ℂ :=
  f ∘ MulAut.conjNormal t⁻¹

lemma conjClassFun_apply (N : Subgroup G) [N.Normal] (t : G) (f : N → ℂ) (n : N) :
    conjClassFun N t f n = f (MulAut.conjNormal t⁻¹ n) := (rfl)

lemma coe_conjNormal_inv (N : Subgroup G) [N.Normal] (t : G) (n : N) :
    ((MulAut.conjNormal t⁻¹ n : N) : G) = t⁻¹ * (n : G) * t := by simp

lemma conjClassFun_mem_classFun (N : Subgroup G) [N.Normal] (t : G) {f : N → ℂ}
    (hf : f ∈ classFun N) : conjClassFun N t f ∈ classFun N := fun x g => by
  simpa [conjClassFun_apply, map_mul, map_inv] using hf (MulAut.conjNormal t⁻¹ x)
    (MulAut.conjNormal t⁻¹ g)

theorem conjClassFun_mem_irrChars (N : Subgroup G) [N.Normal] (t : G) {f : N → ℂ}
    (hf : f ∈ irrChars N) : conjClassFun N t f ∈ irrChars N :=
  mem_irrChars_comp_mulEquiv hf (MulAut.conjNormal (H := N) t⁻¹)

theorem indClassFun_eq_zero_of_notMem [Fintype G] (N : Subgroup G) [N.Normal] (f : N → ℂ)
    {g : G} (hg : g ∉ N) : indClassFun N f g = 0 := by
  rw [indClassFun_apply]
  have h : ∀ x : G, extendByZero N f (x⁻¹ * g * x) = 0 := fun x =>
    extendByZero_of_notMem N f fun hmem => hg (by
      have h2 : x * (x⁻¹ * g * x) * x⁻¹ ∈ N := ‹N.Normal›.conj_mem _ hmem x
      simpa [mul_assoc] using h2)
  simp [h]

theorem indClassFun_apply_of_mem [Fintype G] (N : Subgroup G) [N.Normal] {f : N → ℂ}
    (hf : f ∈ classFun N) {T : Finset G}
    (hT : Subgroup.IsComplement (T : Set G) (N : Set G)) (n : N) :
    indClassFun N f (n : G) = ∑ t ∈ T, conjClassFun N t f n := by
  classical
  have key : ∑ x : G, extendByZero N f (x⁻¹ * (n : G) * x)
      = (Nat.card N : ℂ) * ∑ t ∈ T, conjClassFun N t f n := by
    rw [← Equiv.sum_comp hT.equiv.symm (fun x : G => extendByZero N f (x⁻¹ * (n : G) * x)),
      Fintype.sum_prod_type]
    simp only [Subgroup.IsComplement.equiv_symm_apply]
    have inner : ∀ (t : ↑(T : Set G)) (m : ↑(N : Set G)),
        extendByZero N f (((t : G) * (m : G))⁻¹ * (n : G) * ((t : G) * (m : G)))
          = conjClassFun N (t : G) f n := by
      intro t m
      set mm : N := ⟨(m : G), m.2⟩ with hmm
      have h1 : ((t : G) * (m : G))⁻¹ * (n : G) * ((t : G) * (m : G))
          = ((mm⁻¹ * MulAut.conjNormal (t : G)⁻¹ n * mm : N) : G) := by
        push_cast [MulAut.conjNormal_apply, hmm]
        group
      rw [h1, extendByZero_apply_coe, conjClassFun_apply]
      simpa using hf mm⁻¹ (MulAut.conjNormal (t : G)⁻¹ n)
    simp only [inner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_finset_coe (fun t => conjClassFun N t f n) T]
    congr 1
    rw [Nat.card_eq_fintype_card]
    norm_cast
  rw [indClassFun_apply, key, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Nat.cast_ne_zero.2 Nat.card_pos.ne'

end Induction

end NormalInduction

end

end CFSG.FeitThompson
