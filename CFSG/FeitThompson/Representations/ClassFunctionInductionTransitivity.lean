module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Basic.Complex.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace InductionTransitivity

open CategoryTheory

variable {G : Type*} [Group G]

def classFun (G : Type*) [Group G] : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ g x : G, f (x⁻¹ * g * x) = f g}
  add_mem' hf hg := fun a x => by simp [hf a x, hg a x]
  zero_mem' := fun _ _ => rfl
  smul_mem' c f hf := fun a x => by simp [hf a x]

lemma mem_classFun {f : G → ℂ} : f ∈ classFun G ↔ ∀ g x : G, f (x⁻¹ * g * x) = f g := Iff.rfl

lemma classFun.conj_eq {f : G → ℂ} (hf : f ∈ classFun G) (g x : G) : f (x⁻¹ * g * x) = f g :=
  hf g x

lemma classFun.conj_eq' {f : G → ℂ} (hf : f ∈ classFun G) (g x : G) : f (x * g * x⁻¹) = f g := by
  simpa using hf g x⁻¹

lemma character_mem_classFun (V : FDRep ℂ G) : V.character ∈ classFun G := fun g x => by
  simpa using V.char_conj g x⁻¹

noncomputable def classFunInner [Finite G] (f h : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G, f g * (starRingEnd ℂ) (h g)

omit [Group G] in
lemma classFunInner_apply [Fintype G] (f h : G → ℂ) :
    classFunInner f h = (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * (starRingEnd ℂ) (h g) := by
  rw [classFunInner, finsum_eq_sum_of_fintype]

omit [Group G] in
lemma classFunInner_comm [Finite G] (f h : G → ℂ) :
    classFunInner f h = (starRingEnd ℂ) (classFunInner h f) := by
  let _ := Fintype.ofFinite G
  simp only [classFunInner_apply, map_mul, map_sum, map_inv₀, Complex.conj_natCast,
    Complex.conj_conj]
  exact congrArg _ (Finset.sum_congr rfl fun g _ => mul_comm _ _)

omit [Group G] in
lemma classFunInner_add_left [Finite G] (f₁ f₂ h : G → ℂ) :
    classFunInner (f₁ + f₂) h = classFunInner f₁ h + classFunInner f₂ h := by
  let _ := Fintype.ofFinite G
  simp only [classFunInner_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

omit [Group G] in
lemma classFunInner_smul_left [Finite G] (c : ℂ) (f h : G → ℂ) :
    classFunInner (c • f) h = c * classFunInner f h := by
  let _ := Fintype.ofFinite G
  simp only [classFunInner_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

def irrCharSet (G : Type*) [Group G] : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ}

lemma mem_irrCharSet_iff {χ : G → ℂ} :
    χ ∈ irrCharSet G ↔ ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ := Iff.rfl

lemma character_mem_irrCharSet (V : FDRep ℂ G) [Simple V] : V.character ∈ irrCharSet G :=
  ⟨V, ‹_›, rfl⟩

lemma irrCharSet_subset_classFun : irrCharSet G ⊆ classFun G := by
  rintro χ ⟨V, -, rfl⟩
  exact character_mem_classFun V

def resClassFun (H : Subgroup G) (f : G → ℂ) : H → ℂ := f ∘ H.subtype

@[simp] lemma resClassFun_apply (H : Subgroup G) (f : G → ℂ) (x : H) :
    resClassFun H f x = f (x : G) := (rfl)

lemma resClassFun_mem_classFun {H : Subgroup G} {f : G → ℂ} (hf : f ∈ classFun G) :
    resClassFun H f ∈ classFun H := fun g x => by
  simpa using hf (g : G) (x : G)

noncomputable def extendByZero (H : Subgroup G) (f : H → ℂ) : G → ℂ :=
  Function.extend H.subtype f 0

@[simp]
lemma extendByZero_apply_coe (H : Subgroup G) (f : H → ℂ) (x : H) :
    extendByZero H f (x : G) = f x :=
  H.subtype_injective.extend_apply f 0 x

lemma extendByZero_of_mem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∈ H) :
    extendByZero H f g = f ⟨g, hg⟩ :=
  extendByZero_apply_coe H f ⟨g, hg⟩

lemma extendByZero_of_notMem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∉ H) :
    extendByZero H f g = 0 := by
  rw [extendByZero, Function.extend_apply' _ _ _ (by rintro ⟨a, rfl⟩; exact hg a.2)]
  rfl

@[simp] lemma extendByZero_zero (H : Subgroup G) : extendByZero H (0 : H → ℂ) = 0 := by
  funext g
  by_cases hg : g ∈ H
  · rw [extendByZero_of_mem _ _ hg]; rfl
  · rw [extendByZero_of_notMem _ _ hg]; rfl

lemma extendByZero_add (H : Subgroup G) (f₁ f₂ : H → ℂ) :
    extendByZero H (f₁ + f₂) = extendByZero H f₁ + extendByZero H f₂ := by
  funext g
  by_cases hg : g ∈ H
  · simp [extendByZero_of_mem _ _ hg]
  · simp [extendByZero_of_notMem _ _ hg]

lemma extendByZero_smul (H : Subgroup G) (c : ℂ) (f : H → ℂ) :
    extendByZero H (c • f) = c • extendByZero H f := by
  funext g
  by_cases hg : g ∈ H
  · simp [extendByZero_of_mem _ _ hg]
  · simp [extendByZero_of_notMem _ _ hg]

noncomputable def indClassFun [Finite G] (H : Subgroup G) (f : H → ℂ) (g : G) : ℂ :=
  (Nat.card H : ℂ)⁻¹ * ∑ᶠ x : G, extendByZero H f (x⁻¹ * g * x)

lemma indClassFun_apply [Fintype G] (H : Subgroup G) (f : H → ℂ) (g : G) :
    indClassFun H f g = (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendByZero H f (x⁻¹ * g * x) := by
  rw [indClassFun, finsum_eq_sum_of_fintype]

lemma indClassFun_mem_classFun [Finite G] (H : Subgroup G) (f : H → ℂ) :
    indClassFun H f ∈ classFun G := by
  let _ := Fintype.ofFinite G
  intro g x
  rw [indClassFun_apply, indClassFun_apply]
  refine congrArg _ ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft x) fun y => extendByZero H f (y⁻¹ * g * y)]
  exact Finset.sum_congr rfl fun y _ => by simp [mul_assoc]

lemma indClassFun_eq_zero_of_forall_notMem [Finite G] (H : Subgroup G) (f : H → ℂ) {g : G}
    (hg : ∀ x : G, x⁻¹ * g * x ∉ H) : indClassFun H f g = 0 := by
  let _ := Fintype.ofFinite G
  rw [indClassFun_apply, Finset.sum_eq_zero fun x _ => extendByZero_of_notMem _ _ (hg x), mul_zero]

@[simp] lemma indClassFun_zero [Finite G] (H : Subgroup G) : indClassFun H (0 : H → ℂ) = 0 := by
  let _ := Fintype.ofFinite G
  funext g
  simp [indClassFun_apply]

lemma indClassFun_add [Finite G] (H : Subgroup G) (f₁ f₂ : H → ℂ) :
    indClassFun H (f₁ + f₂) = indClassFun H f₁ + indClassFun H f₂ := by
  let _ := Fintype.ofFinite G
  funext g
  simp only [indClassFun_apply, extendByZero_add, Pi.add_apply, Finset.sum_add_distrib]
  ring

lemma indClassFun_smul [Finite G] (H : Subgroup G) (c : ℂ) (f : H → ℂ) :
    indClassFun H (c • f) = c • indClassFun H f := by
  let _ := Fintype.ofFinite G
  funext g
  simp only [indClassFun_apply, extendByZero_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma indClassFun_top [Finite G] (f : (⊤ : Subgroup G) → ℂ) (g : G) :
    indClassFun ⊤ f g = (Nat.card G : ℂ)⁻¹ * ∑ᶠ x : G, f ⟨x⁻¹ * g * x, Subgroup.mem_top _⟩ := by
  rw [indClassFun, Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv]
  exact congrArg _ (finsum_congr fun x => extendByZero_of_mem _ _ (Subgroup.mem_top _))

lemma extendByZero_subgroupOf (H K : Subgroup G) (hHK : H ≤ K) (f : H → ℂ) (v : K) :
    extendByZero (H.subgroupOf K) (f ∘ Subgroup.subgroupOfEquivOfLe hHK) v
      = extendByZero H f (v : G) := by
  by_cases hv : v ∈ H.subgroupOf K
  · rw [extendByZero_of_mem _ _ hv, extendByZero_of_mem _ _ (Subgroup.mem_subgroupOf.mp hv)]
    simp [Subgroup.subgroupOfEquivOfLe]
  · rw [extendByZero_of_notMem _ _ hv,
      extendByZero_of_notMem _ _ fun h => hv (Subgroup.mem_subgroupOf.mpr h)]

theorem indClassFun_indClassFun [Finite G] (H K : Subgroup G) (hHK : H ≤ K) (f : H → ℂ) :
    indClassFun K (indClassFun (H.subgroupOf K) (f ∘ Subgroup.subgroupOfEquivOfLe hHK))
      = indClassFun H f := by
  classical
  let _ := Fintype.ofFinite G
  have hcard : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hKne : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  funext g
  rw [indClassFun_apply, indClassFun_apply]
  have key : ∀ x : G, extendByZero K
      (indClassFun (H.subgroupOf K) (f ∘ Subgroup.subgroupOfEquivOfLe hHK)) (x⁻¹ * g * x)
      = (Nat.card H : ℂ)⁻¹ * ∑ u : K, extendByZero H f ((x * u)⁻¹ * g * (x * u)) := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ K
    · rw [extendByZero_of_mem _ _ hx, indClassFun_apply, hcard]
      refine congrArg _ (Finset.sum_congr rfl fun u _ => ?_)
      rw [extendByZero_subgroupOf H K hHK f]
      refine congrArg _ ?_
      push_cast
      group
    · rw [extendByZero_of_notMem _ _ hx, Finset.sum_eq_zero, mul_zero]
      intro u _
      refine extendByZero_of_notMem _ _ fun hmem => hx ?_
      have hm : (u : G) * ((x * u)⁻¹ * g * (x * u)) * (u : G)⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem u.2 (hHK hmem)) (K.inv_mem u.2)
      have heq : (u : G) * ((x * u)⁻¹ * g * (x * u)) * (u : G)⁻¹ = x⁻¹ * g * x := by group
      rwa [heq] at hm
  rw [Finset.sum_congr rfl fun x _ => key x, ← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ u : K, ∑ x : G, extendByZero H f ((x * u)⁻¹ * g * (x * u))
      = ∑ x : G, extendByZero H f (x⁻¹ * g * x) := fun u =>
    Fintype.sum_equiv (Equiv.mulRight (u : G)) _ _ fun _ => rfl
  rw [Finset.sum_congr rfl fun u _ => hinner u, Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, nsmul_eq_mul]
  field_simp

end InductionTransitivity

end CFSG.FeitThompson
