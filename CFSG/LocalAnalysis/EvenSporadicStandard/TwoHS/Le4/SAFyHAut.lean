module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.TypeTags.Finite

public section

namespace CFSG.EvenSporadicStandard.TwoHS

namespace SAFyHAut

section Simple

variable {A : Type*} [Group A]

theorem hom_eq_one_or_injective [IsSimpleGroup A] {B : Type*} [Group B] (f : A →* B) :
    f = 1 ∨ Function.Injective f := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact Or.inr ((MonoidHom.ker_eq_bot_iff f).mp h)
  · refine Or.inl (MonoidHom.ext fun x => ?_)
    have : x ∈ f.ker := by rw [h]; trivial
    exact MonoidHom.mem_ker.mp this

theorem eq_one_of_commute [Finite A] (hZ : Subgroup.center A = ⊥) {f g : A →* A}
    (hf : Function.Injective f) (h : ∀ a b, Commute (f a) (g b)) : g = 1 := by
  refine MonoidHom.ext fun b => ?_
  have hb : g b ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨a, rfl⟩ := Finite.surjective_of_injective hf c
    exact (h a b).eq
  rw [hZ] at hb
  exact Subgroup.mem_bot.mp hb

theorem commute_dichotomy [Finite A] [IsSimpleGroup A] (hZ : Subgroup.center A = ⊥)
    {u₁ u₂ v₁ v₂ : A →* A}
    (hu : ∀ a, u₁ a = 1 → u₂ a = 1 → a = 1) (hv : ∀ b, v₁ b = 1 → v₂ b = 1 → b = 1)
    (h₁ : ∀ a b, Commute (u₁ a) (v₁ b)) (h₂ : ∀ a b, Commute (u₂ a) (v₂ b)) :
    (u₂ = 1 ∧ v₁ = 1) ∨ (u₁ = 1 ∧ v₂ = 1) := by
  rcases hom_eq_one_or_injective u₁ with h1 | h1 <;>
    rcases hom_eq_one_or_injective u₂ with h2 | h2
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    exact ha (hu a (by simp [h1]) (by simp [h2]))
  · exact Or.inr ⟨h1, eq_one_of_commute hZ h2 h₂⟩
  · exact Or.inl ⟨h2, eq_one_of_commute hZ h1 h₁⟩
  · exfalso
    have e1 := eq_one_of_commute hZ h1 h₁
    have e2 := eq_one_of_commute hZ h2 h₂
    obtain ⟨b, hb⟩ := exists_ne (1 : A)
    exact hb (hv b (by simp [e1]) (by simp [e2]))

end Simple

section Swap

variable {A : Type*} [Group A]

variable (A) in
@[expose] def sw : MulAut (A × A) := MulEquiv.prodComm

@[simp] theorem sw_apply (x : A × A) : sw A x = x.swap := rfl

theorem sw_inv : (sw A)⁻¹ = sw A := by
  ext ⟨a, b⟩ <;> rfl

variable (A) in
open Classical in
@[expose] noncomputable def sect (x : Multiplicative (ZMod 2)) : MulAut (A × A) :=
  if x = 1 then 1 else sw A

theorem sect_one : sect A 1 = 1 := by simp [sect]

theorem sect_ofAdd_one : sect A (Multiplicative.ofAdd 1) = sw A := by
  have : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by decide
  simp [sect, this]

@[expose] def restrHom (α : MulAut (A × A)) : A →* A :=
  (MonoidHom.fst A A).comp ((α : A × A →* A × A).comp (MonoidHom.inl A A))

theorem restrHom_injective {α : MulAut (A × A)} (h : ∀ a, (α (a, 1)).2 = 1) :
    Function.Injective (restrHom α) := by
  intro a a' haa
  have : α (a, 1) = α (a', 1) := Prod.ext haa (by rw [h a, h a'])
  exact (Prod.ext_iff.mp (α.injective this)).1

variable [Finite A]

variable (A) in
@[expose] def presSubgroup : Subgroup (MulAut (A × A)) where
  carrier := {α | ∀ a, (α (a, 1)).2 = 1}
  one_mem' := fun _ => rfl
  mul_mem' := fun {α β} hα hβ a => by
    have h : β (a, 1) = ((β (a, 1)).1, 1) := Prod.ext rfl (hβ a)
    rw [MulAut.mul_apply, h]
    exact hα _
  inv_mem' := fun {α} hα a => by
    obtain ⟨a', ha'⟩ := Finite.surjective_of_injective (restrHom_injective hα) a
    have h1 : α (a', 1) = (a, 1) := Prod.ext ha' (hα a')
    have h2 : α⁻¹ (a, 1) = (a', 1) := by rw [← h1]; simp
    rw [h2]

theorem mem_presSubgroup {α : MulAut (A × A)} :
    α ∈ presSubgroup A ↔ ∀ a, (α (a, 1)).2 = 1 := Iff.rfl

theorem false_of_mem_of_mul_sw_mem [Nontrivial A] {α : MulAut (A × A)} (h : α ∈ presSubgroup A)
    (h' : α * sw A ∈ presSubgroup A) : False := by
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have key : ∀ x : A × A, (α x).2 = 1 := by
    rintro ⟨a, b⟩
    have hx : ((a, b) : A × A) = (a, 1) * (1, b) := by simp
    have hb : (α (1, b)).2 = 1 := by simpa using h' b
    rw [hx, map_mul, Prod.snd_mul, h a, hb, mul_one]
  obtain ⟨x, hx⟩ := α.surjective (1, a)
  exact ha (by simpa [hx] using key x)

theorem sw_not_mem [Nontrivial A] : sw A ∉ presSubgroup A := fun h =>
  false_of_mem_of_mul_sw_mem (one_mem _) (by rwa [one_mul])

theorem mem_or_mul_sw_mem [IsSimpleGroup A] (hZ : Subgroup.center A = ⊥)
    (α : MulAut (A × A)) : α ∈ presSubgroup A ∨ α * sw A ∈ presSubgroup A := by
  have key := commute_dichotomy hZ
    (u₁ := (MonoidHom.fst A A).comp ((α : A × A →* A × A).comp (MonoidHom.inl A A)))
    (u₂ := (MonoidHom.snd A A).comp ((α : A × A →* A × A).comp (MonoidHom.inl A A)))
    (v₁ := (MonoidHom.fst A A).comp ((α : A × A →* A × A).comp (MonoidHom.inr A A)))
    (v₂ := (MonoidHom.snd A A).comp ((α : A × A →* A × A).comp (MonoidHom.inr A A)))
    ?_ ?_ ?_ ?_
  · rcases key with ⟨h2, -⟩ | ⟨-, h2⟩
    · left
      intro a
      simpa using DFunLike.congr_fun h2 a
    · right
      intro a
      simpa using DFunLike.congr_fun h2 a
  · intro a h1 h2
    have : α (a, 1) = α 1 := by rw [map_one]; exact Prod.ext h1 h2
    simpa using α.injective this
  · intro b h1 h2
    have : α (1, b) = α 1 := by rw [map_one]; exact Prod.ext h1 h2
    simpa using α.injective this
  · intro a b
    have hc : Commute ((a, 1) : A × A) (1, b) := by
      show (a, 1) * (1, b) = (1, b) * (a, 1)
      simp
    exact (hc.map (α : A × A →* A × A)).map (MonoidHom.fst A A)
  · intro a b
    have hc : Commute ((a, 1) : A × A) (1, b) := by
      show (a, 1) * (1, b) = (1, b) * (a, 1)
      simp
    exact (hc.map (α : A × A →* A × A)).map (MonoidHom.snd A A)

theorem index_presSubgroup [IsSimpleGroup A] (hZ : Subgroup.center A = ⊥) :
    (presSubgroup A).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨sw A, fun b => ?_⟩
  rcases mem_or_mul_sw_mem hZ b with h | h
  · exact Or.inr ⟨h, fun h' => false_of_mem_of_mul_sw_mem h h'⟩
  · exact Or.inl ⟨h, fun h' => false_of_mem_of_mul_sw_mem h' h⟩

open Classical in
@[expose] noncomputable def phi [IsSimpleGroup A] (hZ : Subgroup.center A = ⊥) :
    MulAut (A × A) →* Multiplicative (ZMod 2) where
  toFun α := if α ∈ presSubgroup A then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' α β := by
    have h2 := Subgroup.mul_mem_iff_of_index_two (index_presSubgroup hZ) (a := α) (b := β)
    by_cases hα : α ∈ presSubgroup A <;> by_cases hβ : β ∈ presSubgroup A
    · simp [hα, hβ, h2]
    · simp [hα, hβ, h2]
    · simp [hα, hβ, h2]
    · simp [hα, hβ, h2]
      decide

theorem phi_eq_one_iff [IsSimpleGroup A] (hZ : Subgroup.center A = ⊥) {α : MulAut (A × A)} :
    phi hZ α = 1 ↔ α ∈ presSubgroup A := by
  by_cases h : α ∈ presSubgroup A
  · simp [phi, h]
  · have : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by decide
    simp [phi, h, this]

theorem phi_sect [IsSimpleGroup A] (hZ : Subgroup.center A = ⊥) (x : Multiplicative (ZMod 2)) :
    phi hZ (sect A x) = x := by
  have hx : x = 1 ∨ x = Multiplicative.ofAdd 1 := by revert x; decide
  rcases hx with rfl | rfl
  · rw [sect_one, map_one]
  · rw [sect_ofAdd_one]
    simp [phi, sw_not_mem]

end Swap

end SAFyHAut

end CFSG.EvenSporadicStandard.TwoHS
