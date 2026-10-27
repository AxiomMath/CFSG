module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Equiv

section Generic

variable {A : Type*} [Group A] [Finite A] [IsSimpleGroup A]

theorem s3a_triv_or_surj (f : A →* A) : (∀ a, f a = 1) ∨ Function.Surjective f := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · right
    have : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 h
    exact Finite.injective_iff_surjective.1 this
  · left
    intro a
    have : a ∈ f.ker := h ▸ Subgroup.mem_top a
    exact this

omit [Finite A] [IsSimpleGroup A] in
theorem s3a_exists_ne_one (hnc : ∃ a b : A, a * b ≠ b * a) : ∃ x : A, x ≠ 1 := by
  obtain ⟨a, b, hab⟩ := hnc
  by_cases ha : a = 1
  · exact ⟨b, fun hb => hab (by rw [ha, hb])⟩
  · exact ⟨a, ha⟩

theorem s3a_aut_prod (hnc : ∃ a b : A, a * b ≠ b * a) (α : A × A ≃* A × A) :
    ((∀ a, (α (a, 1)).2 = 1) ∧ ∀ b, (α (1, b)).1 = 1) ∨
    ((∀ a, (α (a, 1)).1 = 1) ∧ ∀ b, (α (1, b)).2 = 1) := by
  let f : A →* A := (MonoidHom.fst A A).comp (α.toMonoidHom.comp (MonoidHom.inl A A))
  let g : A →* A := (MonoidHom.snd A A).comp (α.toMonoidHom.comp (MonoidHom.inl A A))
  let h : A →* A := (MonoidHom.fst A A).comp (α.toMonoidHom.comp (MonoidHom.inr A A))
  let k : A →* A := (MonoidHom.snd A A).comp (α.toMonoidHom.comp (MonoidHom.inr A A))
  have hf : ∀ a, (α (a, 1)).1 = f a := fun a => rfl
  have hg : ∀ a, (α (a, 1)).2 = g a := fun a => rfl
  have hh : ∀ b, (α (1, b)).1 = h b := fun b => rfl
  have hk : ∀ b, (α (1, b)).2 = k b := fun b => rfl
  have hcomm : ∀ a b, f a * h b = h b * f a ∧ g a * k b = k b * g a := by
    intro a b
    have : α (a, 1) * α (1, b) = α (1, b) * α (a, 1) := by
      rw [← map_mul, ← map_mul]
      congr 1
      simp
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hcen : ∀ z : A, (∀ s, z * s = s * z) → z = 1 := fun z hz => eq_one_of_forall_commute hnc hz
  obtain ⟨x0, hx0⟩ := s3a_exists_ne_one hnc
  have hker : ∀ a : A, f a = 1 → g a = 1 → a = 1 := by
    intro a h1 h2
    have : α (a, 1) = α 1 := by
      rw [map_one]
      exact Prod.ext h1 h2
    have := α.injective this
    exact (Prod.ext_iff.1 this).1
  have hker' : ∀ b : A, h b = 1 → k b = 1 → b = 1 := by
    intro b h1 h2
    have : α (1, b) = α 1 := by
      rw [map_one]
      exact Prod.ext h1 h2
    have := α.injective this
    exact (Prod.ext_iff.1 this).2
  rcases s3a_triv_or_surj f with hf0 | hfs
  · right
    have hgs : Function.Surjective g := by
      rcases s3a_triv_or_surj g with hg0 | hgs
      · exact absurd (hker x0 (hf0 x0) (hg0 x0)) hx0
      · exact hgs
    have hk0 : ∀ b, k b = 1 := by
      intro b
      apply hcen
      intro s
      obtain ⟨a, rfl⟩ := hgs s
      exact (hcomm a b).2.symm
    exact ⟨fun a => by rw [hf]; exact hf0 a, fun b => by rw [hk]; exact hk0 b⟩
  · left
    have hh0 : ∀ b, h b = 1 := by
      intro b
      apply hcen
      intro s
      obtain ⟨a, rfl⟩ := hfs s
      exact (hcomm a b).1.symm
    have hks : Function.Surjective k := by
      rcases s3a_triv_or_surj k with hk0 | hks
      · exact absurd (hker' x0 (hh0 x0) (hk0 x0)) hx0
      · exact hks
    have hg0 : ∀ a, g a = 1 := by
      intro a
      apply hcen
      intro s
      obtain ⟨b, rfl⟩ := hks s
      exact (hcomm a b).2
    exact ⟨fun a => by rw [hg]; exact hg0 a, fun b => by rw [hh]; exact hh0 b⟩

theorem s3a_pure_swap (τ : A × A ≃* A × A)
    (h₁ : ∀ a, (τ (a, 1)).2 = 1) (h₂ : ∀ b, (τ (1, b)).1 = 1)
    (g : A →* A × A) (hfix : ∀ a, τ (g a) = g a) :
    (∀ x, τ x = x) ∨ (∀ a, (g a).1 = 1) ∨ (∀ a, (g a).2 = 1) := by
  have hτ : ∀ a b : A, τ (a, b) = ((τ (a, 1)).1, (τ (1, b)).2) := by
    intro a b
    have e : ((a, b) : A × A) = (a, 1) * (1, b) := by simp
    rw [e, map_mul]
    have e1 : τ (a, 1) = ((τ (a, 1)).1, 1) := Prod.ext rfl (h₁ a)
    have e2 : τ (1, b) = (1, (τ (1, b)).2) := Prod.ext (h₂ b) rfl
    rw [e1, e2]
    simp
  let f₁ : A →* A := (MonoidHom.fst A A).comp g
  let f₂ : A →* A := (MonoidHom.snd A A).comp g
  rcases s3a_triv_or_surj f₁ with h1 | h1
  · exact Or.inr (Or.inl h1)
  rcases s3a_triv_or_surj f₂ with h2 | h2
  · exact Or.inr (Or.inr h2)
  left
  have k1 : ∀ a, (τ (a, 1)).1 = a := by
    intro a
    obtain ⟨a₀, ha₀⟩ := h1 a
    have := hfix a₀
    have e : g a₀ = ((g a₀).1, (g a₀).2) := rfl
    rw [e, hτ] at this
    have := congrArg Prod.fst this
    simp only at this
    have e1 : (g a₀).1 = a := ha₀
    rw [e1] at this
    exact this
  have k2 : ∀ b, (τ (1, b)).2 = b := by
    intro b
    obtain ⟨a₀, ha₀⟩ := h2 b
    have := hfix a₀
    have e : g a₀ = ((g a₀).1, (g a₀).2) := rfl
    rw [e, hτ] at this
    have := congrArg Prod.snd this
    simp only at this
    have e1 : (g a₀).2 = b := ha₀
    rw [e1] at this
    exact this
  intro x
  obtain ⟨a, b⟩ := x
  rw [hτ, k1, k2]

end Generic

section A5Sec

local notation "A5" => alternatingGroup (Fin 5)

theorem s3a_A5_noncomm : ∃ a b : ↥A5, a * b ≠ b * a := by
  refine ⟨⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
    ⟨swap 0 1 * swap 1 3, Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  revert this
  decide +kernel

theorem s3a_A5_comm_exists : ∀ a : ↥A5, a ≠ 1 → ∃ x : ↥A5, x * a = a * x ∧ x ≠ 1 ∧ x ≠ a := by
  decide +kernel

end A5Sec

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
