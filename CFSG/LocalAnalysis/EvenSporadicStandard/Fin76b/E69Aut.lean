module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableSound
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSporadicStandard.Fin76b.E69

open AutETable

theorem mul_self_mem_of_index_le_two {Γ : Type*} [Group Γ] [Finite Γ] {A : Subgroup Γ}
    (hA : A.index ≤ 2) (a : Γ) : a * a ∈ A := by
  have h0 : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain h | h : A.index = 1 ∨ A.index = 2 := by omega
  · rw [Subgroup.index_eq_one.1 h]
    exact Subgroup.mem_top _
  · exact Subgroup.mul_self_mem_of_index_two h a

theorem isAutArr_spec {m : ℕ → ℕ → ℕ} {A : Array ℕ} (h : isAutArr m A = true) :
    (∀ a < 32, ix A a < 32) ∧ (∀ a < 32, ∀ b < 32, ix A (m a b) = m (ix A a) (ix A b)) ∧
      ∀ a < 32, ∀ b < 32, ix A a = ix A b → a = b := by
  simp only [isAutArr, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  refine ⟨fun a ha => (h a ha).1, fun a ha b hb => ((h a ha).2 b hb).1, fun a ha b hb hab => ?_⟩
  rcases ((h a ha).2 b hb).2 with h' | h'
  · exact absurd hab h'
  · exact h'

section Realizes

variable {H : Type*} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H}

theorem finite_of_realizes (R : Realizes H 32 M elt) : Finite H :=
  Finite.of_surjective (fun i : Fin 32 => elt i) fun h => by
    obtain ⟨a, ha, rfl⟩ := R.surj h
    exact ⟨⟨a, ha⟩, rfl⟩

theorem exists_aut_of_isAutArr (R : Realizes H 32 M elt) {A : Array ℕ}
    (h : isAutArr (mt M) A = true) : ∃ φ : MulAut H, ∀ k < 32, sg R φ k = ix A k := by
  classical
  obtain ⟨hlt, hmul, hinj⟩ := isAutArr_spec h
  have := finite_of_realizes R
  choose idx hidx helt using R.surj
  have idx_elt : ∀ k < 32, idx (elt k) = k := fun k hk => R.inj _ _ (hidx _) hk (helt _)
  have idx_mul : ∀ x y : H, idx (x * y) = mt M (idx x) (idx y) := fun x y =>
    R.inj _ _ (hidx _) (R.lt _ _ (hidx x) (hidx y))
      (by rw [helt, R.mul _ _ (hidx x) (hidx y), helt, helt])
  let f : H →* H := MonoidHom.mk' (fun x => elt (ix A (idx x))) fun x y => by
    show elt (ix A (idx (x * y))) = elt (ix A (idx x)) * elt (ix A (idx y))
    rw [idx_mul, hmul _ (hidx x) _ (hidx y), R.mul _ _ (hlt _ (hidx x)) (hlt _ (hidx y))]
  have hf : ∀ x, f x = elt (ix A (idx x)) := fun x => rfl
  have hfinj : Function.Injective f := by
    intro x y hxy
    rw [hf, hf] at hxy
    have h1 := R.inj _ _ (hlt _ (hidx x)) (hlt _ (hidx y)) hxy
    rw [← helt x, ← helt y, hinj _ (hidx x) _ (hidx y) h1]
  refine ⟨MulEquiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj), fun k hk => ?_⟩
  apply R.inj _ _ (sg_lt R _ k) (hlt k hk)
  rw [sg_elt R _ k, MulEquiv.ofBijective_apply, hf, idx_elt k hk]

end Realizes

end CFSG.EvenSporadicStandard.Fin76b.E69
