module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrbAlt
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ComponentClassification.SolMax

open Equiv

namespace NFOrb

variable {ι Ω : Type*} {t : ι → ι → Perm Ω}

section Family

variable (ht : ∀ c d e, t c d * t d e = t c e) (hs : ∀ c d, t c d = t d c)
include ht

theorem pair_self (c : ι) : t c c = 1 :=
  mul_left_cancel (a := t c c) (by rw [ht c c c, mul_one])

theorem pair_fix_trans {c d e : ι} {ω : Ω} (h1 : t c d ω = ω) (h2 : t d e ω = ω) :
    t c e ω = ω := by
  rw [← ht c d e, Perm.mul_apply, h2, h1]

include hs

theorem pair_mul_self (c d : ι) : t c d * t c d = 1 := by
  calc t c d * t c d = t c d * t d c := by rw [← hs c d]
    _ = 1 := by rw [ht c d c, pair_self ht c]

theorem pair_apply_apply (c d : ι) (ω : Ω) : t c d (t c d ω) = ω := by
  rw [← Perm.mul_apply, pair_mul_self ht hs, Perm.one_apply]

theorem pair_eq_mul (c₀ c d : ι) : t c d = t c₀ c * t c₀ d := by
  rw [← ht c c₀ d, hs c c₀]

theorem pair_commute (a b c d : ι) : Commute (t a b) (t c d) := by
  have hr : ∀ x y, Commute (t a x) (t a y) := fun x y => by
    change t a x * t a y = t a y * t a x
    rw [← pair_eq_mul ht hs a x y, ← pair_eq_mul ht hs a y x, hs x y]
  rw [pair_eq_mul ht hs a a b, pair_eq_mul ht hs a c d]
  exact ((hr a c).mul_right (hr a d)).mul_left ((hr b c).mul_right (hr b d))

theorem pair_fix_apply (a b c d : ι) (ω : Ω) : t c d (t a b ω) = t a b ω ↔ t c d ω = ω := by
  rw [← Perm.mul_apply, (pair_commute ht hs c d a b).eq, Perm.mul_apply]
  exact (t a b).injective.eq_iff

theorem pair_apply_eq_iff (a b c d : ι) (ω : Ω) : t a b ω = t c d ω ↔ t c d (t a b ω) = ω := by
  constructor
  · intro h
    rw [h, pair_apply_apply ht hs]
  · intro h
    calc t a b ω = t c d (t c d (t a b ω)) := (pair_apply_apply ht hs c d _).symm
      _ = t c d ω := by rw [h]

theorem pair_apply_eq_iff_fix (a b c : ι) (ω : Ω) : t a b ω = t a c ω ↔ t b c ω = ω := by
  rw [pair_apply_eq_iff ht hs, ← Perm.mul_apply, hs a c, ht c a b, hs c b]

end Family

theorem perm_apply_inv {α : Type*} (f : Perm α) (x : α) : f (f⁻¹ x) = x :=
  Equiv.apply_symm_apply f x

theorem perm_inv_apply {α : Type*} (f : Perm α) (x : α) : f⁻¹ (f x) = x :=
  Equiv.symm_apply_apply f x

theorem pair_fix_conj {π : Perm Ω} {τ : Perm ι} (hπ : ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d))
    (c d : ι) (ω : Ω) : t (τ c) (τ d) (π ω) = π ω ↔ t c d ω = ω := by
  rw [← hπ c d, Perm.mul_apply, Perm.mul_apply, perm_inv_apply]
  exact π.injective.eq_iff

@[expose] def pairClosure (t : ι → ι → Perm Ω) : Subgroup (Perm Ω) :=
  Subgroup.closure (Set.range fun p : ι × ι => t p.1 p.2)

theorem mem_pairClosure (c d : ι) : t c d ∈ pairClosure t :=
  Subgroup.subset_closure ⟨(c, d), rfl⟩

section Closure

variable (ht : ∀ c d e, t c d * t d e = t c e) (hs : ∀ c d, t c d = t d c)
include ht hs

theorem commute_of_mem_pairClosure {g : Perm Ω} (hg : g ∈ pairClosure t) (c d : ι) :
    Commute g (t c d) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact pair_commute ht hs a b c d
  | one => exact Commute.one_left _
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

theorem commute_of_mem_pairClosure₂ {g h : Perm Ω} (hg : g ∈ pairClosure t)
    (hh : h ∈ pairClosure t) : Commute g h := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact commute_of_mem_pairClosure ht hs hg a b
  | one => exact Commute.one_right _
  | mul x y _ _ hx hy => exact hx.mul_right hy
  | inv x _ hx => exact hx.inv_right

theorem mul_self_of_mem_pairClosure {g : Perm Ω} (hg : g ∈ pairClosure t) : g * g = 1 := by
  have hg' := hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact pair_mul_self ht hs a b
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * x * (y * y) := by
          rw [mul_assoc, ← mul_assoc y x y, ← (commute_of_mem_pairClosure₂ ht hs hx hy).eq]
          group
      _ = 1 := by rw [ihx hx, ihy hy, mul_one]
  | inv x hx ihx =>
    rw [← mul_inv_rev, ihx hx, inv_one]

theorem isPGroup_pairClosure : IsPGroup 2 (pairClosure t) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
  exact mul_self_of_mem_pairClosure ht hs g.2

end Closure

theorem card_mul_le_of_fibre [Fintype Ω] {Y : Type*} [DecidableEq Y] (f : Ω → Y) (S : Finset Y)
    {k : ℕ} (hk : ∀ y ∈ S, k ≤ (Finset.univ.filter fun ω => f ω = y).card) :
    S.card * k ≤ Fintype.card Ω := by
  classical
  set s := Finset.univ.filter fun ω => f ω ∈ S with hsdef
  have h1 : s.card = ∑ y ∈ S, (s.filter fun ω => f ω = y).card :=
    Finset.card_eq_sum_card_fiberwise (fun ω hω => (Finset.mem_filter.mp hω).2)
  have h2 : ∀ y ∈ S, (s.filter fun ω => f ω = y) = Finset.univ.filter fun ω => f ω = y := by
    intro y hy
    ext ω
    simp only [hsdef, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hy, h⟩
  have h3 : S.card * k ≤ ∑ y ∈ S, (s.filter fun ω => f ω = y).card := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun y hy => by rw [h2 y hy]; exact hk y hy
  calc S.card * k ≤ s.card := by rw [h1]; exact h3
    _ ≤ Fintype.card Ω := Finset.card_le_univ s

end NFOrb

end CFSG.ComponentClassification.SolMax
