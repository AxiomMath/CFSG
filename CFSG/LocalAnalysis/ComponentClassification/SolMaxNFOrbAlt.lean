module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.ComponentClassification.SolMax.NFOrb

open Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem swap_mul_swap_mem_alternatingGroup {x y u v : ι} (hxy : x ≠ y) (huv : u ≠ v) :
    swap x y * swap u v ∈ alternatingGroup ι := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hxy, Perm.sign_swap huv]
  rfl

theorem exists_two_notMem (h4 : 4 ≤ Fintype.card ι) (a b : ι) :
    ∃ x y : ι, x ≠ y ∧ x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b := by
  classical
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({a, b} : Finset ι))
    (t := Finset.univ)
    (by rw [Finset.card_univ]; exact lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({a, b, x} : Finset ι))
    (t := Finset.univ)
    (by rw [Finset.card_univ]; exact lt_of_le_of_lt Finset.card_le_three (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
  exact ⟨x, y, Ne.symm hy.2.2, hx.1, hx.2, hy.1, hy.2.1⟩

theorem exists_mem_alternatingGroup_apply_eq (h4 : 4 ≤ Fintype.card ι) (a a' : ι) :
    ∃ τ ∈ alternatingGroup ι, τ a = a' := by
  by_cases h : a = a'
  · exact ⟨1, one_mem _, by rw [h, Perm.one_apply]⟩
  obtain ⟨x, y, hxy, hxa, -, hya, -⟩ := exists_two_notMem h4 a a
  have hxa' := hxa
  refine ⟨swap a a' * swap x y, swap_mul_swap_mem_alternatingGroup h hxy, ?_⟩
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hxa') (Ne.symm hya), swap_apply_left]

theorem exists_mem_alternatingGroup_apply_eq_apply_eq (h4 : 4 ≤ Fintype.card ι) {a b a' b' : ι}
    (hab : a ≠ b) (hab' : a' ≠ b') : ∃ τ ∈ alternatingGroup ι, τ a = a' ∧ τ b = b' := by
  set b₁ := swap a a' b with hb₁
  set τ₀ := swap b₁ b' * swap a a' with hτ₀
  have hb₁a' : a' ≠ b₁ := by
    intro h
    apply hab
    have h1 : swap a a' b = swap a a' a := by rw [← hb₁, ← h, swap_apply_left]
    exact (swap a a').injective h1 |>.symm
  have hτa : τ₀ a = a' := by
    rw [hτ₀, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hb₁a' hab']
  have hτb : τ₀ b = b' := by
    rw [hτ₀, Perm.mul_apply, ← hb₁, swap_apply_left]
  rcases Int.units_eq_one_or (Perm.sign τ₀) with hs | hs
  · exact ⟨τ₀, hs, hτa, hτb⟩
  obtain ⟨x, y, hxy, hxa, hxb, hya, hyb⟩ := exists_two_notMem h4 a' b'
  refine ⟨swap x y * τ₀, ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hxy, hs]
    rfl
  · rw [Perm.mul_apply, hτa, swap_apply_of_ne_of_ne (Ne.symm hxa) (Ne.symm hya)]
  · rw [Perm.mul_apply, hτb, swap_apply_of_ne_of_ne (Ne.symm hxb) (Ne.symm hyb)]

theorem smul_eq_of_card_orbit_lt (h5 : 5 ≤ Fintype.card ι) {Y : Type*}
    [MulAction (alternatingGroup ι) Y] (y : Y) [Finite (MulAction.orbit (alternatingGroup ι) y)]
    (hy : Nat.card (MulAction.orbit (alternatingGroup ι) y) < Fintype.card ι)
    (g : alternatingGroup ι) : g • y = y := by
  classical
  have hcard : 5 ≤ Nat.card ι := by rwa [Nat.card_eq_fintype_card]
  have hsimple : IsSimpleGroup (alternatingGroup ι) := alternatingGroup.isSimpleGroup hcard
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  set κ := MulAction.toPermHom (alternatingGroup ι) (MulAction.orbit (alternatingGroup ι) y)
    with hκ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal κ.ker with h | h
  · exfalso
    have hinj : Function.Injective κ := (MonoidHom.ker_eq_bot_iff κ).mp h
    have h1 := Nat.card_le_card_of_injective κ hinj
    rw [Nat.card_perm] at h1
    have h2 := two_mul_nat_card_alternatingGroup (α := ι)
    rw [Nat.card_perm] at h2
    obtain ⟨m, hm⟩ : ∃ m, Nat.card ι = m + 1 := ⟨Nat.card ι - 1, by omega⟩
    have h3 : (Nat.card (MulAction.orbit (alternatingGroup ι) y)).factorial ≤ m.factorial :=
      Nat.factorial_le (by rw [← Nat.card_eq_fintype_card] at hy; omega)
    rw [hm, Nat.factorial_succ] at h2
    have h4 : 0 < m.factorial := Nat.factorial_pos m
    have h5' : 2 * m.factorial < (m + 1) * m.factorial :=
      Nat.mul_lt_mul_of_pos_right (by omega) h4
    omega
  · have hg : g ∈ κ.ker := by rw [h]; exact Subgroup.mem_top g
    have h1 := congrArg (fun f : Perm (MulAction.orbit (alternatingGroup ι) y) =>
      ((f ⟨y, MulAction.mem_orbit_self y⟩ : MulAction.orbit (alternatingGroup ι) y) : Y))
      (MonoidHom.mem_ker.mp hg)
    exact h1

end CFSG.ComponentClassification.SolMax.NFOrb
