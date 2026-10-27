module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

private def unitVec {m : ℕ} (a : Fin m) : G6.PermMod m := Multiplicative.ofAdd (Pi.single a 1)

private theorem toAdd_unitVec {m : ℕ} (a i : Fin m) :
    Multiplicative.toAdd (unitVec a) i = (Pi.single a 1 : Fin m → ZMod 2) i := rfl

private theorem permAct_unitVec {m : ℕ} (σ : Equiv.Perm (Fin m)) (a : Fin m) :
    G6.permAct m σ (unitVec a) = unitVec (σ a) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [G6.permAct_apply, toAdd_unitVec, Pi.single_apply, Equiv.symm_apply_eq]

private theorem unitVec_mul_self {m : ℕ} (a : Fin m) : unitVec a * unitVec a = 1 := by
  apply Multiplicative.toAdd.injective
  funext j
  simp only [toAdd_mul, Pi.add_apply, toAdd_unitVec, toAdd_one, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

private theorem exists_ne_coord {m : ℕ} {x : G6.PermMod m} (hx0 : x ≠ 1)
    (hx1 : x ≠ G6.allOnes m) (i0 : Fin m) :
    ∃ i j, Multiplicative.toAdd x i ≠ Multiplicative.toAdd x j := by
  by_contra h
  replace h : ∀ i j, Multiplicative.toAdd x i = Multiplicative.toAdd x j :=
    fun i j => by_contra fun hij => h ⟨i, j, hij⟩
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd x i0) with h0 | h1
  · refine hx0 (Multiplicative.toAdd.injective ?_)
    funext i
    rw [h i i0, h0]
    simp
  · refine hx1 (Multiplicative.toAdd.injective ?_)
    funext i
    rw [h i i0, h1]
    simp [G6.allOnes]

private theorem exists_three_cycle {m : ℕ} {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : ∃ τ ∈ alternatingGroup (Fin m),
      τ i = j ∧ τ j = k ∧ τ k = i ∧ ∀ a, a ≠ i → a ≠ j → a ≠ k → τ a = a := by
  refine ⟨Equiv.swap i j * Equiv.swap j k, ?_, ?_, ?_, ?_, fun a hai haj hak => ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hij, hjk]
  · simp [Equiv.swap_apply_of_ne_of_ne hij hik]
  · simp [Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm]
  · simp
  · simp [Equiv.swap_apply_of_ne_of_ne haj hak, Equiv.swap_apply_of_ne_of_ne hai haj]

private theorem exists_pair_mem {m : ℕ} (hm : 3 ≤ m) {N : Subgroup (G6.PermMod m)}
    (hN : ∀ σ ∈ alternatingGroup (Fin m), ∀ x ∈ N, G6.permAct m σ x ∈ N)
    {x : G6.PermMod m} (hx : x ∈ N) {i j : Fin m}
    (hij : Multiplicative.toAdd x i ≠ Multiplicative.toAdd x j) :
    ∃ a b : Fin m, a ≠ b ∧ unitVec a * unitVec b ∈ N := by
  have hne : i ≠ j := fun h => hij (by rw [h])
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
    have hlt : ({i, j} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt Finset.card_le_two (by omega)
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact ⟨k, hk.1, hk.2⟩
  obtain ⟨τ, hτ, hτi, hτj, hτk, hτa⟩ := exists_three_cycle hne hki.symm hkj.symm
  have hy : G6.permAct m τ⁻¹ x * x⁻¹ ∈ N := N.mul_mem (hN _ (inv_mem hτ) x hx) (N.inv_mem hx)
  have hyc : ∀ a, Multiplicative.toAdd (G6.permAct m τ⁻¹ x * x⁻¹) a =
      Multiplicative.toAdd x (τ a) + Multiplicative.toAdd x a := by
    intro a
    simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply, inv_inv]
    exact congrArg _ (ZMod.neg_eq_self_mod_two _)
  obtain ⟨h1, h2 | h2⟩ := (by decide : ∀ p q r : ZMod 2, p ≠ q →
      q + p = 1 ∧ ((r + q = 1 ∧ p + r = 0) ∨ (r + q = 0 ∧ p + r = 1)))
    (Multiplicative.toAdd x i) (Multiplicative.toAdd x j) (Multiplicative.toAdd x k) hij
  · refine ⟨i, j, hne, ?_⟩
    convert hy using 1
    apply Multiplicative.toAdd.injective
    funext a
    rw [toAdd_mul, Pi.add_apply, toAdd_unitVec, toAdd_unitVec, hyc]
    by_cases hai : a = i
    · subst hai
      simp [hne, hτi, h1]
    by_cases haj : a = j
    · subst haj
      simp [hai, hτj, h2.1]
    by_cases hak : a = k
    · subst hak
      simp [hai, haj, hτk, h2.2]
    · simp [hai, haj, hτa a hai haj hak]
      exact (CharTwo.add_self_eq_zero _).symm
  · refine ⟨i, k, hki.symm, ?_⟩
    convert hy using 1
    apply Multiplicative.toAdd.injective
    funext a
    rw [toAdd_mul, Pi.add_apply, toAdd_unitVec, toAdd_unitVec, hyc]
    by_cases hai : a = i
    · subst hai
      simp [hki, hτi, h1]
    by_cases haj : a = j
    · subst haj
      simp [hai, hkj, hτj, h2.1]
    by_cases hak : a = k
    · subst hak
      simp [hai, hτk, h2.2]
    · simp [hai, hak, hτa a hai haj hak]
      exact (CharTwo.add_self_eq_zero _).symm

private theorem exists_alt_two {m : ℕ} (hm : 4 ≤ m) {a b c d : Fin m} (hab : a ≠ b)
    (hcd : c ≠ d) : ∃ τ ∈ alternatingGroup (Fin m), τ a = c ∧ τ b = d := by
  have h := alternatingGroup.isMultiplyPretransitive (Fin m)
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin m)) (Fin m) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := m - 2) (by omega) (by simp)
  obtain ⟨g, hg1, hg2⟩ := (MulAction.is_two_pretransitive_iff.mp h2) hab hcd
  exact ⟨g, g.2, hg1, hg2⟩

private theorem unitVec_mul_mem {m : ℕ} (hm : 4 ≤ m) {N : Subgroup (G6.PermMod m)}
    (hN : ∀ σ ∈ alternatingGroup (Fin m), ∀ x ∈ N, G6.permAct m σ x ∈ N)
    {a b : Fin m} (hab : a ≠ b) (hmem : unitVec a * unitVec b ∈ N) {c d : Fin m} (hcd : c ≠ d) :
    unitVec c * unitVec d ∈ N := by
  obtain ⟨τ, hτ, rfl, rfl⟩ := exists_alt_two hm hab hcd
  have := hN τ hτ _ hmem
  rwa [map_mul, permAct_unitVec, permAct_unitVec] at this

private theorem mem_of_unitVec_mul_mem {m : ℕ} {N : Subgroup (G6.PermMod m)} (i0 : Fin m)
    (h : ∀ c : Fin m, c ≠ i0 → unitVec c * unitVec i0 ∈ N)
    {u : G6.PermMod m} (hu : u ∈ G6.coreMod m) : u ∈ N := by
  have hprod : u = ∏ i : Fin m, (unitVec i * unitVec i0) ^ (Multiplicative.toAdd u i).val := by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_prod, toAdd_pow, Finset.sum_apply, Pi.smul_apply, toAdd_mul, Pi.add_apply]
    simp only [toAdd_unitVec, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_add, Finset.sum_add_distrib]
    have h1 : ∑ i, Multiplicative.toAdd u i * (Pi.single i 1 : Fin m → ZMod 2) j =
        Multiplicative.toAdd u j := by
      simp [Pi.single_apply]
    have h2 : ∑ i, Multiplicative.toAdd u i * (Pi.single i0 1 : Fin m → ZMod 2) j = 0 := by
      rw [← Finset.sum_mul, G6.mem_coreMod.mp hu, zero_mul]
    rw [h1, h2, add_zero]
  rw [hprod]
  refine N.prod_mem fun i _ => N.pow_mem ?_ _
  by_cases hi : i = i0
  · subst hi
    rw [unitVec_mul_self]
    exact N.one_mem
  · exact h i hi

theorem coreMod_le_of_invariant {m : ℕ} (hm : 4 ≤ m) {N : Subgroup (G6.PermMod m)}
    (hN : ∀ σ ∈ alternatingGroup (Fin m), ∀ x ∈ N, G6.permAct m σ x ∈ N)
    {x : G6.PermMod m} (hx : x ∈ N) (hx0 : x ≠ 1) (hx1 : x ≠ G6.allOnes m) :
    G6.coreMod m ≤ N := by
  obtain ⟨i0⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, j, hij⟩ := exists_ne_coord hx0 hx1 i0
  obtain ⟨a, b, hab, hmem⟩ := exists_pair_mem (by omega) hN hx hij
  exact fun u hu => mem_of_unitVec_mul_mem i0 (fun c hc => unitVec_mul_mem hm hN hab hmem hc) hu

theorem coreMod_irreducible {m : ℕ} (hm : Odd m) (hm5 : 5 ≤ m) {N : Subgroup (G6.PermMod m)}
    (hN : ∀ σ ∈ alternatingGroup (Fin m), ∀ x ∈ N, G6.permAct m σ x ∈ N)
    (hle : N ≤ G6.coreMod m) : N = ⊥ ∨ N = G6.coreMod m := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  refine Or.inr (le_antisymm hle ?_)
  obtain ⟨⟨x, hxN⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hall : G6.allOnes m ∉ G6.coreMod m := by
    rw [G6.mem_coreMod]
    simp only [G6.allOnes, toAdd_ofAdd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Odd.natCast_zmod_two hm]
    decide
  exact coreMod_le_of_invariant (by omega) hN hxN (fun h => hx1 (Subtype.ext h))
    (fun h => hall (h ▸ hle hxN))

theorem coreMod_subgroup_eq_bot_or_top {m : ℕ} (hm : Odd m) (hm5 : 5 ≤ m)
    (N : Subgroup ↥(G6.coreMod m))
    (hN : ∀ σ ∈ alternatingGroup (Fin m), ∀ x ∈ N, G6.coreAct m σ x ∈ N) : N = ⊥ ∨ N = ⊤ := by
  have hinj : Function.Injective (G6.coreMod m).subtype := Subtype.val_injective
  have hN' : ∀ σ ∈ alternatingGroup (Fin m), ∀ y ∈ N.map (G6.coreMod m).subtype,
      G6.permAct m σ y ∈ N.map (G6.coreMod m).subtype := by
    rintro σ hσ _ ⟨z, hz, rfl⟩
    exact ⟨G6.coreAct m σ z, hN σ hσ z hz, rfl⟩
  rcases coreMod_irreducible hm hm5 hN' (Subgroup.map_subtype_le N) with h | h
  · exact Or.inl (Subgroup.map_injective hinj (h.trans (Subgroup.map_bot _).symm))
  · refine Or.inr (Subgroup.map_injective hinj (h.trans ?_))
    rw [Subgroup.map_top, Subgroup.range_subtype]

end CFSG.CGT.PushingUpLit.CGT6
