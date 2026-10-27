module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Block.PermAux
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin

namespace B69K

open Equiv Equiv.Perm MulAction CFSG.QuasithinUnique.L246C127.C127Block

theorem exists_even_mem_young_move {n : ℕ} (O : Finset (Fin n)) (h2 : 2 ≤ O.card)
    (hO : O.card + 2 ≤ n) (p : Fin n) :
    ∃ g ∈ alternatingGroup (Fin n), g ∈ young O ∧ g p ≠ p := by
  by_cases hp : p ∈ O
  ·
    obtain ⟨x, hx, hxp⟩ := bt_exists_ne_mem O h2 p
    obtain ⟨c, hc, -⟩ := bt_exists_notMem_ne O hO p
    obtain ⟨d, hd, hdc⟩ := bt_exists_notMem_ne O hO c
    have hpc : p ≠ c := by
      rintro rfl
      exact hc hp
    have hpd : p ≠ d := by
      rintro rfl
      exact hd hp
    refine ⟨Equiv.swap p x * Equiv.swap c d, ?_, ?_, ?_⟩
    · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hxp.symm,
        Perm.sign_swap hdc.symm]
      all_goals first | rfl | decide | norm_num | simp
    · exact mul_mem (bt_swap_mem_young (iff_of_true hp hx))
        (bt_swap_mem_young (iff_of_false hc hd))
    · rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpc hpd, Equiv.swap_apply_left]
      exact hxp
  ·
    obtain ⟨y, hy, hyp⟩ := bt_exists_notMem_ne O hO p
    obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < O.card)
    have hpa : p ≠ a := by
      rintro rfl
      exact hp ha
    have hpa' : p ≠ a' := by
      rintro rfl
      exact hp ha'
    refine ⟨Equiv.swap p y * Equiv.swap a a', ?_, ?_, ?_⟩
    · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hyp.symm,
        Perm.sign_swap haa']
      all_goals first | rfl | decide | norm_num | simp
    · exact mul_mem (bt_swap_mem_young (iff_of_false hp hy))
        (bt_swap_mem_young (iff_of_true ha ha'))
    · rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpa hpa', Equiv.swap_apply_left]
      exact hyp

theorem alt_pair_odd {m : ℕ} (hm : 5 ≤ m) (hodd : Odd m) (hnp : ¬ ∃ j : ℕ, m = 2 ^ j + 1)
    (T' : Subgroup (Perm (Fin m))) (hT' : IsPGroup 2 T') :
    ∃ Q₀ Q₁ : Subgroup (alternatingGroup (Fin m)), Q₀ ≠ ⊤ ∧ Q₁ ≠ ⊤ ∧ Q₀ ⊔ Q₁ = ⊤ ∧
      (∀ Q ∈ ({Q₀, Q₁} : Set (Subgroup (alternatingGroup (Fin m)))),
        (∀ τ ∈ T', ∀ g ∈ Q, ∀ h : τ * (g : Perm (Fin m)) * τ⁻¹ ∈ alternatingGroup (Fin m),
          (⟨τ * (g : Perm (Fin m)) * τ⁻¹, h⟩ : alternatingGroup (Fin m)) ∈ Q) ∧
        (∀ u : alternatingGroup (Fin m), (u : Perm (Fin m)) ∈ T' → u ∈ Q)) := by
  have hcard : Nat.card (Fin m) = m := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨p, hp⟩ : ∃ p : Fin m, ∀ s ∈ T', s p = p := by
    by_contra hcon
    push Not at hcon
    have hempty : MulAction.fixedPoints T' (Fin m) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨s, hs, hsx⟩ := hcon x
      exact hsx (MulAction.mem_fixedPoints.1 hx ⟨s, hs⟩)
    have hc0 : Nat.card (MulAction.fixedPoints T' (Fin m)) = 0 := by
      rw [hempty]
      simp
    have hcong := hT'.card_modEq_card_fixedPoints (Fin m)
    rw [hc0, hcard] at hcong
    obtain ⟨k, hk⟩ := hodd
    unfold Nat.ModEq at hcong
    omega
  obtain ⟨O, hO, h2, hOm⟩ : ∃ O : Finset (Fin m), (∀ s ∈ T', ∀ x ∈ O, s x ∈ O) ∧
      2 ≤ O.card ∧ O.card + 2 ≤ m := by
    rcases perm_two_subgroup_dichotomy hodd hm T' hT' with h | ⟨j, hj⟩
    · exact h
    · exact (hnp ⟨j, hj⟩).elim
  have hco : IsCoatom (MulAction.stabilizer (alternatingGroup (Fin m)) p) := by
    have h := alternatingGroup.isCoatom_stabilizer_singleton (α := Fin m)
      (s := ({p} : Set (Fin m))) (by rw [hcard]; omega) (Set.singleton_nonempty p)
      Set.subsingleton_singleton
    rwa [MulAction.stabilizer_singleton] at h
  refine ⟨MulAction.stabilizer (alternatingGroup (Fin m)) p,
    (young O).subgroupOf (alternatingGroup (Fin m)), hco.1, ?_, ?_, ?_⟩
  ·
    obtain ⟨σ, hσA, hσY⟩ := exists_even_not_mem_young O h2 hOm
    intro htop
    have hmem : (⟨σ, hσA⟩ : alternatingGroup (Fin m)) ∈
        (young O).subgroupOf (alternatingGroup (Fin m)) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hσY (Subgroup.mem_subgroupOf.1 hmem)
  ·
    obtain ⟨g, hgA, hgY, hgp⟩ := exists_even_mem_young_move O h2 hOm p
    have hle : MulAction.stabilizer (alternatingGroup (Fin m)) p ≤
        MulAction.stabilizer (alternatingGroup (Fin m)) p ⊔
          (young O).subgroupOf (alternatingGroup (Fin m)) := le_sup_left
    rcases hco.le_iff.1 hle with h | h
    · exact h
    · exfalso
      have hQ1 : (young O).subgroupOf (alternatingGroup (Fin m)) ≤
          MulAction.stabilizer (alternatingGroup (Fin m)) p :=
        le_of_le_of_eq le_sup_right h
      have hmem : (⟨g, hgA⟩ : alternatingGroup (Fin m)) ∈
          (young O).subgroupOf (alternatingGroup (Fin m)) :=
        Subgroup.mem_subgroupOf.2 hgY
      exact hgp (MulAction.mem_stabilizer_iff.1 (hQ1 hmem))
  ·
    rintro Q (rfl | rfl)
    · refine ⟨fun τ hτ g hg h => ?_, fun u hu => ?_⟩
      · have hg' : (g : Perm (Fin m)) p = p := MulAction.mem_stabilizer_iff.1 hg
        have hτinv : τ⁻¹ p = p := Equiv.Perm.inv_eq_iff_eq.2 (hp τ hτ).symm
        rw [MulAction.mem_stabilizer_iff]
        show (τ * (g : Perm (Fin m)) * τ⁻¹) p = p
        rw [Perm.mul_apply, Perm.mul_apply, hτinv, hg', hp τ hτ]
      · rw [MulAction.mem_stabilizer_iff]
        exact hp (u : Perm (Fin m)) hu
    · refine ⟨fun τ hτ g hg h => ?_, fun u hu => ?_⟩
      · have hτY : τ ∈ young O := mem_young_of_forall_mem O (hO τ hτ)
        have hgY : (g : Perm (Fin m)) ∈ young O := Subgroup.mem_subgroupOf.1 hg
        exact Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hτY hgY) (inv_mem hτY))
      · exact Subgroup.mem_subgroupOf.2 (mem_young_of_forall_mem O (hO _ hu))

end B69K

end CFSG.Quasithin
