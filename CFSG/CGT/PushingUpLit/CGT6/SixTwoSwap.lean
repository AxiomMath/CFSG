module

public import CFSG.CGT.PushingUpLit.BHS6.NestedPerm

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b CFSG.CGT.PushingUpLit.BHS
open CFSG.CGT.PushingUpLit.BHS6

variable {n : ℕ}

theorem exists_setStab_swaps_mem (hn : Odd n) {T : Set (Equiv.Perm (Fin n))}
    (hT : ∀ t ∈ T, t.IsSwap) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t)
    (hcard : T.ncard = (n - 1) / 2) {t₀ : Equiv.Perm (Fin n)} (ht₀ : t₀ ∈ T) {r : ℕ}
    (hr : r ≤ n) (hr2 : 2 ≤ r) :
    ∃ S : Finset (Fin n), S.card = r ∧ (∀ t ∈ T, t ∈ setStab S) ∧ t₀.support ⊆ S := by
  classical
  have hfin : T.Finite := Set.toFinite T
  set Tf := hfin.toFinset with hTf
  have hTfc : Tf.card = (n - 1) / 2 := by rw [← hcard, Set.ncard_eq_toFinset_card T hfin]
  have hsupp : ∀ t ∈ Tf, t.support.card = 2 := fun t ht =>
    Equiv.Perm.card_support_eq_two.2 (hT t (hfin.mem_toFinset.1 ht))
  have hdisj : ∀ s ⊆ Tf, (s : Set (Equiv.Perm (Fin n))).PairwiseDisjoint Equiv.Perm.support :=
    fun s hs t ht t' ht' hne => disjoint_support_of_commute
      (hT t (hfin.mem_toFinset.1 (hs ht))) (hT t' (hfin.mem_toFinset.1 (hs ht')))
      (hc t (hfin.mem_toFinset.1 (hs ht)) t' (hfin.mem_toFinset.1 (hs ht'))) hne
  have hcardU : ∀ s ⊆ Tf, (s.biUnion Equiv.Perm.support).card = 2 * s.card := by
    intro s hs
    rw [Finset.card_biUnion (hdisj s hs), Finset.sum_congr rfl fun t ht => hsupp t (hs ht),
      Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ Tf.biUnion Equiv.Perm.support := by
    apply exists_notMem_finset
    rw [hcardU Tf le_rfl, hTfc]
    obtain ⟨j, rfl⟩ := hn
    omega
  have ht₀Tf : t₀ ∈ Tf := hfin.mem_toFinset.2 ht₀
  obtain ⟨T₀, hT₀s, hT₀, hT₀c⟩ := Finset.exists_subsuperset_card_eq (s := {t₀}) (t := Tf)
    (n := r / 2) (Finset.singleton_subset_iff.2 ht₀Tf) (by simp; omega)
    (by rw [hTfc]; obtain ⟨j, rfl⟩ := hn; omega)
  have ht₀T₀ : t₀ ∈ T₀ := hT₀s (Finset.mem_singleton_self t₀)
  set B := T₀.biUnion Equiv.Perm.support with hB
  have hBc : B.card = 2 * (r / 2) := by rw [hcardU T₀ hT₀, hT₀c]
  have hv₀B : v₀ ∉ B := fun h => hv₀ (Finset.biUnion_subset_biUnion_of_subset_left _ hT₀ h)
  have ht₀B : t₀.support ⊆ B := Finset.subset_biUnion_of_mem Equiv.Perm.support ht₀T₀
  refine ⟨if r % 2 = 1 then insert v₀ B else B, ?_, fun t ht => ?_, ?_⟩
  · split_ifs with h
    · rw [Finset.card_insert_of_notMem hv₀B, hBc]
      omega
    · rw [hBc]
      omega
  · have htT : t ∈ Tf := hfin.mem_toFinset.2 ht
    have hBt : ∀ x ∈ B, t x ∈ B := by
      intro x hx
      obtain ⟨t₁, ht₁, hx₁⟩ := Finset.mem_biUnion.1 hx
      by_cases h₁ : t₁ = t
      · subst h₁
        exact Finset.mem_biUnion.2 ⟨t₁, ht₁, Equiv.Perm.apply_mem_support.2 hx₁⟩
      · have ht₁T := hfin.mem_toFinset.1 (hT₀ ht₁)
        rw [apply_eq_of_commute_swap (hT t₁ ht₁T) (hT t ht) (hc t₁ ht₁T t ht) h₁
          (Equiv.Perm.mem_support.1 hx₁)]
        exact hx
    have htv₀ : t v₀ = v₀ := by
      by_contra hne
      exact hv₀ (Finset.mem_biUnion.2 ⟨t, htT, Equiv.Perm.mem_support.2 hne⟩)
    have hinto : ∀ x ∈ (if r % 2 = 1 then insert v₀ B else B), t x ∈
        (if r % 2 = 1 then insert v₀ B else B) := by
      intro x hx
      split_ifs at hx ⊢ with h
      · rcases Finset.mem_insert.1 hx with rfl | hx
        · rw [htv₀]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hBt x hx)
      · exact hBt x hx
    have hinv : ∀ x, t (t x) = x := by
      obtain ⟨a, b, -, rfl⟩ := hT t ht
      exact fun x => Equiv.swap_apply_self a b x
    intro x
    exact ⟨fun h => hinv x ▸ hinto _ h, hinto x⟩
  · split_ifs with h
    · exact ht₀B.trans (Finset.subset_insert _ _)
    · exact ht₀B

theorem exists_conj_setStab_swap (hn : Odd n) {T : Set (Equiv.Perm (Fin n))}
    (hT : ∀ t ∈ T, t.IsSwap) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t)
    (hcard : T.ncard = (n - 1) / 2) {t₀ : Equiv.Perm (Fin n)} (ht₀ : t₀ ∈ T)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    ∃ g : Equiv.Perm (Fin n), (∀ y ∈ Subgroup.closure T, g * y * g⁻¹ ∈ setStab S) ∧
      ∃ i j : Fin n, i ≠ j ∧ i ∈ S ∧ j ∈ S ∧ g * t₀ * g⁻¹ = Equiv.swap i j := by
  classical
  obtain ⟨S', hS'c, hS', ht₀S'⟩ := exists_setStab_swaps_mem hn hT hc hcard ht₀
    (r := S.card) (by simpa using Finset.card_le_univ S) hS
  have hY' : Subgroup.closure T ≤ setStab S' := (Subgroup.closure_le _).2 hS'
  let e : {x // x ∈ S'} ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hS'c])
  set g := e.extendSubtype with hgdef
  have hg : ∀ z, g z ∈ S ↔ z ∈ S' := fun z => by
    by_cases hz : z ∈ S'
    · exact ⟨fun _ => hz, fun _ => e.extendSubtype_mem z hz⟩
    · exact ⟨fun h => absurd h (e.extendSubtype_not_mem z hz), fun h => absurd h hz⟩
  refine ⟨g, fun y hy => ?_, ?_⟩
  · have hy0 := mem_setStab.mp (hY' hy)
    rw [mem_setStab]
    intro x
    have e1 : (g * y * g⁻¹) x = g (y (g⁻¹ x)) := by simp [Equiv.Perm.mul_apply]
    rw [e1, hg, hy0 (g⁻¹ x), ← hg (g⁻¹ x), perm_apply_inv_self]
  · obtain ⟨p, q, hpq, hpqt⟩ := hT t₀ ht₀
    have hsupp : t₀.support = {p, q} := by rw [hpqt, Equiv.Perm.support_swap hpq]
    have hp : p ∈ S' := ht₀S' (by rw [hsupp]; simp)
    have hq : q ∈ S' := ht₀S' (by rw [hsupp]; simp)
    refine ⟨g p, g q, g.injective.ne hpq, (hg p).2 hp, (hg q).2 hq, ?_⟩
    rw [hpqt, Equiv.swap_apply_apply g p q]

theorem exists_even_conj_swap (hn : Odd n) {T : Set (Equiv.Perm (Fin n))}
    (hT : ∀ t ∈ T, t.IsSwap) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t)
    {t₀ : Equiv.Perm (Fin n)} (ht₀ : t₀ ∈ T) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    ∃ σ ∈ alternatingGroup (Fin n), (∀ y ∈ Subgroup.closure T, σ * y * σ⁻¹ ∈ setStab S) ∧
      ∃ i j : Fin n, i ≠ j ∧ i ∈ S ∧ j ∈ S ∧ σ * t₀ * σ⁻¹ = Equiv.swap i j := by
  obtain ⟨T'', hT'', hs'', hc'', hcard⟩ := exists_isMaxSwapGroup_ge hn hT hc
  obtain ⟨g, hg1, i, j, hij, hi, hj, hg2⟩ :=
    exists_conj_setStab_swap hn hs'' hc'' hcard (hT'' ht₀) S hS
  have ht₀cl : t₀ ∈ Subgroup.closure T'' := Subgroup.subset_closure (hT'' ht₀)
  have hcl : ∀ y ∈ Subgroup.closure T, y ∈ Subgroup.closure T'' := fun y hy =>
    Subgroup.closure_mono hT'' hy
  have hs0 : Equiv.Perm.sign t₀ = -1 := (hT t₀ ht₀).sign_eq
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hsg | hsg
  · exact ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hsg, fun y hy => hg1 y (hcl y hy), i, j, hij,
      hi, hj, hg2⟩
  · refine ⟨g * t₀, Equiv.Perm.mem_alternatingGroup.mpr ?_, fun y hy => ?_, i, j, hij, hi, hj, ?_⟩
    · rw [Equiv.Perm.sign_mul, hsg, hs0]
      decide
    · have e1 : (g * t₀) * y * (g * t₀)⁻¹ = g * (t₀ * y * t₀⁻¹) * g⁻¹ := by group
      rw [e1]
      exact hg1 _ ((Subgroup.closure T'').mul_mem
        ((Subgroup.closure T'').mul_mem ht₀cl (hcl y hy)) ((Subgroup.closure T'').inv_mem ht₀cl))
    · rw [← hg2]
      group

end CFSG.CGT.PushingUpLit.CGT6
