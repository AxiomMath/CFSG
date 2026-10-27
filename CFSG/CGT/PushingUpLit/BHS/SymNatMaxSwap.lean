module

public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbits
public import CFSG.CGT.PushingUpLit.BHS.SymNatSwaps

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b

variable {n : ℕ}

@[expose] def setStab (S : Finset (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {a | ∀ x, a x ∈ S ↔ x ∈ S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => by rw [Equiv.Perm.mul_apply, ha, hb]
  inv_mem' := fun {a} ha x => by
    show a⁻¹ x ∈ S ↔ x ∈ S
    rw [← ha (a⁻¹ x), perm_apply_inv_self]

theorem mem_setStab {S : Finset (Fin n)} {a : Equiv.Perm (Fin n)} :
    a ∈ setStab S ↔ ∀ x, a x ∈ S ↔ x ∈ S := Iff.rfl

theorem disjoint_support_of_commute {t t' : Equiv.Perm (Fin n)} (ht : t.IsSwap)
    (ht' : t'.IsSwap) (hc : t * t' = t' * t) (hne : t ≠ t') : Disjoint t.support t'.support :=
  Finset.disjoint_left.2 fun _ hx hx' =>
    Equiv.Perm.mem_support.1 hx' (apply_eq_of_commute_swap ht ht' hc hne
      (Equiv.Perm.mem_support.1 hx))

theorem exists_setStab_swaps (hn : Odd n) {T : Set (Equiv.Perm (Fin n))}
    (hT : ∀ t ∈ T, t.IsSwap) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t)
    (hcard : T.ncard = (n - 1) / 2) {r : ℕ} (hr : r ≤ n) :
    ∃ S : Finset (Fin n), S.card = r ∧ ∀ t ∈ T, t ∈ setStab S := by
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
  obtain ⟨T₀, hT₀, hT₀c⟩ := Finset.exists_subset_card_eq (s := Tf) (n := r / 2)
    (by rw [hTfc]; obtain ⟨j, rfl⟩ := hn; omega)
  set B := T₀.biUnion Equiv.Perm.support with hB
  have hBc : B.card = 2 * (r / 2) := by rw [hcardU T₀ hT₀, hT₀c]
  have hv₀B : v₀ ∉ B := fun h => hv₀ (Finset.biUnion_subset_biUnion_of_subset_left _ hT₀ h)
  refine ⟨if r % 2 = 1 then insert v₀ B else B, ?_, fun t ht => ?_⟩
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

theorem exists_conjSub_le_setStab (hn : Odd n) {Y : Subgroup (Equiv.Perm (Fin n))}
    (hY : IsMaxSwapGroup Y) (S : Finset (Fin n)) :
    ∃ g : Equiv.Perm (Fin n), conjSub g Y ≤ setStab S := by
  classical
  obtain ⟨T, hT, hc, hcard, rfl⟩ := hY
  obtain ⟨S', hS'c, hS'⟩ := exists_setStab_swaps hn hT hc hcard
    (by simpa using Finset.card_le_univ S)
  have hY' : Subgroup.closure T ≤ setStab S' := (Subgroup.closure_le _).2 hS'
  let e : {x // x ∈ S'} ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hS'c])
  set g := e.extendSubtype with hgdef
  have hg : ∀ z, g z ∈ S ↔ z ∈ S' := fun z => by
    by_cases hz : z ∈ S'
    · exact ⟨fun _ => hz, fun _ => e.extendSubtype_mem z hz⟩
    · exact ⟨fun h => absurd h (e.extendSubtype_not_mem z hz), fun h => absurd h hz⟩
  refine ⟨g, fun y hy => ?_⟩
  rw [mem_conjSub_iff] at hy
  have hy0 := hY' hy
  intro x
  have h1 : y x = g ((g⁻¹ * y * g) (g⁻¹ x)) := by
    simp only [Equiv.Perm.mul_apply, perm_apply_inv_self]
  rw [h1, hg, hy0, ← hg, perm_apply_inv_self]

theorem pairwise_disjoint_of_swaps {S : Set (Equiv.Perm (Fin n))} (hS : ∀ t ∈ S, t.IsSwap)
    (hc : ∀ t ∈ S, ∀ t' ∈ S, t * t' = t' * t) : S.Pairwise Equiv.Perm.Disjoint := by
  intro t ht t' ht' hne x
  by_cases hx : t x = x
  · exact Or.inl hx
  · exact Or.inr (apply_eq_of_commute_swap (hS t ht) (hS t' ht') (hc t ht t' ht') hne hx)

theorem exists_prod_swaps {T : Set (Equiv.Perm (Fin n))} (hT : ∀ t ∈ T, t.IsSwap)
    (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) :
    ∃ σ : Equiv.Perm (Fin n), (σ.cycleFactorsFinset : Set (Equiv.Perm (Fin n))) = T ∧
      σ.cycleType = Multiset.replicate T.ncard 2 := by
  classical
  have hfin : T.Finite := Set.toFinite T
  have hd : ((hfin.toFinset : Finset (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))).Pairwise
      Equiv.Perm.Disjoint := by
    rw [hfin.coe_toFinset]
    exact pairwise_disjoint_of_swaps hT hc
  refine ⟨hfin.toFinset.noncommProd id (hd.mono' fun _ _ => Equiv.Perm.Disjoint.commute),
    ?_, ?_⟩
  · rw [Equiv.Perm.cycleFactorsFinset_eq_finset.2
      ⟨fun f hf => (hT f (hfin.mem_toFinset.1 hf)).isCycle, hd, rfl⟩, hfin.coe_toFinset]
  · rw [Equiv.Perm.cycleType_def, Equiv.Perm.cycleFactorsFinset_eq_finset.2
      ⟨fun f hf => (hT f (hfin.mem_toFinset.1 hf)).isCycle, hd, rfl⟩,
      Set.ncard_eq_toFinset_card T hfin, Multiset.eq_replicate]
    refine ⟨by rw [Multiset.card_map, Finset.card_val], fun b hb => ?_⟩
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hb
    exact Equiv.Perm.card_support_eq_two.2 (hT t (hfin.mem_toFinset.1 ht))

theorem exists_conjSub_eq_of_isMaxSwapGroup {Y Y' : Subgroup (Equiv.Perm (Fin n))}
    (hY : IsMaxSwapGroup Y) (hY' : IsMaxSwapGroup Y') :
    ∃ g : Equiv.Perm (Fin n), conjSub g Y = Y' := by
  obtain ⟨T, hT, hc, hcard, rfl⟩ := hY
  obtain ⟨T', hT', hc', hcard', rfl⟩ := hY'
  obtain ⟨σ, hσ, hσt⟩ := exists_prod_swaps hT hc
  obtain ⟨σ', hσ', hσt'⟩ := exists_prod_swaps hT' hc'
  obtain ⟨g, hg⟩ := isConj_iff.1 ((Equiv.Perm.isConj_iff_cycleType_eq (σ := σ) (τ := σ')).2
    (by rw [hσt, hσt', hcard, hcard']))
  refine ⟨g, ?_⟩
  have hmap := Equiv.Perm.cycleFactorsFinset_conj σ g
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hg] at hmap
  unfold conjSub
  rw [MonoidHom.map_closure, ← hσ, ← hσ', hmap, Finset.coe_map]
  rfl

end CFSG.CGT.PushingUpLit.BHS
