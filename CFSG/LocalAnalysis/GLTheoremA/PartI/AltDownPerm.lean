module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.GLTheoremA.AltDown

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem pow_eq_one_of_mem_cycleFactorsFinset {σ c : Perm α} {p : ℕ} (hσ : σ ^ p = 1)
    (hc : c ∈ σ.cycleFactorsFinset) : c ^ p = 1 := by
  obtain ⟨a, ha⟩ := (mem_cycleFactorsFinset_iff.1 hc).1.nonempty_support
  rw [cycle_is_cycleOf ha hc]
  exact orderOf_dvd_iff_pow_eq_one.1
    ((orderOf_cycleOf_dvd_orderOf σ a).trans (orderOf_dvd_of_pow_eq_one hσ))

theorem mul_mul_inv_mem_cycleFactorsFinset {σ g c : Perm α} (hg : Commute g σ)
    (hc : c ∈ σ.cycleFactorsFinset) : g * c * g⁻¹ ∈ σ.cycleFactorsFinset := by
  have h := (mem_cycleFactorsFinset_conj σ g c).2 hc
  have e : g * σ * g⁻¹ = σ := by rw [hg.eq, mul_inv_cancel_right]
  rwa [e] at h

theorem apply_mem_support_of_commute {σ g : Perm α} (hg : Commute g σ) {u : α}
    (hu : u ∈ σ.support) : g u ∈ σ.support := by
  rw [mem_support] at hu ⊢
  intro h
  apply hu
  have h1 : g (σ u) = σ (g u) := congrArg (fun f : Perm α => f u) hg.eq
  apply g.injective
  rw [h1, h]

theorem exists_pow_apply_eq_of_commute {σ g : Perm α} {u : α} (hu : u ∈ σ.support)
    (hg : Commute g (σ.cycleOf u)) : ∃ j : ℕ, g u = ((σ.cycleOf u) ^ j) u := by
  have hu' : σ u ≠ u := mem_support.1 hu
  have hcyc : (σ.cycleOf u).IsCycle := isCycle_cycleOf σ hu'
  have hcu : σ.cycleOf u u ≠ u := by rwa [cycleOf_apply_self]
  have hgu : σ.cycleOf u (g u) ≠ g u := by
    intro e
    apply hcu
    have h1 : g (σ.cycleOf u u) = σ.cycleOf u (g u) := congrArg (fun f : Perm α => f u) hg.eq
    apply g.injective
    rw [h1, e]
  obtain ⟨j, hj⟩ := hcyc.exists_pow_eq hcu hgu
  exact ⟨j, hj.symm⟩

theorem apply_comm_of_mem_support {σ g g' : Perm α}
    (hg : ∀ c ∈ σ.cycleFactorsFinset, Commute g c) (hg' : ∀ c ∈ σ.cycleFactorsFinset, Commute g' c)
    {u : α} (hu : u ∈ σ.support) : g (g' u) = g' (g u) := by
  have hc : σ.cycleOf u ∈ σ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.2 hu
  obtain ⟨j, hj⟩ := exists_pow_apply_eq_of_commute hu (hg _ hc)
  obtain ⟨j', hj'⟩ := exists_pow_apply_eq_of_commute hu (hg' _ hc)
  have e1 : g ((σ.cycleOf u ^ j') u) = (σ.cycleOf u ^ j') (g u) :=
    congrArg (fun f : Perm α => f u) ((hg _ hc).pow_right j').eq
  have e2 : g' ((σ.cycleOf u ^ j) u) = (σ.cycleOf u ^ j) (g' u) :=
    congrArg (fun f : Perm α => f u) ((hg' _ hc).pow_right j).eq
  calc g (g' u) = g ((σ.cycleOf u ^ j') u) := by rw [hj']
    _ = (σ.cycleOf u ^ j') (g u) := e1
    _ = (σ.cycleOf u ^ j') ((σ.cycleOf u ^ j) u) := by rw [hj]
    _ = (σ.cycleOf u ^ j) ((σ.cycleOf u ^ j') u) := by
        rw [← Perm.mul_apply, ← Perm.mul_apply, ← pow_add, ← pow_add, add_comm]
    _ = (σ.cycleOf u ^ j) (g' u) := by rw [hj']
    _ = g' ((σ.cycleOf u ^ j) u) := e2.symm
    _ = g' (g u) := by rw [hj]

theorem commutator_apply_of_mem_support {σ g g' : Perm α} (hgσ : Commute g σ)
    (hg'σ : Commute g' σ) (hg : ∀ c ∈ σ.cycleFactorsFinset, Commute g c)
    (hg' : ∀ c ∈ σ.cycleFactorsFinset, Commute g' c) {u : α} (hu : u ∈ σ.support) :
    (g * g' * g⁻¹ * g'⁻¹) u = u := by
  have h1 : g'⁻¹ u ∈ σ.support := apply_mem_support_of_commute hg'σ.inv_left hu
  have h2 : g⁻¹ (g'⁻¹ u) ∈ σ.support := apply_mem_support_of_commute hgσ.inv_left h1
  have h3 := apply_comm_of_mem_support hg hg' h2
  have e : (g * g' * g⁻¹ * g'⁻¹) u = g (g' (g⁻¹ (g'⁻¹ u))) := rfl
  rw [e, h3]
  simp

@[expose] def cycleSet (σ : Perm α) : Set (alternatingGroup α) :=
  {c | (c : Perm α) ∈ σ.cycleFactorsFinset}

@[expose] def cycleGroup (σ : Perm α) : Subgroup (alternatingGroup α) :=
  Subgroup.closure (cycleSet σ)

theorem cycleSet_pairwise_commute (σ : Perm α) : (cycleSet σ).Pairwise Commute := by
  intro c hc c' hc' _
  exact Subtype.ext (cycleFactorsFinset_mem_commute' σ hc hc').eq

theorem commute_of_mem_cycleGroup {σ : Perm α} {n : alternatingGroup α}
    (hn : n ∈ cycleGroup σ) : Commute (n : Perm α) σ := by
  induction hn using Subgroup.closure_induction with
  | mem c hc => exact self_mem_cycle_factors_commute hc
  | one => exact Commute.one_left _
  | mul a b _ _ ha hb => exact ha.mul_left hb
  | inv a _ ha => exact ha.inv_left

theorem cycleGroup_conj_mem {σ : Perm α} {g : alternatingGroup α} (hg : Commute (g : Perm α) σ)
    {n : alternatingGroup α} (hn : n ∈ cycleGroup σ) : g * n * g⁻¹ ∈ cycleGroup σ := by
  induction hn using Subgroup.closure_induction with
  | mem c hc =>
    exact Subgroup.subset_closure
      (show ((g * c * g⁻¹ : alternatingGroup α) : Perm α) ∈ σ.cycleFactorsFinset from
        mul_mul_inv_mem_cycleFactorsFinset hg hc)
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem pow_eq_one_of_mem_cycleGroup {σ : Perm α} {p : ℕ} (hσ : σ ^ p = 1)
    {n : alternatingGroup α} (hn : n ∈ cycleGroup σ) : n ^ p = 1 := by
  haveI : IsMulCommutative (Subgroup.closure (cycleSet σ)) :=
    Subgroup.isMulCommutative_closure (cycleSet_pairwise_commute σ)
  have hn' : n ∈ Subgroup.closure (cycleSet σ) := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem c hc => exact Subtype.ext (pow_eq_one_of_mem_cycleFactorsFinset hσ hc)
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := setLike_mul_comm ha hb
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a _ ha => rw [inv_pow, ha, inv_one]

theorem exists_mem_cycleGroup_of_mem_cycleFactorsFinset {σ c : Perm α} {p : ℕ} (hp : Odd p)
    (hσ : σ ^ p = 1) (hc : c ∈ σ.cycleFactorsFinset) :
    ∃ c' ∈ cycleGroup σ, (c' : Perm α) = c := by
  have hcp : c ^ p = 1 := pow_eq_one_of_mem_cycleFactorsFinset hσ hc
  have hs : sign c ^ p = 1 := by rw [← map_pow, hcp, map_one]
  have hsc : sign c = 1 := by
    rcases Int.units_eq_one_or (sign c) with h | h
    · exact h
    · rw [h, hp.neg_one_pow] at hs
      exact absurd hs (by decide)
  exact ⟨⟨c, mem_alternatingGroup.2 hsc⟩, Subgroup.subset_closure hc, rfl⟩

theorem mem_range_ofSubtype_compl_iff (T : Finset α) (k : alternatingGroup α) :
    k ∈ (alternatingGroup.ofSubtype Tᶜ).range ↔ ∀ u ∈ T, (k : Perm α) u = u := by
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro h u hu
    by_contra hne
    exact (Finset.mem_compl.1 (h (mem_support.2 hne))) hu
  · intro h u hu
    rw [Finset.mem_compl]
    intro huT
    exact (mem_support.1 hu) (h u huT)

theorem nonempty_range_ofSubtype_equiv (s : Finset α) (m : ℕ) (h : s.card = m) :
    Nonempty ((alternatingGroup.ofSubtype s).range ≃* alternatingGroup (Fin m)) := by
  have e : ↥s ≃ Fin m := Fintype.equivFinOfCardEq (by simpa using h)
  exact ⟨(MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).symm.trans e.altCongrHom⟩

theorem le_card_support_of_pow_eq_one {p : ℕ} (hp : p.Prime) {σ : Perm α} (hσp : σ ^ p = 1)
    (hσ1 : σ ≠ 1) : p ≤ σ.support.card := by
  obtain ⟨u, hu⟩ : σ.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hσ1 (support_eq_empty_iff.1 h)
  have hc : σ.cycleOf u ∈ σ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.2 hu
  have hcyc : (σ.cycleOf u).IsCycle := isCycle_cycleOf _ (mem_support.1 hu)
  have hcp : σ.cycleOf u ^ p = 1 := pow_eq_one_of_mem_cycleFactorsFinset hσp hc
  have hne1 : orderOf (σ.cycleOf u) ≠ 1 := fun h => hcyc.ne_one (orderOf_eq_one_iff.1 h)
  have hord : orderOf (σ.cycleOf u) = p :=
    ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hcp)).resolve_left hne1
  calc p = (σ.cycleOf u).support.card := by rw [← hord, hcyc.orderOf]
    _ ≤ σ.support.card := Finset.card_le_card (support_cycleOf_le σ u)

theorem commute_of_mem_range_ofSubtype_compl {σ : Perm α} {k : alternatingGroup α}
    (hk : k ∈ (alternatingGroup.ofSubtype σ.supportᶜ).range) : Commute (k : Perm α) σ := by
  have hsupp : (k : Perm α).support ⊆ σ.supportᶜ :=
    (alternatingGroup.mem_range_ofSubtype_iff _ k).1 hk
  have hdisj : Disjoint (k : Perm α) σ := by
    rw [Perm.disjoint_iff_disjoint_support]
    exact Finset.disjoint_of_subset_left hsupp disjoint_compl_left
  exact hdisj.commute

theorem natCard_alternatingGroup_dvd_factorial (α : Type*) [Fintype α] [DecidableEq α] :
    Nat.card (alternatingGroup α) ∣ (Fintype.card α).factorial := by
  have h : Nat.card (alternatingGroup α) ∣ Nat.card (Perm α) := Subgroup.card_subgroup_dvd_card _
  simpa [Nat.card_eq_fintype_card, Fintype.card_perm] using h

end CFSG.LocalAnalysis.GLTheoremA.AltDown
