module

public import CFSG.LieType.Chevalley.WeylExchange
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def dynkinGraph (τ : Tag) : SimpleGraph (Fin τ.rank) where
  Adj i j := i ≠ j ∧ 0 < τ.cartan i j * τ.cartan j i
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [mul_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (τ : Tag) : DecidableRel (dynkinGraph τ).Adj := fun i j =>
  decidable_of_iff (i ≠ j ∧ 0 < τ.cartan i j * τ.cartan j i) Iff.rfl

theorem dynkinGraph_connected (τ : Tag) : (dynkinGraph τ).Connected := by
  have hne : Nonempty (Fin τ.rank) := ⟨⟨0, by cases τ <;> decide⟩⟩
  refine @SimpleGraph.Connected.mk _ _ (fun u v => ?_) hne
  have h0 : ∀ v : Fin τ.rank, (dynkinGraph τ).Reachable ⟨0, by cases τ <;> decide⟩ v := by
    have adj : ∀ (a b : ℕ) (ha : a < τ.rank) (hb : b < τ.rank),
        (dynkinGraph τ).Adj ⟨a, ha⟩ ⟨b, hb⟩ → (dynkinGraph τ).Reachable ⟨a, ha⟩ ⟨b, hb⟩ :=
      fun _ _ _ _ h => h.reachable
    cases τ
    · intro v
      fin_cases v
      · rfl
      · exact adj 0 1 (by decide) (by decide) (by decide)
    · have h1 := adj 0 1 (by decide) (by decide) (by decide)
      have h2 := h1.trans (adj 1 2 (by decide) (by decide) (by decide))
      intro v
      fin_cases v
      · rfl
      · exact h1
      · exact h2
      · exact h2.trans (adj 2 3 (by decide) (by decide) (by decide))
    · have h2 := adj 0 2 (by decide) (by decide) (by decide)
      intro v
      fin_cases v
      · rfl
      · exact h2.trans (adj 2 1 (by decide) (by decide) (by decide))
      · exact h2
      · exact h2.trans (adj 2 3 (by decide) (by decide) (by decide))
    all_goals
      have h2 := adj 0 2 (by decide) (by decide) (by decide)
      have h3 := h2.trans (adj 2 3 (by decide) (by decide) (by decide))
      have h1 := h3.trans (adj 3 1 (by decide) (by decide) (by decide))
      have h4 := h3.trans (adj 3 4 (by decide) (by decide) (by decide))
      have h5 := h4.trans (adj 4 5 (by decide) (by decide) (by decide))
    · intro v
      fin_cases v
      · rfl
      all_goals assumption
    · have h6 := h5.trans (adj 5 6 (by decide) (by decide) (by decide))
      intro v
      fin_cases v
      · rfl
      all_goals assumption
    · have h6 := h5.trans (adj 5 6 (by decide) (by decide) (by decide))
      have h7 := h6.trans (adj 6 7 (by decide) (by decide) (by decide))
      intro v
      fin_cases v
      · rfl
      all_goals assumption
  exact (h0 u).symm.trans (h0 v)

theorem height_reflect_pos_of_adj (τ : Tag) :
    ∀ i j : Fin τ.rank, (dynkinGraph τ).Adj i j →
      0 < height (reflect τ i (Pi.single j 1)) ∧
        0 < height (reflect τ j (reflect τ i (Pi.single j 1))) := by
  cases τ <;> decide

theorem length_simple_mul_simple
    {τ : Tag} {i j : Fin τ.rank} (h : (dynkinGraph τ).Adj i j) :
    (coxeterSystem τ).length (simple τ j * simple τ i) = 2 ∧
      (coxeterSystem τ).length (simple τ j * simple τ i * simple τ j) = 3 := by
  have hex := (weyl_exchange_condition τ).1
  have hpos : ∀ (a b : Fin τ.rank), (dynkinGraph τ).Adj a b →
      (coxeterSystem τ).length (simple τ b * simple τ a) = 2 := fun a b hab => by
    have hr : IsRoot τ (reflect τ a (Pi.single b 1)) := IsRoot.reflect a (isRoot_single τ b)
    have := (hex (simple τ a) b).2 ⟨by rw [simple_inv, simple_smul]; exact hr,
      by rw [simple_inv, simple_smul]; exact (height_reflect_pos_of_adj τ a b hab).1⟩
    rw [this, (coxeterSystem τ).length_simple]
  refine ⟨hpos i j h, ?_⟩
  have hij := hpos j i h.symm
  have hr : IsRoot τ (reflect τ j (reflect τ i (Pi.single j 1))) :=
    IsRoot.reflect j (IsRoot.reflect i (isRoot_single τ j))
  have := (hex (simple τ i * simple τ j) j).2 ⟨by
      rw [mul_inv_rev, simple_inv, simple_inv, mul_smul, simple_smul, simple_smul]; exact hr,
    by
      rw [mul_inv_rev, simple_inv, simple_inv, mul_smul, simple_smul, simple_smul]
      exact (height_reflect_pos_of_adj τ i j h).2⟩
  rw [mul_assoc, this, hij]

theorem connected_weyl_diagram
    (τ : Tag) :
    (dynkinGraph τ).Connected ∧
    (∀ i j : Fin τ.rank, (dynkinGraph τ).Adj i j →
      (coxeterSystem τ).length (simple τ j * simple τ i) = 2 ∧
        (coxeterSystem τ).length (simple τ j * simple τ i * simple τ j) = 3) ∧
    ∀ J : Set (Fin τ.rank), J.Nonempty → J ≠ Set.univ →
      ∃ i ∈ J, ∃ j ∉ J, (dynkinGraph τ).Adj i j ∧
        (coxeterSystem τ).length (simple τ j * simple τ i) = 2 ∧
        (coxeterSystem τ).length (simple τ j * simple τ i * simple τ j) = 3 := by
  refine ⟨dynkinGraph_connected τ, fun i j h => length_simple_mul_simple h, fun J hJ hJu => ?_⟩
  obtain ⟨u, hu⟩ := hJ
  obtain ⟨v, hv⟩ : ∃ v, v ∉ J := by
    by_contra h
    push Not at h
    exact hJu (Set.eq_univ_of_forall h)
  obtain ⟨p⟩ := (dynkinGraph_connected τ).preconnected u v
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart J hu hv
  exact ⟨d.fst, hd1, d.snd, hd2, d.adj, length_simple_mul_simple d.adj⟩

end CFSG.LieType.Chevalley
