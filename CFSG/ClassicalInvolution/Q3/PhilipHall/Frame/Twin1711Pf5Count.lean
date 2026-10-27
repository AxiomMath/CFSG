module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Set.Card

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

theorem mem_of_nodup_card {M : Type} [Group M] [Finite M] (K : Subgroup M) (l : List M)
    (hnd : l.Nodup) (hK : ∀ x ∈ l, x ∈ K) (hcard : l.length = Nat.card K) {g : M} (hg : g ∈ K) :
    g ∈ l := by
  classical
  by_contra hne
  have : Fintype M := Fintype.ofFinite M
  have hcard' : l.toFinset.card = Nat.card K := by
    rw [List.toFinset_card_of_nodup hnd, hcard]
  have hnot : g ∉ l.toFinset := fun h => hne (List.mem_toFinset.1 h)
  have hsub : insert g l.toFinset ⊆ (Finset.univ : Finset M).filter (fun x => x ∈ K) := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using hg
    · simpa using hK x (List.mem_toFinset.1 hx)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hcard'] at h1
  have h2 : ((Finset.univ : Finset M).filter (fun x => x ∈ K)).card = Nat.card K := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem ncard_le_of_subset_list {M : Type} (S : Set M) (l : List M) (hS : ∀ x ∈ S, x ∈ l) :
    S.ncard ≤ l.length := by
  classical
  calc S.ncard ≤ (l.toFinset : Set M).ncard :=
        Set.ncard_le_ncard (fun x hx => by simpa using hS x hx) (Finset.finite_toSet _)
    _ = l.toFinset.card := Set.ncard_coe_finset _
    _ ≤ l.length := List.toFinset_card_le _

theorem card_le_of_subset_list {M : Type} [Group M] (K : Subgroup M) (l : List M) (hK : ∀ x ∈ K, x ∈ l) :
    Nat.card K ≤ l.length := by
  have := ncard_le_of_subset_list (K : Set M) l hK
  rwa [← Nat.card_coe_set_eq] at this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711
