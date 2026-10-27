module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

private theorem toList_eq_map_getElem! {α : Type*} [Inhabited α] (E : Array α) :
    E.toList = (List.range E.size).map (fun k => E[k]!) := by
  refine List.ext_getElem (by simp) fun n h1 _ => ?_
  have hn : n < E.size := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  rw [getElem!_pos E n hn]

private theorem ncard_eq_length_of_nodup {α : Type*} {S : Set α} {L : List α} (hL : L.Nodup)
    (h : ∀ x, x ∈ S ↔ x ∈ L) : S.ncard = L.length := by
  classical
  have : S = (L.toFinset : Set α) := by
    ext x
    rw [h x, Finset.mem_coe, List.mem_toFinset]
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

private theorem ncard_filter_size (E : Array Table) (b : Table → Bool) :
    {k : ℕ | k < E.size ∧ b E[k]! = true}.ncard = (E.filter b).size := by
  have hcount : E.toList.countP b = ((List.range E.size).filter fun k => b E[k]!).length := by
    rw [toList_eq_map_getElem!, List.countP_eq_length_filter, List.filter_map, List.length_map]
    rfl
  have hlen : ((List.range E.size).filter fun k => b E[k]!).length = (E.filter b).size := by
    rw [← hcount, Array.countP_toList (p := b) (xs := E),
      Array.countP_eq_size_filter (p := b) (xs := E)]
  rw [← hlen]
  exact ncard_eq_length_of_nodup ((List.nodup_range (n := E.size)).filter _) fun x => by
    simp only [Set.mem_setOf_eq, List.mem_filter, List.mem_range]

theorem getElem!_map_of_lt_size {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β)
    (a : Array α) {i : ℕ} (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using hi), getElem!_pos a i hi]
  simp

theorem size_subgroupList_of_enumW {cap m : ℕ} {ws : List (List ℕ)} (h : enumW cap m ws = true) :
    (subgroupList cap ws).size = m := by
  simp only [enumW, enumOKH, Bool.and_eq_true, beq_iff_eq] at h
  simpa only [subgroupList] using h.2.2

theorem IsEnumSet.filter {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (b : Table → Bool) (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → (b x = true ↔ Q g)) :
    IsEnumSet n (E.filter b) {g : Equiv.Perm (Fin n) | g ∈ S ∧ Q g} := by
  constructor
  · intro k hk
    have hmem : (E.filter b)[k]! ∈ E.filter b := getElem!_mem_array hk
    rw [Array.mem_filter] at hmem
    obtain ⟨hmemE, hbtrue⟩ := hmem
    obtain ⟨j, hj, hjE⟩ := Array.getElem_of_mem hmemE
    obtain ⟨g, hgS, hrep⟩ := h.rep j hj
    have hjt : (E.filter b)[k]! = E[j]! := by
      rw [getElem!_pos E j hj, ← hjE]
    have hrep' : Rep n (E.filter b)[k]! g := by rw [hjt]; exact hrep
    exact ⟨g, ⟨hgS, (hb (E.filter b)[k]! g hrep').1 hbtrue⟩, hrep'⟩
  · intro g hg
    obtain ⟨hgS, hQg⟩ := hg
    obtain ⟨j, hj, hrep⟩ := h.cov g hgS
    have hbj : b E[j]! = true := (hb (E[j]!) g hrep).2 hQg
    have hmemf : E[j]! ∈ E.filter b := by
      rw [Array.mem_filter]
      exact ⟨getElem!_mem_array hj, hbj⟩
    obtain ⟨k, hk, hkE⟩ := Array.getElem_of_mem hmemf
    refine ⟨k, hk, ?_⟩
    have hkt : (E.filter b)[k]! = E[j]! := by
      rw [getElem!_pos (E.filter b) k hk, hkE]
    rw [hkt]; exact hrep

theorem IsEnumSet.ncard_filter {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (hsize : E.size = S.ncard) (b : Table → Bool)
    (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → (b x = true ↔ Q g)) :
    {g : Equiv.Perm (Fin n) | g ∈ S ∧ Q g}.ncard = (E.filter b).size := by
  classical
  let π : ℕ → Equiv.Perm (Fin n) :=
    fun k => if hk : k < E.size then Classical.choose (h.rep k hk) else 1
  have hπrep : ∀ k (hk : k < E.size), Rep n E[k]! (π k) := by
    intro k hk
    simpa only [π, dif_pos hk] using (Classical.choose_spec (h.rep k hk)).2
  have hπmem : ∀ k (hk : k < E.size), π k ∈ S := by
    intro k hk
    simpa only [π, dif_pos hk] using (Classical.choose_spec (h.rep k hk)).1
  have himage : π '' {k : ℕ | k < E.size} = S := by
    apply Set.Subset.antisymm
    · rintro g ⟨k, hk, rfl⟩
      exact hπmem k hk
    · intro g hg
      obtain ⟨k, hk, hrep⟩ := h.cov g hg
      exact ⟨k, hk, rep_unique (hπrep k hk) hrep⟩
  have hcard : (π '' {k : ℕ | k < E.size}).ncard = ({k : ℕ | k < E.size} : Set ℕ).ncard := by
    rw [himage, ← hsize]
    exact (Set.ncard_Iio_nat E.size).symm
  have hinj : Set.InjOn π {k : ℕ | k < E.size} :=
    Set.injOn_of_ncard_image_eq hcard (Set.finite_Iio E.size)
  let s' : Set ℕ := {k : ℕ | k < E.size ∧ b E[k]! = true}
  let T : Set (Equiv.Perm (Fin n)) := {g : Equiv.Perm (Fin n) | g ∈ S ∧ Q g}
  have hT : T = π '' s' := by
    apply Set.Subset.antisymm
    · rintro g ⟨hgS, hQg⟩
      obtain ⟨k, hk, hrep⟩ := h.cov g hgS
      have hbk : b E[k]! = true := (hb (E[k]!) g hrep).2 hQg
      exact ⟨k, ⟨hk, hbk⟩, rep_unique (hπrep k hk) hrep⟩
    · rintro g ⟨k, ⟨hk, hbk⟩, rfl⟩
      exact ⟨hπmem k hk, (hb (E[k]!) (π k) (hπrep k hk)).1 hbk⟩
  have hinj' : Set.InjOn π s' := by
    intro k hk l hl hkl
    simp only [s', Set.mem_setOf_eq] at hk hl
    exact hinj hk.1 hl.1 hkl
  have hTs : T.ncard = s'.ncard := by
    rw [hT, hinj'.ncard_image]
  have hmain : T.ncard = (E.filter b).size := by
    rw [hTs]
    exact ncard_filter_size E b
  simpa only [T] using hmain

end CFSG.EvenSporadicStandard.HNRecog
