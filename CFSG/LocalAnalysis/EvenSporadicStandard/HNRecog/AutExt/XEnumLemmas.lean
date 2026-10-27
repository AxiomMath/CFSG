module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.EnumCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem forall_iff_of_mem {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (b : Table → Bool) (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → g ∈ S → (b x = true ↔ Q g)) :
    E.all b = true ↔ ∀ g ∈ S, Q g := by
  constructor
  · intro hm g hg
    rw [Array.all_eq_true'] at hm
    obtain ⟨k, hk, hrep⟩ := h.cov g hg
    exact (hb (E[k]!) g hrep hg).1 (hm (E[k]!) (getElem!_mem_array hk))
  · intro hQ
    rw [Array.all_eq_true']
    intro x hx
    obtain ⟨k, hk, hkT⟩ := Array.getElem_of_mem hx
    obtain ⟨g, hgS, hrep⟩ := h.rep k hk
    have hbk : b (E[k]!) = true := (hb (E[k]!) g hrep hgS).2 (hQ g hgS)
    have hxE : x = E[k]! := hkT.symm.trans (getElem!_pos E k hk).symm
    rw [hxE]
    exact hbk

theorem exists_iff_of_mem {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (b : Table → Bool) (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → g ∈ S → (b x = true ↔ Q g)) :
    E.any b = true ↔ ∃ g ∈ S, Q g := by
  constructor
  · intro hm
    rw [Array.any_eq_true'] at hm
    obtain ⟨x, hx, hbx⟩ := hm
    obtain ⟨k, hk, hkT⟩ := Array.getElem_of_mem hx
    obtain ⟨g, hgS, hrep⟩ := h.rep k hk
    have hxE : x = E[k]! := hkT.symm.trans (getElem!_pos E k hk).symm
    have hrep' : Rep n x g := by rw [hxE]; exact hrep
    exact ⟨g, hgS, (hb x g hrep' hgS).1 hbx⟩
  · rintro ⟨g, hgS, hQg⟩
    obtain ⟨k, hk, hrep⟩ := h.cov g hgS
    rw [Array.any_eq_true']
    exact ⟨E[k]!, getElem!_mem_array hk, (hb (E[k]!) g hrep hgS).2 hQg⟩

theorem IsEnumSet.filter_of_mem {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (b : Table → Bool) (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → g ∈ S → (b x = true ↔ Q g)) :
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
    exact ⟨g, ⟨hgS, (hb (E.filter b)[k]! g hrep' hgS).1 hbtrue⟩, hrep'⟩
  · intro g hg
    obtain ⟨hgS, hQg⟩ := hg
    obtain ⟨j, hj, hrep⟩ := h.cov g hgS
    have hbj : b E[j]! = true := (hb (E[j]!) g hrep hgS).2 hQg
    have hmemf : E[j]! ∈ E.filter b := by
      rw [Array.mem_filter]
      exact ⟨getElem!_mem_array hj, hbj⟩
    obtain ⟨k, hk, hkE⟩ := Array.getElem_of_mem hmemf
    refine ⟨k, hk, ?_⟩
    have hkt : (E.filter b)[k]! = E[j]! := by
      rw [getElem!_pos (E.filter b) k hk, hkE]
    rw [hkt]; exact hrep

theorem forall_of_all {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (b : Table → Bool) (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → g ∈ S → b x = true → Q g)
    (hall : E.all b = true) : ∀ g ∈ S, Q g := by
  intro g hg
  rw [Array.all_eq_true'] at hall
  obtain ⟨k, hk, hrep⟩ := h.cov g hg
  exact hb (E[k]!) g hrep hg (hall (E[k]!) (getElem!_mem_array hk))

theorem memT_of_mem_array {n : ℕ} {E : Array Table} {x : Table} (hx : x ∈ E) :
    memT n E x = true := by
  rw [memT, Array.any_eq_true']
  refine ⟨x, hx, ?_⟩
  rw [tblEq, allIn_eq_true]
  intro i _ _
  exact beq_self_eq_true _

theorem IsEnumSet.ncard_filter_of_mem {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (hsize : E.size = S.ncard) (b : Table → Bool)
    (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → g ∈ S → (b x = true ↔ Q g)) :
    {g : Equiv.Perm (Fin n) | g ∈ S ∧ Q g}.ncard = (E.filter b).size := by
  have hb' : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g →
      ((fun y => b y && memT n E y) x = true ↔ (g ∈ S ∧ Q g)) := by
    intro x g hx
    have hmem := h.memT_iff hx
    simp only [Bool.and_eq_true, hmem]
    constructor
    · rintro ⟨hbx, hgS⟩
      exact ⟨hgS, (hb x g hx hgS).1 hbx⟩
    · rintro ⟨hgS, hQ⟩
      exact ⟨(hb x g hx hgS).2 hQ, hgS⟩
  have h1 := h.ncard_filter hsize (fun y => b y && memT n E y) (fun g => g ∈ S ∧ Q g) hb'
  have hset : {g : Equiv.Perm (Fin n) | g ∈ S ∧ (g ∈ S ∧ Q g)} =
      {g : Equiv.Perm (Fin n) | g ∈ S ∧ Q g} := by
    ext g
    simp only [Set.mem_setOf_eq, and_self_left]
  have hfil : (E.filter (fun y => b y && memT n E y)).size = (E.filter b).size := by
    rw [← Array.countP_eq_size_filter, ← Array.countP_eq_size_filter]
    exact Array.countP_congr fun x hx => by simp only [memT_of_mem_array hx, Bool.and_true]
  rw [hset, hfil] at h1
  exact h1

end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
