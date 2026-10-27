module

public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Actions

public section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open scoped Pointwise

variable {n : ℕ}

@[expose] def finSet (n : ℕ) (l : List ℕ) : Set (Fin n) := {p | (p : ℕ) ∈ l}

structure PointList (n : ℕ) (l : List ℕ) : Prop where
  lt : ∀ q ∈ l, q < n
  sorted : l.Pairwise (· < ·)

theorem pointList_fixedList (x : Array ℕ) : PointList n (fixedList n x) where
  lt _ hq := List.mem_range.1 (List.mem_filter.1 hq).1
  sorted := List.pairwise_lt_range.filter _

theorem finSet_fixedList {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X) :
    finSet n (fixedList n x) = {p | X p = p} := by
  ext p
  simp only [finSet, fixedList, Set.mem_ofPred_eq, List.mem_filter, List.mem_range, beq_iff_eq]
  rw [hx p]
  exact ⟨fun h => Fin.ext h.2, fun h => ⟨p.2, by rw [h]⟩⟩

theorem PointList.eq_of_finSet_eq {l₁ l₂ : List ℕ} (h₁ : PointList n l₁) (h₂ : PointList n l₂)
    (h : finSet n l₁ = finSet n l₂) : l₁ = l₂ := by
  refine h₁.sorted.eq_of_mem_iff h₂.sorted fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · have : (⟨q, h₁.lt q hq⟩ : Fin n) ∈ finSet n l₁ := hq
    rw [h] at this
    exact this
  · have : (⟨q, h₂.lt q hq⟩ : Fin n) ∈ finSet n l₂ := hq
    rw [← h] at this
    exact this

theorem mem_imgSorted {g : Array ℕ} {l : List ℕ} {q : ℕ} :
    q ∈ Native.imgSorted g l ↔ ∃ p ∈ l, g[p]! = q := by
  rw [Native.imgSorted, (List.mergeSort_perm _ _).mem_iff, List.mem_map]

theorem PointList.img {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hg : Rep n g G) {l : List ℕ}
    (hl : PointList n l) :
    PointList n (Native.imgSorted g l) ∧ finSet n (Native.imgSorted g l) = G • finSet n l := by
  have hnd : (Native.imgSorted g l).Nodup := by
    rw [Native.imgSorted, (List.mergeSort_perm _ _).nodup_iff]
    refine hl.sorted.nodup.map_on fun a ha b hb hab => ?_
    rw [hg.apply (hl.lt a ha), hg.apply (hl.lt b hb)] at hab
    exact congrArg Fin.val (G.injective (Fin.ext hab))
  have hle : (Native.imgSorted g l).Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (l.map fun p => g[p]!)
    exact this.imp fun h => by simpa using h
  refine ⟨⟨fun q hq => ?_, (hle.and hnd).imp fun h => lt_of_le_of_ne h.1 h.2⟩, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := mem_imgSorted.1 hq
    exact hg.lt (hl.lt p hp)
  · ext q
    simp only [finSet, Set.mem_ofPred_eq, Set.mem_smul_set, mem_imgSorted, Equiv.Perm.smul_def]
    constructor
    · rintro ⟨p, hp, hpq⟩
      refine ⟨⟨p, hl.lt p hp⟩, hp, Fin.ext ?_⟩
      rw [← hpq, hg.apply (hl.lt p hp)]
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, hg p⟩

section Translates

variable {H : Subgroup (Equiv.Perm (Fin n))} {gens : Array (Array ℕ)}
  {Gs : ℕ → Equiv.Perm (Fin n)} {start : List ℕ} {sets : Array (List ℕ)} {par lab : Array ℕ}

theorem translates_spec (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (hmem : ∀ k < gens.size, Gs k ∈ H) (hstart : PointList n start)
    (hok : translatesOK gens start sets par lab = true) :
    ∀ k < sets.size, PointList n sets[k]! ∧
      ∃ g ∈ H, finSet n sets[k]! = g • finSet n start := by
  simp only [translatesOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨-, h0⟩, hall⟩ := hok
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hk' := allLt_spec hall hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hk'
    rcases hk' with rfl | ⟨⟨hp, hl⟩, he⟩
    · rw [h0]
      exact ⟨hstart, 1, H.one_mem, by rw [one_smul]⟩
    · obtain ⟨hpl, g, hg, hgs⟩ := ih _ hp (by omega)
      obtain ⟨hpl', hset⟩ := hpl.img (hrep _ hl)
      rw [he]
      refine ⟨hpl', Gs lab[k]! * g, H.mul_mem (hmem _ hl) hg, ?_⟩
      rw [hset, hgs, mul_smul]

theorem le_ncard_orbit_of_translatesOK (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (hmem : ∀ k < gens.size, Gs k ∈ H) (hstart : PointList n start)
    (hok : translatesOK gens start sets par lab = true) (hnd : sets.toList.Nodup) :
    sets.size ≤ (Set.range fun g : H => g • finSet n start).ncard := by
  have hspec := translates_spec hrep hmem hstart hok
  let f : Fin sets.size → Set (Fin n) := fun k => finSet n sets[(k : ℕ)]!
  have hinj : Function.Injective f := by
    intro i j hij
    have hl := (hspec i i.2).1.eq_of_finSet_eq (hspec j j.2).1 hij
    rw [getElem!_pos sets (i : ℕ) i.2, getElem!_pos sets (j : ℕ) j.2, ← Array.getElem_toList,
      ← Array.getElem_toList] at hl
    exact Fin.ext ((hnd.getElem_inj_iff).1 hl)
  have hsub : Set.range f ⊆ Set.range fun g : H => g • finSet n start := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨g, hg, hgs⟩ := (hspec k k.2).2
    exact ⟨⟨g, hg⟩, hgs.symm⟩
  calc sets.size = (Set.range f).ncard := by rw [Set.ncard_range_of_injective hinj, Nat.card_fin]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end Translates

end CFSG.Certificates
