module

public import CFSG.Certificates.Kernel.BalanceSC.Parts

public section

namespace CFSG.KC.BalanceSC

open Equiv Equiv.Perm Finset

theorem mem_insEvery_erase : ∀ {a : ℕ} {l : List ℕ}, a ∈ l → l ∈ insEvery a (l.erase a)
  | a, b :: l, h => by
    by_cases hb : b = a
    · subst hb
      rw [List.erase_cons_head]
      cases l with
      | nil => simp [insEvery]
      | cons c l => simp [insEvery]
    · rw [List.erase_cons_tail (by simpa using hb)]
      have ha : a ∈ l := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hb
        · exact h
      simp only [insEvery]
      exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨l, mem_insEvery_erase ha, rfl⟩)

theorem mem_perms : ∀ {l l' : List ℕ}, l'.Perm l → l' ∈ perms l
  | [], l', h => by
    rw [List.perm_nil] at h
    subst h
    simp [perms]
  | a :: l, l', h => by
    have ha : a ∈ l' := h.symm.subset List.mem_cons_self
    have he : (l'.erase a).Perm l := ((List.perm_cons_erase ha).symm.trans h).cons_inv
    simp only [perms, List.mem_flatMap]
    exact ⟨_, mem_perms he, mem_insEvery_erase ha⟩

theorem lookup_zip_maps (u v g : ℕ → ℕ) : ∀ (l : List ℕ), (∀ j ∈ l, v j = g (u j)) → ∀ y : ℕ,
    ((l.map u).zip (l.map v)).lookup y = if y ∈ l.map u then some (g y) else none
  | [], _, y => by simp
  | j :: l, h, y => by
    have ih := lookup_zip_maps u v g l (fun i hi => h i (List.mem_cons_of_mem _ hi)) y
    by_cases hy : y = u j
    · subst hy
      simp [List.lookup, h j List.mem_cons_self]
    · have hb : (y == u j) = false := by simpa using hy
      simp only [List.map_cons, List.zip_cons_cons, List.lookup, hb, ih, List.mem_cons, hy,
        false_or]

theorem lookup_append (l₁ l₂ : List (ℕ × ℕ)) (y : ℕ) :
    (l₁ ++ l₂).lookup y = ((l₁.lookup y).or (l₂.lookup y)) := by
  induction l₁ with
  | nil => simp
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : y = a
    · subst h
      simp [List.lookup]
    · have hb : (y == a) = false := by simpa using h
      simp only [List.cons_append, List.lookup, hb, ih]

variable {n : ℕ}

@[expose] def imgE (e : Perm (Fin n)) (i : ℕ) : ℕ := if h : i < n then (e ⟨i, h⟩ : ℕ) else i

@[expose] def imgList (e : Perm (Fin n)) : List ℕ := (List.range n).map (imgE e)

theorem imgE_fin (e : Perm (Fin n)) (z : Fin n) : imgE e z = e z := by
  simp [imgE]

theorem mem_bitsOf_fmask {s : Finset (Fin n)} {i : ℕ} :
    i ∈ bitsOf n (fmask s) ↔ ∃ z ∈ s, (z : ℕ) = i := by
  simp only [bitsOf, List.mem_filter, List.mem_range, testBit_fmask]
  constructor
  · exact fun h => h.2
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, z, hz, rfl⟩

theorem nodup_bitsOf (m : ℕ) : (bitsOf n m).Nodup := List.nodup_range.filter _

theorem exists_cycMaps {e : Perm (Fin n)} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1) {x : Fin n}
    (hx : x ∈ e.support) {b : ℕ} {rest : List ℕ} (hbr : bitsOf n (fmask (blk e x)) = b :: rest) :
    ∃ c ∈ cycMaps b rest, c.1.length = c.2.length ∧ ∀ y : ℕ,
      (c.1.zip c.2).lookup y = if y ∈ b :: rest then some (imgE e y) else none := by
  set B := blk e x with hB
  have hmemB : ∀ z : Fin n, (z : ℕ) ∈ b :: rest ↔ z ∈ B := fun z => by
    rw [← hbr, mem_bitsOf_fmask]
    exact ⟨fun ⟨z', hz', h⟩ => (Fin.ext h) ▸ hz', fun h => ⟨z, h, rfl⟩⟩
  obtain ⟨zb, hzbB, hzb⟩ : ∃ zb : Fin n, zb ∈ B ∧ (zb : ℕ) = b := by
    have : b ∈ bitsOf n (fmask B) := by rw [hbr]; exact List.mem_cons_self
    obtain ⟨z, hz, h⟩ := mem_bitsOf_fmask.1 this
    exact ⟨z, hz, h⟩
  have hzbS : zb ∈ e.support := (mem_blk.1 hzbB).mem_support_iff.1 hx
  have : Fact r.Prime := ⟨hr⟩
  have hord : orderOf e = r := orderOf_eq_prime her fun h => by
    rw [h] at hx
    simp at hx
  set u : ℕ → ℕ := fun j => ((e ^ j) zb : ℕ) with hu
  have hr1 : r = (r - 1) + 1 := (Nat.succ_pred_eq_of_pos hr.pos).symm
  set P0 := (List.range r).map u with hP0
  set I0 := (List.range r).map (fun j => u (j + 1)) with hI0
  have hu0 : u 0 = b := by simp [hu, hzb]
  have hur : u r = b := by simp [hu, her, hzb]
  set c := (List.range (r - 1)).map (fun j => u (j + 1)) with hc
  have hP0c : P0 = b :: c := by
    rw [hP0, hr1, List.range_succ_eq_map, List.map_cons, List.map_map, hu0]
    rfl
  have hI0c : I0 = c ++ [b] := by
    rw [hI0, hr1, List.range_succ, List.map_append, List.map_singleton, ← hr1, hur]
  have hmemP0 : ∀ y : ℕ, y ∈ P0 ↔ y ∈ b :: rest := by
    intro y
    rw [hP0, List.mem_map]
    constructor
    · rintro ⟨j, -, rfl⟩
      exact (hmemB _).2 (mem_blk.2 ((mem_blk.1 hzbB).trans ⟨j, by simp⟩))
    · intro hy
      have hy' : y ∈ bitsOf n (fmask B) := by rw [hbr]; exact hy
      obtain ⟨z, hz, rfl⟩ := mem_bitsOf_fmask.1 hy'
      obtain ⟨j, hj, hjz⟩ := ((mem_blk.1 hzbB).symm.trans (mem_blk.1 hz)).exists_pow_eq'
      exact ⟨j, List.mem_range.2 (hord ▸ hj), by simp [hu, hjz]⟩
  have hnd : P0.Nodup := by
    have hcard : (B.map Fin.valEmbedding) ⊆ P0.toFinset := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := mem_map.1 hy
      rw [List.mem_toFinset, hmemP0]
      exact (hmemB z).2 hz
    have h1 := card_le_card hcard
    rw [card_map, hB, card_blk hr her hx, List.card_toFinset] at h1
    have hlen : P0.length = r := by simp [hP0]
    have h2 : P0.dedup = P0 :=
      (List.dedup_sublist P0).eq_of_length_le (by rw [hlen]; exact h1)
    rw [← h2]
    exact List.nodup_dedup P0
  have hperm : c.Perm rest := by
    refine List.Perm.cons_inv (a := b) ?_
    rw [← hP0c]
    refine (List.perm_ext_iff_of_nodup hnd ?_).2 hmemP0
    rw [← hbr]
    exact nodup_bitsOf _
  refine ⟨(b :: c, c ++ [b]), List.mem_map.2 ⟨c, mem_perms hperm, rfl⟩, by simp, fun y => ?_⟩
  simp only
  rw [← hP0c, ← hI0c, hP0, hI0]
  rw [lookup_zip_maps u (fun j => u (j + 1)) (imgE e) _ (fun j _ => by
    simp only [hu, pow_succ', mul_apply, imgE_fin])]
  simp only [← hP0, hmemP0]

theorem exists_blockMaps {e : Perm (Fin n)} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1) :
    ∀ Ls : List (List ℕ), (∀ pts ∈ Ls, ∃ x ∈ e.support, pts = bitsOf n (fmask (blk e x))) →
    ∃ PI ∈ blockMaps Ls, ∀ y : ℕ,
      (PI.1.zip PI.2).lookup y = if ∃ pts ∈ Ls, y ∈ pts then some (imgE e y) else none
  | [], _ => ⟨([], []), by simp [blockMaps], fun y => by simp⟩
  | pts :: Ls, h => by
    obtain ⟨x, hx, hpts⟩ := h pts List.mem_cons_self
    obtain ⟨PI, hPI, hlook⟩ := exists_blockMaps hr her Ls fun p hp => h p (List.mem_cons_of_mem _ hp)
    cases pts with
    | nil =>
      have : (x : ℕ) ∈ bitsOf n (fmask (blk e x)) :=
        mem_bitsOf_fmask.2 ⟨x, mem_blk.2 (SameCycle.refl _ _), rfl⟩
      rw [← hpts] at this
      simp at this
    | cons b rest =>
      obtain ⟨c, hc, hlen, hclook⟩ := exists_cycMaps hr her hx hpts.symm
      refine ⟨(c.1 ++ PI.1, c.2 ++ PI.2), ?_, fun y => ?_⟩
      · simp only [blockMaps, List.mem_flatMap, List.mem_map]
        exact ⟨PI, hPI, c, hc, rfl⟩
      · simp only
        rw [List.zip_append hlen, lookup_append, hclook, hlook]
        by_cases hy : y ∈ b :: rest
        · simp only [hy, if_true, Option.some_or]
          rw [if_pos ⟨_, List.mem_cons_self, hy⟩]
        · simp only [hy, if_false, Option.none_or, List.mem_cons, exists_eq_or_imp, false_or]

theorem imgList_mem_elemsOf {e : Perm (Fin n)} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1)
    {L : List ℕ} (hL : ∀ m ∈ L, ∃ x ∈ e.support, fmask (blk e x) = m)
    (hcov : ∀ x ∈ e.support, fmask (blk e x) ∈ L) : imgList e ∈ elemsOf n L := by
  obtain ⟨PI, hPI, hlook⟩ := exists_blockMaps hr her (L.map (bitsOf n)) fun pts hp => by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hp
    obtain ⟨x, hx, rfl⟩ := hL m hm
    exact ⟨x, hx, rfl⟩
  rw [elemsOf, elemsOfPts, List.mem_map]
  refine ⟨PI, hPI, ?_⟩
  rw [imgList]
  refine List.map_congr_left fun i hi => ?_
  rw [lookImg, hlook]
  split_ifs with hP
  · rfl
  · have hin : i < n := List.mem_range.1 hi
    have hfix : e ⟨i, hin⟩ = ⟨i, hin⟩ := by
      by_contra hne
      apply hP
      have hz : (⟨i, hin⟩ : Fin n) ∈ e.support := mem_support.2 hne
      exact ⟨_, List.mem_map.2 ⟨_, hcov _ hz, rfl⟩,
        mem_bitsOf_fmask.2 ⟨_, mem_blk.2 (SameCycle.refl _ _), rfl⟩⟩
    simp [imgE, hin, hfix]

theorem imgList_mem_elemsOf_sort {e : Perm (Fin n)} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1) :
    imgList e ∈ elemsOf n (sortMasks e) := by
  refine imgList_mem_elemsOf hr her (fun m hm => ?_) (fun x hx => ?_)
  · obtain ⟨B, hB, rfl⟩ := mem_sortMasks.1 hm
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hB
    exact ⟨x, hx, rfl⟩
  · exact mem_sortMasks.2 ⟨_, mem_image_of_mem _ hx, rfl⟩

end CFSG.KC.BalanceSC
