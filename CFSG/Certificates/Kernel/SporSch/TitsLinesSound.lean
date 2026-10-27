module

public import Certificates.Data.Kernel.SporSch.TitsLines
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawDefs
import Mathlib.Data.Finset.Card

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

private theorem strictB_eqL (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by
  simp [Nat.blt_eq]

private theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b := by
  simp

private def LexLt (a b c d : Nat) : Prop := a < c ∨ (a = c ∧ b < d)

private theorem lexLtK_iffL {a b c d : Nat} :
    lexLtK a b c d = true ↔ LexLt a b c d := by
  unfold lexLtK LexLt
  by_cases h1 : a < c
  · rw [Nat.blt_eq.mpr h1]
    exact ⟨fun _ => Or.inl h1, fun _ => rfl⟩
  · have e1 : Nat.blt a c = false := by
      cases e : Nat.blt a c
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h1
    rw [e1]
    change Bool.rec false (Nat.blt b d) (Nat.beq a c) = true ↔ _
    by_cases h2 : a = c
    · subst h2
      rw [Nat.beq_refl]
      change Nat.blt b d = true ↔ _
      rw [Nat.blt_eq]
      omega
    · have e2 : Nat.beq a c = false := by
        cases e : Nat.beq a c
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) h2
      rw [e2]
      constructor
      · intro h
        exact absurd h Bool.false_ne_true
      · intro h
        omega

private theorem mergeSort_lt_of_nodup {l : List Nat} (h : l.Nodup) :
    (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· < ·) := by
  have hs := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) l
  have hn : (l.mergeSort fun a b => decide (a ≤ b)).Nodup := (List.mergeSort_perm l _).nodup_iff.2 h
  refine (hs.and hn).imp ?_
  intro a b ⟨h1, h2⟩
  simp at h1
  omega

theorem orderK_sound {V SO SOI w : Nat} {f : Nat → Nat} (h : orderK V f SO SOI w = true) :
    (((List.range V).map f).mergeSort fun a b => decide (a ≤ b)).Pairwise (· < ·) := by
  unfold orderK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hP : ∀ i < V, pg w (mask w) SO i < V ∧ pg w (mask w) SOI (pg w (mask w) SO i) = i := by
    intro i hi
    have := allN_spec h1 i hi
    rw [strictB_eqL] at this
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 this
    exact ⟨blt_iff.1 a, beq_iff.1 b⟩
  have hM : ∀ i j, i < j → j < V → f (pg w (mask w) SO i) < f (pg w (mask w) SO j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have := blt_iff.1 (allN_spec h2 j (by simp; omega))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
      · exact lt_trans (ih hij (by omega)) this
      · exact this
  have hinj : ∀ i < V, ∀ j < V, pg w (mask w) SO i = pg w (mask w) SO j → i = j := by
    intro i hi j hj e
    have a := (hP i hi).2
    have b := (hP j hj).2
    rw [e] at a
    rw [a] at b
    exact b
  have hsurj : ∀ v < V, ∃ i < V, pg w (mask w) SO i = v := by
    intro v hv
    have himg : (Finset.range V).image (pg w (mask w) SO) = Finset.range V := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
        obtain ⟨i, hi, rfl⟩ := hx
        exact (hP i hi).1
      · rw [Finset.card_image_of_injOn (fun i hi j hj e => hinj i (by simpa using hi)
          j (by simpa using hj) e)]
    have : v ∈ (Finset.range V).image (pg w (mask w) SO) := by rw [himg]; simpa using hv
    simp only [Finset.mem_image, Finset.mem_range] at this
    exact this
  apply mergeSort_lt_of_nodup
  rw [List.nodup_iff_injective_get]
  intro ⟨a, ha⟩ ⟨b, hb⟩ e
  simp only [List.length_map, List.length_range] at ha hb
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at e
  obtain ⟨i, hi, rfl⟩ := hsurj a ha
  obtain ⟨j, hj, rfl⟩ := hsurj b hb
  have : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · exact absurd e (ne_of_lt (hM i j h hj))
    · exact h
    · exact absurd e (ne_of_gt (hM j i h hi))
  subst this
  rfl


private theorem foldl_buckets (κ : Array Nat) (V : Nat) (L : List Nat) :
    (L.foldl (fun acc j => acc.modify κ[j]! fun l => l ++ [j]) (Array.replicate V [])).size = V ∧
    ∀ v < V, (L.foldl (fun acc j => acc.modify κ[j]! fun l => l ++ [j])
      (Array.replicate V []))[v]! = L.filter (fun j => κ[j]! = v) := by
  induction L using List.reverseRecOn with
  | nil =>
    refine ⟨by simp, fun v hv => ?_⟩
    simp [getElem!_pos (Array.replicate V ([] : List Nat)) v (by simpa using hv)]
  | append_singleton L j ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [h1], fun v hv => ?_⟩
    have hs : v < ((L.foldl (fun acc j => acc.modify κ[j]! fun l => l ++ [j])
        (Array.replicate V [])).modify κ[j]! fun l => l ++ [j]).size := by simp [h1, hv]
    rw [getElem!_pos _ v hs, Array.getElem_modify, List.filter_append]
    have := h2 v hv
    rw [getElem!_pos _ v (by rw [h1]; exact hv)] at this
    rw [this]
    by_cases e : κ[j]! = v
    · simp [e]
    · simp [e]

private theorem pair_sublist_of_lt : ∀ {l : List Nat}, l.Pairwise (· < ·) → ∀ {a b : Nat},
    a ∈ l → b ∈ l → a < b → List.Sublist [a, b] l
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: t, hl, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · omega
      · exact List.Sublist.cons_cons _ (List.singleton_sublist.2 hb')
    · have hxa := hl.1 a ha'
      rcases List.mem_cons.1 hb with rfl | hb'
      · omega
      · exact List.Sublist.cons _ (pair_sublist_of_lt hl.2 ha' hb' hab)

private theorem eq_of_pair_sublists : ∀ {l : List Nat}, l.Nodup → ∀ {a b : Nat},
    List.Sublist [a, b] l → List.Sublist [b, a] l → a = b
  | [], _, _, _, h, _ => by simp at h
  | x :: t, hl, a, b, h1, h2 => by
    rw [List.nodup_cons] at hl
    rw [List.sublist_cons_iff] at h1 h2
    rcases h1 with h1 | ⟨r, hr, h1⟩ <;> rcases h2 with h2 | ⟨r', hr', h2⟩
    · exact eq_of_pair_sublists hl.2 h1 h2
    · simp only [List.cons.injEq] at hr'
      obtain ⟨rfl, rfl⟩ := hr'
      exact absurd (h1.subset (List.mem_cons_of_mem _ List.mem_cons_self)) hl.1
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact absurd (h2.subset (List.mem_cons_of_mem _ List.mem_cons_self)) hl.1
    · simp only [List.cons.injEq] at hr hr'
      rw [hr.1, hr'.1]

private theorem stable_lex {l : List Nat} (hl : l.Pairwise (· < ·)) (β : Nat → Nat) :
    (l.mergeSort fun a b => decide (β a ≤ β b)).Pairwise
      (fun a b => β a < β b ∨ (β a = β b ∧ a ≤ b)) := by
  have tr : ∀ a b c : Nat, decide (β a ≤ β b) = true → decide (β b ≤ β c) = true →
      decide (β a ≤ β c) = true := by
    intro a b c h1 h2
    simp only [decide_eq_true_eq] at *
    omega
  have tot : ∀ a b : Nat, (decide (β a ≤ β b) || decide (β b ≤ β a)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  have s := List.pairwise_mergeSort tr tot l
  have hn : (l.mergeSort fun a b => decide (β a ≤ β b)).Nodup :=
    (List.mergeSort_perm l _).nodup_iff.2 (hl.imp fun h => Nat.ne_of_lt h)
  rw [List.pairwise_iff_forall_sublist]
  intro a b hab
  have h1 : β a ≤ β b := by
    have := List.pairwise_iff_forall_sublist.1 s hab
    simpa using this
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    by_contra hba
    have ha : a ∈ l := (List.mergeSort_perm l _).subset (hab.subset List.mem_cons_self)
    have hb : b ∈ l := (List.mergeSort_perm l _).subset
      (hab.subset (List.mem_cons_of_mem _ List.mem_cons_self))
    have hs := List.pair_sublist_mergeSort tr tot (decide_eq_true (Nat.le_of_eq h.symm))
      (pair_sublist_of_lt hl hb ha (by omega))
    have := eq_of_pair_sublists hn hab hs
    omega

theorem lineFlagsK_sound {N V wk K wb B wl LF : Nat} (h : lineFlagsK N V wk K wb B wl LF = true) :
    lineFlags N V (unpack N wk K) (unpack N wb B) = unpack N wl LF := by
  unfold lineFlagsK at h
  obtain ⟨hN, h⟩ := (bAnd_iff _ _).1 h
  have hN : N = 3 * V := beq_iff.1 hN
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = unpack N wk K := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β, β = unpack N wb B := ⟨_, rfl⟩
  rw [← hκd, ← hβd]
  have hκ : ∀ j < N, κ[j]! = pg wk (mask wk) K j := fun j hj => by
    rw [hκd, unpack]
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  have hβ : ∀ j < N, β[j]! = pg wb (mask wb) B j := fun j hj => by
    rw [hβd, unpack]
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  have hL : ∀ v < V, (∀ k < 3, pg wl (mask wl) LF (3 * v + k) < N ∧
      κ[pg wl (mask wl) LF (3 * v + k)]! = v) ∧
      LexLt β[pg wl (mask wl) LF (3 * v)]! (pg wl (mask wl) LF (3 * v))
        β[pg wl (mask wl) LF (3 * v + 1)]! (pg wl (mask wl) LF (3 * v + 1)) ∧
      LexLt β[pg wl (mask wl) LF (3 * v + 1)]! (pg wl (mask wl) LF (3 * v + 1))
        β[pg wl (mask wl) LF (3 * v + 2)]! (pg wl (mask wl) LF (3 * v + 2)) := by
    intro v hv
    have := allN_spec h v hv
    simp only [strictB_eqL, bAnd_iff, blt_iff, beq_iff, lexLtK_iffL] at this
    obtain ⟨a0, a1, a2, k0, k1, k2, l1, l2⟩ := this
    have a0' : pg wl (mask wl) LF (3 * v) < N := a0
    have a1' : pg wl (mask wl) LF (3 * v + 1) < N := a1
    have a2' : pg wl (mask wl) LF (3 * v + 2) < N := a2
    have k0' : pg wk (mask wk) K (pg wl (mask wl) LF (3 * v)) = v := k0
    have k1' : pg wk (mask wk) K (pg wl (mask wl) LF (3 * v + 1)) = v := k1
    have k2' : pg wk (mask wk) K (pg wl (mask wl) LF (3 * v + 2)) = v := k2
    have l1' : LexLt (pg wb (mask wb) B (pg wl (mask wl) LF (3 * v))) (pg wl (mask wl) LF (3 * v))
        (pg wb (mask wb) B (pg wl (mask wl) LF (3 * v + 1))) (pg wl (mask wl) LF (3 * v + 1)) := l1
    have l2' : LexLt (pg wb (mask wb) B (pg wl (mask wl) LF (3 * v + 1)))
        (pg wl (mask wl) LF (3 * v + 1))
        (pg wb (mask wb) B (pg wl (mask wl) LF (3 * v + 2))) (pg wl (mask wl) LF (3 * v + 2)) := l2
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · interval_cases k
      · exact ⟨a0', (hκ _ a0').trans k0'⟩
      · exact ⟨a1', (hκ _ a1').trans k1'⟩
      · exact ⟨a2', (hκ _ a2').trans k2'⟩
    · rw [hβ _ a0', hβ _ a1']
      exact l1'
    · rw [hβ _ a1', hβ _ a2']
      exact l2'
  let R : Nat → Nat → Prop := fun a b => β[a]! < β[b]! ∨ (β[a]! = β[b]! ∧ a ≤ b)
  let row := fun v => [pg wl (mask wl) LF (3 * v), pg wl (mask wl) LF (3 * v + 1), pg wl (mask wl) LF (3 * v + 2)]
  have hrow : ∀ v < V, (row v).Pairwise R ∧ (row v).Nodup := by
    intro v hv
    obtain ⟨-, l1, l2⟩ := hL v hv
    simp only [LexLt] at l1 l2
    have r01 : R (pg wl (mask wl) LF (3 * v)) (pg wl (mask wl) LF (3 * v + 1)) := by
      simp only [R]
      omega
    have r12 : R (pg wl (mask wl) LF (3 * v + 1)) (pg wl (mask wl) LF (3 * v + 2)) := by
      simp only [R]
      omega
    have r02 : R (pg wl (mask wl) LF (3 * v)) (pg wl (mask wl) LF (3 * v + 2)) := by
      simp only [R]
      omega
    have n01 : pg wl (mask wl) LF (3 * v) ≠ pg wl (mask wl) LF (3 * v + 1) := by
      intro e
      rw [e] at l1
      omega
    have n12 : pg wl (mask wl) LF (3 * v + 1) ≠ pg wl (mask wl) LF (3 * v + 2) := by
      intro e
      rw [e] at l2
      omega
    have n02 : pg wl (mask wl) LF (3 * v) ≠ pg wl (mask wl) LF (3 * v + 2) := by
      intro e
      rw [e] at l1
      omega
    refine ⟨?_, ?_⟩
    · simp only [row, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
        List.Pairwise.nil, or_false]
      refine ⟨fun b hb => ?_, fun b hb => ?_, fun _ h => h.elim, trivial⟩
      · rcases hb with rfl | rfl
        · exact r01
        · exact r02
      · rw [hb]
        exact r12
    · simp only [row, List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, or_false, not_or]
      exact ⟨⟨n01, n02⟩, n12, not_false, trivial⟩
  have hFv : ∀ t < N, pg wl (mask wl) LF t < N ∧ κ[pg wl (mask wl) LF t]! = t / 3 := by
    intro t ht
    have := (hL (t / 3) (by omega)).1 (t % 3) (Nat.mod_lt _ (by omega))
    rw [Nat.div_add_mod] at this
    exact this
  have hinj : ∀ t < N, ∀ t' < N, pg wl (mask wl) LF t = pg wl (mask wl) LF t' → t = t' := by
    intro t ht t' ht' e
    have e3 : t / 3 = t' / 3 := by
      rw [← (hFv t ht).2, ← (hFv t' ht').2, e]
    have hn := (hrow (t / 3) (by omega)).2
    have ht3 := Nat.div_add_mod t 3
    have ht3' := Nat.div_add_mod t' 3
    have hm := Nat.mod_lt t (show 3 > 0 by omega)
    have hm' := Nat.mod_lt t' (show 3 > 0 by omega)
    simp only [row, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hn
    have key : t % 3 = t' % 3 := by
      have ef : pg wl (mask wl) LF (3 * (t / 3) + t % 3) = pg wl (mask wl) LF (3 * (t / 3) + t' % 3) := by
        rw [ht3, e3, ht3', e]
      interval_cases ht : t % 3 <;> interval_cases ht' : t' % 3 <;> simp_all
    omega
  have hsurj : ∀ j < N, ∃ t < N, pg wl (mask wl) LF t = j := by
    intro j hj
    have himg : (Finset.range N).image (pg wl (mask wl) LF) = Finset.range N := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
        obtain ⟨i, hi, rfl⟩ := hx
        exact (hFv i hi).1
      · rw [Finset.card_image_of_injOn (fun i hi j hj e => hinj i (by simpa using hi)
          j (by simpa using hj) e)]
    have : j ∈ (Finset.range N).image (pg wl (mask wl) LF) := by
      rw [himg]
      simpa using hj
    simpa using this
  have hbucket : ∀ v < V, ((List.range N).filter fun j => κ[j]! = v).mergeSort
      (fun a b => decide (β[a]! ≤ β[b]!)) = row v := by
    intro v hv
    have hsort := stable_lex (l := (List.range N).filter fun j => κ[j]! = v)
      ((List.pairwise_lt_range).filter _) (fun a => β[a]!)
    apply List.Perm.eq_of_pairwise (le := R) _ hsort (hrow v hv).1
    · apply (List.perm_ext_iff_of_nodup ((List.mergeSort_perm _ _).nodup_iff.2
        ((List.nodup_range).filter _)) (hrow v hv).2).2
      intro j
      rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filter, List.mem_range]
      simp only [decide_eq_true_eq, row, List.mem_cons, List.not_mem_nil,
        or_false]
      constructor
      · rintro ⟨hj, hk⟩
        obtain ⟨t, ht, rfl⟩ := hsurj j hj
        rw [(hFv t ht).2] at hk
        have := Nat.div_add_mod t 3
        have := Nat.mod_lt t (show 3 > 0 by omega)
        subst hk
        interval_cases ht' : t % 3
        · exact Or.inl (by rw [← Nat.add_zero (3 * (t / 3))]; congr 1; omega)
        · exact Or.inr (Or.inl (by congr 1; omega))
        · exact Or.inr (Or.inr (by congr 1; omega))
      · rintro (rfl | rfl | rfl)
        · exact ⟨((hL v hv).1 0 (by omega)).1, ((hL v hv).1 0 (by omega)).2⟩
        · exact ((hL v hv).1 1 (by omega))
        · exact ((hL v hv).1 2 (by omega))
    · intro a b _ _ h1 h2
      simp only [R] at h1 h2
      omega
  have hfl : ∀ M, M ≤ V → ((List.range M).map row).flatten = (List.range (3 * M)).map (pg wl (mask wl) LF) := by
    intro M hM
    induction M with
    | zero => rfl
    | succ M ih =>
      have e3 : 3 * (M + 1) = 3 * M + 1 + 1 + 1 := by omega
      rw [List.range_succ, List.map_append, List.flatten_append, ih (by omega), e3,
        List.range_succ, List.range_succ, List.range_succ]
      simp [row]
  obtain ⟨hsz, hget⟩ := foldl_buckets κ V (List.range N)
  unfold lineFlags
  apply Array.ext'
  rw [List.toList_toArray]
  have hl : ((List.range N).foldl (fun acc j => acc.modify κ[j]! fun l => l ++ [j])
      (Array.replicate V [])).toList.map
        (fun l => l.mergeSort fun a b => decide (β[a]! ≤ β[b]!)) = (List.range V).map row := by
    apply List.ext_getElem
    · simp [hsz]
    · intro i h1 h2
      simp only [List.length_map, Array.length_toList] at h1
      rw [List.getElem_map, List.getElem_map, List.getElem_range, Array.getElem_toList,
        ← hbucket i (by rw [hsz] at h1; exact h1)]
      have := hget i (by rw [hsz] at h1; exact h1)
      rw [getElem!_pos _ i h1] at this
      rw [this]
  rw [hl, hfl V le_rfl, ← hN]
  apply List.ext_getElem
  · simp [unpack]
  · intro i h1 h2
    simp [unpack]

end CFSG.KS.SporSch

end
