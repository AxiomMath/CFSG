module

public import CFSG.Sporadic.Schreier.ClassSpec
public import CFSG.Sporadic.SmallOddCore.GroupFacts
import CFSG.Certificates.Kernel.Spor.RawOrbBfs
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.SporSch.ClsSpec

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore

variable {n : ℕ}

theorem foldr_digits_inj (f f' : ℕ → ℕ) (n : ℕ) :
    ∀ s len, (∀ i, s ≤ i → i < s + len → f i < n ∧ f' i < n) →
      (List.range' s len).foldr (fun i acc => f i + n * acc) 0 =
        (List.range' s len).foldr (fun i acc => f' i + n * acc) 0 →
      ∀ i, s ≤ i → i < s + len → f i = f' i
  | _, 0, _, _, _, h1, h2 => absurd h2 (by omega)
  | s, len + 1, hlt, he, i, h1, h2 => by
    simp only [List.range'_succ, List.foldr_cons] at he
    have hs := hlt s le_rfl (by omega)
    have e1 : f s = f' s := by
      have := congrArg (· % n) he
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs.1, Nat.mod_eq_of_lt hs.2] at this
      exact this
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact e1
    · rw [e1] at he
      have hn : 0 < n := by omega
      have e2 := Nat.eq_of_mul_eq_mul_left hn (Nat.add_left_cancel he)
      exact foldr_digits_inj f f' n (s + 1) len (fun j hj1 hj2 => hlt j (by omega) (by omega)) e2 i
        (by omega) (by omega)

theorem keyOf_inj {g g' : Equiv.Perm (Fin n)} (h : keyOf n g = keyOf n g') : g = g' := by
  unfold keyOf at h
  rw [List.range_eq_range'] at h
  have := foldr_digits_inj (idx n g) (idx n g') n 0 n
    (fun i _ hi => ⟨idx_lt g (by omega), idx_lt g' (by omega)⟩) h
  apply Equiv.ext
  intro x
  apply Fin.ext
  have e := this x.val (Nat.zero_le _) (by simp)
  rw [idx_of_lt _ x.2, idx_of_lt _ x.2] at e
  exact e

theorem eq_of_key {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T h)
    (e : key n S = key n T) : g = h := by
  rw [key_eq_keyOf hS, key_eq_keyOf hT] at e
  exact keyOf_inj e

theorem conj_closed {M : Type*} [Group M] [Finite M] {gs : Set M} {S : Set M}
    (hS : ∀ g ∈ gs, ∀ z ∈ S, g * z * g⁻¹ ∈ S) :
    ∀ h ∈ Subgroup.closure gs, ∀ z ∈ S, h * z * h⁻¹ ∈ S := by
  intro h hh
  have hmul : ∀ a b : M, (∀ z ∈ S, a * z * a⁻¹ ∈ S) → (∀ z ∈ S, b * z * b⁻¹ ∈ S) →
      ∀ z ∈ S, (a * b) * z * (a * b)⁻¹ ∈ S := fun a b ha hb z hz => by
    have := ha _ (hb z hz)
    simpa [mul_assoc] using this
  induction hh using Subgroup.closure_induction with
  | mem g hg => exact hS g hg
  | one => intro z hz; simp [hz]
  | mul a b _ _ ha hb => exact hmul a b ha hb
  | inv a _ ha =>
    have hpow : ∀ k : ℕ, ∀ z ∈ S, a ^ k * z * (a ^ k)⁻¹ ∈ S := by
      intro k
      induction k with
      | zero => intro z hz; simpa using hz
      | succ k ih => rw [pow_succ]; exact hmul _ _ ih ha
    have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
    rw [hinv]
    exact hpow _

theorem conj_mem_conjClass {M : Type*} [Group M] {K : Subgroup M} {g y z : M} (hg : g ∈ K)
    (hz : z ∈ conjClass K y) : g * z * g⁻¹ ∈ conjClass K y := by
  obtain ⟨c, hc, rfl⟩ := hz
  exact ⟨g * c, K.mul_mem hg hc, by group⟩

theorem push_get_lt {α : Type} [Inhabited α] {xs : Array α} {x : α} {i : ℕ}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i h, Array.getElem_push_lt h]

theorem push_get_eq {α : Type} [Inhabited α] {xs : Array α} {x : α} :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by simp)]
  exact Array.getElem_push_eq

theorem tblEq_self (S : Table) : tblEq n S S = true := tblEq_iff.2 fun _ _ => rfl

abbrev CState := Std.HashSet ℕ × Array Table × Array ℕ × Array ℕ

structure CInv (n : ℕ) (gens gensInv : Array Table) (T : Table) (C : Set (Equiv.Perm (Fin n)))
    (st : CState) : Prop where
  par_size : st.2.2.1.size = st.2.1.size
  lab_size : st.2.2.2.size = st.2.1.size
  pos : 0 < st.2.1.size
  first : st.2.1[0]! = T
  tree : ∀ k, 0 < k → k < st.2.1.size → st.2.2.1[k]! < k ∧ st.2.2.2[k]! < gens.size ∧
    st.2.1[k]! = conjT n gens[st.2.2.2[k]!]! gensInv[st.2.2.2[k]!]! st.2.1[st.2.2.1[k]!]!
  seen : ∀ kk, st.1.contains kk = true ↔ ∃ k < st.2.1.size, key n st.2.1[k]! = kk
  rep : ∀ k < st.2.1.size, ∃ z ∈ C, Rep n st.2.1[k]! z
  dist : ∀ k < st.2.1.size, ∀ k' < st.2.1.size, key n st.2.1[k]! = key n st.2.1[k']! → k = k'

@[expose] def Prog (n : ℕ) (gens gensInv : Array Table) (h l₀ : ℕ) (st : CState) : Prop :=
  ∀ k < st.2.1.size, ∀ l < gens.size, (k < h ∨ (k = h ∧ l < l₀)) →
    st.1.contains (key n (conjT n gens[l]! gensInv[l]! st.2.1[k]!)) = true

section Search

variable {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
  (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹)
  {T : Table} {y : Equiv.Perm (Fin n)}
include hg

abbrev genK (gens : Array Table) (gg : ℕ → Equiv.Perm (Fin n)) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ l < gens.size, gg l = g}

omit hg in
theorem gg_mem {l : ℕ} (hl : l < gens.size) : gg l ∈ genK gens gg :=
  Subgroup.subset_closure ⟨l, hl, rfl⟩

theorem inner_step {st : CState} {h l : ℕ} (hl : l < gens.size)
    (hI : CInv n gens gensInv T (conjClass (genK gens gg) y) st)
    (hP : Prog n gens gensInv h l st) (hh : h < st.2.1.size) :
    let z := conjT n gens[l]! gensInv[l]! st.2.1[h]!
    let st' : CState := if (!st.1.contains (key n z)) = true then
        (st.1.insert (key n z), st.2.1.push z, st.2.2.1.push h, st.2.2.2.push l) else st
    CInv n gens gensInv T (conjClass (genK gens gg) y) st' ∧ Prog n gens gensInv h (l + 1) st' ∧
      h < st'.2.1.size ∧ st'.2.1[h]! = st.2.1[h]! := by
  intro z st'
  by_cases hc : st.1.contains (key n z) = true
  · have : st' = st := by simp [st', hc]
    rw [this]
    refine ⟨hI, fun k hk l' hl' hkl => ?_, hh, rfl⟩
    rcases hkl with h1 | ⟨rfl, h2⟩
    · exact hP k hk l' hl' (Or.inl h1)
    · rcases Nat.lt_or_ge l' l with h3 | h3
      · exact hP k hk l' hl' (Or.inr ⟨rfl, h3⟩)
      · have : l' = l := by omega
        subst this
        exact hc
  · have hst' : st' = (st.1.insert (key n z), st.2.1.push z, st.2.2.1.push h, st.2.2.2.push l) := by
      simp [st', hc]
    rw [hst']
    obtain ⟨hps, hls, hpos, hfirst, htree, hseen, hrep, hdist⟩ := hI
    have hsz : (st.2.1.push z).size = st.2.1.size + 1 := Array.size_push _
    have hget : ∀ k < st.2.1.size, (st.2.1.push z)[k]! = st.2.1[k]! := fun k hk => push_get_lt hk
    refine ⟨⟨by simp [hps], by simp [hls], by simp, ?_, ?_, ?_, ?_, ?_⟩, ?_, by simp; omega,
      hget h hh⟩
    · rw [hget 0 hpos, hfirst]
    · intro k hk0 hk
      simp only [Array.size_push] at hk ⊢
      rcases Nat.lt_or_ge k st.2.1.size with hk1 | hk1
      · rw [push_get_lt (by omega), push_get_lt (by omega), hget k hk1]
        obtain ⟨a, b, c⟩ := htree k hk0 hk1
        refine ⟨a, b, ?_⟩
        rw [hget _ (by omega)]
        exact c
      · have hk2 : k = st.2.1.size := by omega
        subst hk2
        have e1 : (st.2.2.1.push h)[st.2.1.size]! = h := by rw [← hps]; exact push_get_eq
        have e2 : (st.2.2.2.push l)[st.2.1.size]! = l := by rw [← hls]; exact push_get_eq
        rw [e1, e2, push_get_eq, hget h hh]
        exact ⟨hh, hl, rfl⟩
    · intro kk
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hseen kk]
      constructor
      · rintro (e | ⟨k, hk, e⟩)
        · exact ⟨st.2.1.size, by simp, by rw [push_get_eq]; exact e⟩
        · exact ⟨k, by simp; omega, by rw [hget k hk]; exact e⟩
      · rintro ⟨k, hk, e⟩
        simp only [Array.size_push] at hk
        rcases Nat.lt_or_ge k st.2.1.size with hk1 | hk1
        · exact Or.inr ⟨k, hk1, by rw [← hget k hk1]; exact e⟩
        · have : k = st.2.1.size := by omega
          subst this
          rw [push_get_eq] at e
          exact Or.inl e
    · intro k hk
      simp only [Array.size_push] at hk
      rcases Nat.lt_or_ge k st.2.1.size with hk1 | hk1
      · rw [hget k hk1]
        exact hrep k hk1
      · have : k = st.2.1.size := by omega
        subst this
        rw [push_get_eq]
        obtain ⟨w, hw, hwr⟩ := hrep h hh
        exact ⟨gg l * w * (gg l)⁻¹, conj_mem_conjClass (gg_mem hl) hw,
          rep_conjT (hg l hl).1 (hg l hl).2 hwr⟩
    · intro k hk k' hk' e
      simp only [Array.size_push] at hk hk'
      have hnot : ∀ k < st.2.1.size, key n st.2.1[k]! ≠ key n z := fun k hk e' =>
        hc ((hseen _).2 ⟨k, hk, e'⟩)
      rcases Nat.lt_or_ge k st.2.1.size with hk1 | hk1 <;>
        rcases Nat.lt_or_ge k' st.2.1.size with hk1' | hk1'
      · rw [hget k hk1, hget k' hk1'] at e
        exact hdist k hk1 k' hk1' e
      · have : k' = st.2.1.size := by omega
        subst this
        rw [hget k hk1, push_get_eq] at e
        exact absurd e (hnot k hk1)
      · have : k = st.2.1.size := by omega
        subst this
        rw [hget k' hk1', push_get_eq] at e
        exact absurd e.symm (hnot k' hk1')
      · omega
    · intro k hk l' hl' hkl
      simp only [Array.size_push] at hk
      rw [Std.HashSet.contains_insert, Bool.or_eq_true]
      rcases Nat.lt_or_ge k st.2.1.size with hk1 | hk1
      · rw [hget k hk1]
        rcases hkl with h1 | ⟨rfl, h2⟩
        · exact Or.inr (hP k hk1 l' hl' (Or.inl h1))
        · rcases Nat.lt_or_ge l' l with h3 | h3
          · exact Or.inr (hP k hk1 l' hl' (Or.inr ⟨rfl, h3⟩))
          · have : l' = l := by omega
            subst this
            exact Or.inl (beq_self_eq_true _)
      · rcases hkl with h1 | ⟨h1, -⟩ <;> omega

omit hg in
theorem size_le {st : CState} (hI : CInv n gens gensInv T (conjClass (genK gens gg) y) st) :
    st.2.1.size ≤ (conjClass (genK gens gg) y).ncard := by
  classical
  set f : ℕ → Equiv.Perm (Fin n) := fun k =>
    if hk : k < st.2.1.size then Classical.choose (hI.rep k hk) else 1
  have hf : ∀ k (hk : k < st.2.1.size), f k ∈ conjClass (genK gens gg) y ∧ Rep n st.2.1[k]! (f k) :=
    fun k hk => by
      simp only [f, hk, ↓reduceDIte]
      exact Classical.choose_spec (hI.rep k hk)
  have hinj : Set.InjOn f ↑(Finset.range st.2.1.size) := by
    intro k hk k' hk' e
    have hk1 : k < st.2.1.size := by simpa using hk
    have hk2 : k' < st.2.1.size := by simpa using hk'
    refine hI.dist k hk1 k' hk2 ?_
    rw [key_eq_keyOf (hf k hk1).2, key_eq_keyOf (hf k' hk2).2, e]
  have hsub : ↑((Finset.range st.2.1.size).image f) ⊆ conjClass (genK gens gg) y := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
    exact (hf k (by simpa using hk)).1
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_range] at this

omit hg in
theorem init_inv (hT : Rep n T y) :
    CInv n gens gensInv T (conjClass (genK gens gg) y)
      ((∅ : Std.HashSet ℕ).insert (key n T), #[T], #[0], #[0]) ∧
    Prog n gens gensInv 0 0 ((∅ : Std.HashSet ℕ).insert (key n T), #[T], #[0], #[0]) := by
  refine ⟨⟨rfl, rfl, by simp, rfl, fun k hk0 hk => by simp at hk; omega, fun kk => ?_,
    fun k hk => ?_, fun k hk k' hk' _ => by simp at hk hk'; omega⟩, fun k _ l _ hkl => by omega⟩
  · rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq]
    constructor
    · intro e
      exact ⟨0, by simp, by simpa using e⟩
    · rintro ⟨k, hk, e⟩
      have : k = 0 := by simpa using hk
      subst this
      simpa using e
  · have : k = 0 := by simpa using hk
    subst this
    exact ⟨y, self_mem_conjClass _ _, by simpa using hT⟩

theorem final_of {st : CState} (hT : Rep n T y)
    (hI : CInv n gens gensInv T (conjClass (genK gens gg) y) st)
    (hP : Prog n gens gensInv st.2.1.size 0 st) :
    conjTreeOK n gens gensInv T st.2.1 st.2.2.1 st.2.2.2 = true ∧
      (st.2.1.toList.map (key n)).Nodup ∧
      (∀ t ∈ st.2.1.toList, ∃ z ∈ conjClass (genK gens gg) y, Rep n t z) ∧
      (∀ z ∈ conjClass (genK gens gg) y, ∃ t ∈ st.2.1.toList, Rep n t z) := by
  have hmem : ∀ t ∈ st.2.1.toList, ∃ k < st.2.1.size, st.2.1[k]! = t := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    simp only [Array.length_toList] at hk
    exact ⟨k, hk, by rw [getElem!_pos _ k hk]; simp⟩
  have hin : ∀ k < st.2.1.size, st.2.1[k]! ∈ st.2.1.toList := fun k hk => by
    rw [getElem!_pos _ k hk]
    exact Array.getElem_mem_toList hk
  refine ⟨?_, ?_, fun t ht => ?_, ?_⟩
  · unfold conjTreeOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hI.pos, by rw [hI.first]; exact tblEq_self T⟩, allIn_eq_true.2 fun k hk1 hk2 => ?_⟩
    obtain ⟨a, b, c⟩ := hI.tree k hk1 hk2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨a, b⟩, by rw [← c]; exact tblEq_self _⟩
  · rw [List.nodup_iff_injective_get]
    intro ⟨k, hk⟩ ⟨k', hk'⟩ e
    simp only [List.length_map, Array.length_toList] at hk hk'
    simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList] at e
    rw [← getElem!_pos st.2.1 k hk, ← getElem!_pos st.2.1 k' hk'] at e
    exact Fin.ext (hI.dist k hk k' hk' e)
  · obtain ⟨k, hk, rfl⟩ := hmem t ht
    exact hI.rep k hk
  · set S : Set (Equiv.Perm (Fin n)) := {z | ∃ t ∈ st.2.1.toList, Rep n t z}
    have hcl : ∀ g ∈ {g | ∃ l < gens.size, gg l = g}, ∀ z ∈ S, g * z * g⁻¹ ∈ S := by
      rintro g ⟨l, hl, rfl⟩ z ⟨t, ht, htz⟩
      obtain ⟨k, hk, rfl⟩ := hmem t ht
      have hc := hP k hk l hl (Or.inl hk)
      obtain ⟨k', hk', e⟩ := (hI.seen _).1 hc
      obtain ⟨z', -, hz'⟩ := hI.rep k' hk'
      have hR := rep_conjT (hg l hl).1 (hg l hl).2 htz
      rw [eq_of_key hR hz' e.symm]
      exact ⟨_, hin k' hk', hz'⟩
    have hy : y ∈ S := ⟨T, by rw [← hI.first]; exact hin 0 hI.pos, hT⟩
    rintro z ⟨h, hh, rfl⟩
    exact conj_closed hcl h hh y hy

theorem conjClosure_spec (hT : Rep n T y) {cap : ℕ}
    (hcap : (conjClass (genK gens gg) y).ncard ≤ cap) :
    conjTreeOK n gens gensInv T (conjClosure n gens gensInv T cap).1
        (conjClosure n gens gensInv T cap).2.1 (conjClosure n gens gensInv T cap).2.2 = true ∧
      ((conjClosure n gens gensInv T cap).1.toList.map (key n)).Nodup ∧
      (∀ t ∈ (conjClosure n gens gensInv T cap).1.toList,
        ∃ z ∈ conjClass (genK gens gg) y, Rep n t z) ∧
      (∀ z ∈ conjClass (genK gens gg) y,
        ∃ t ∈ (conjClosure n gens gensInv T cap).1.toList, Rep n t z) := by
  set C := conjClass (genK gens gg) y
  unfold conjClosure
  simp only [Id.run_bind, Id.run_pure]
  refine (fun st (hst : CInv n gens gensInv T C st ∧ Prog n gens gensInv st.2.1.size 0 st) =>
    final_of hg hT hst.1 hst.2) _ (CFSG.KS.Raw.Orb.forIn_range_idx cap _ _
      (fun a st => CInv n gens gensInv T C st ∧ Prog n gens gensInv a 0 st)
      (fun st => CInv n gens gensInv T C st ∧ Prog n gens gensInv st.2.1.size 0 st)
      (init_inv (gens := gens) (gensInv := gensInv) (gg := gg) hT) ?_ ?_)
  · intro a _ st ⟨hI, hP⟩
    split
    · rename_i ha
      simp only [Id.run_bind]
      refine CFSG.KS.Raw.Orb.forIn_range_idx gens.size _ _
        (fun l s => CInv n gens gensInv T C s ∧ Prog n gens gensInv a l s ∧ a < s.2.1.size ∧
          s.2.1[a]! = st.2.1[a]!)
        (fun s => CInv n gens gensInv T C s ∧ Prog n gens gensInv (a + 1) 0 s)
        ⟨hI, hP, ha, rfl⟩ ?_ (fun s hs => ⟨hs.1, fun k hk l hl hkl => hs.2.1 k hk l hl (by
          rcases hkl with h1 | ⟨-, h3⟩
          · rcases Nat.lt_or_ge k a with h2 | h2
            · exact Or.inl h2
            · exact Or.inr ⟨by omega, hl⟩
          · exact absurd h3 (Nat.not_lt_zero _))⟩)
      intro l hl s ⟨hI', hP', ha', he⟩
      have H := inner_step hg hl hI' hP' ha'
      simp only at H
      rw [he] at H
      split
      · rename_i hc
        simp only [hc, ↓reduceIte] at H
        exact H
      · rename_i hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at H
        exact H
    · rename_i ha
      simp only [not_lt] at ha
      exact ⟨hI, fun k hk l hl _ => hP k (by simpa using hk) l hl (Or.inl (by simp at hk; omega))⟩
  · intro st ⟨hI, hP⟩
    have := (size_le hI).trans hcap
    exact ⟨hI, fun k hk l hl _ => hP k hk l hl (Or.inl (by omega))⟩

theorem conjClosure_size (hT : Rep n T y) {cap : ℕ}
    (hcap : (conjClass (genK gens gg) y).ncard ≤ cap) :
    (conjClosure n gens gensInv T cap).1.size = (conjClass (genK gens gg) y).ncard := by
  obtain ⟨-, h2, h3, h4⟩ := conjClosure_spec hg hT hcap
  set E := (conjClosure n gens gensInv T cap).1.toList
  have e : keyOf n '' conjClass (genK gens gg) y = ↑((E.map (key n)).toFinset) := by
    ext kk
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_map, Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨t, ht, htz⟩ := h4 z hz
      exact ⟨t, ht, key_eq_keyOf htz⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨z, hz, htz⟩ := h3 t ht
      exact ⟨z, hz, (key_eq_keyOf htz).symm⟩
  rw [← Set.ncard_image_of_injective _ (fun a b h => keyOf_inj h), e, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup h2, List.length_map, Array.length_toList]

end Search

theorem conjClass_symm {M : Type*} [Group M] {K : Subgroup M} {a b : M}
    (h : a ∈ conjClass K b) : b ∈ conjClass K a := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, K.inv_mem hg, by group⟩

theorem conjClass_trans {M : Type*} [Group M] {K : Subgroup M} {a b c : M}
    (h1 : a ∈ conjClass K b) (h2 : b ∈ conjClass K c) : a ∈ conjClass K c := by
  obtain ⟨g, hg, rfl⟩ := h1
  exact conj_mem_conjClass hg h2

theorem conjClass_sub {M : Type*} [Group M] {K : Subgroup M} {a b : M} (hb : b ∈ K)
    (h : a ∈ conjClass K b) : a ∈ K := by
  obtain ⟨g, hg, rfl⟩ := h
  exact K.mul_mem (K.mul_mem hg hb) (K.inv_mem hg)

theorem contains_foldl (l : List Table) (kk : ℕ) :
    ∀ s : Std.HashSet ℕ, (l.foldl (fun s e => s.insert (key n e)) s).contains kk = true ↔
      s.contains kk = true ∨ ∃ e ∈ l, key n e = kk := by
  induction l with
  | nil => intro s; simp
  | cons e l ih =>
    intro s
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem strictlyIncreasing_of : ∀ {l : List ℕ}, l.Pairwise (· < ·) → strictlyIncreasing l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, strictlyIncreasing_of h.of_cons⟩

theorem keysDistinct_of {Ts : List Table} (h : (Ts.map (key n)).Nodup) :
    keysDistinct n Ts = true := by
  unfold keysDistinct
  apply strictlyIncreasing_of
  have hp := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simpa using Nat.le_total a b) (Ts.map (key n))
  have hnd := (List.mergeSort_perm (Ts.map (key n)) (fun a b : ℕ => decide (a ≤ b))).nodup_iff.2 h
  refine (hp.and hnd).imp ?_
  rintro a b ⟨h1, h2⟩
  simp only [decide_eq_true_eq] at h1
  omega

section Classes

variable {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
  (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹)
  {X : List Table} {xs : List (Equiv.Perm (Fin n))} (hX : List.Forall₂ (Rep n) X xs)
  {cap : ℕ} (hcap : ∀ y ∈ xs, (conjClass (genK gens gg) y).ncard ≤ cap)
include hg hX hcap

@[expose] def First (K : Subgroup (Equiv.Perm (Fin n))) (xs : List (Equiv.Perm (Fin n))) (p : ℕ) :
    Prop :=
  ∀ p' < p, xs.getD p' 1 ∉ conjClass K (xs.getD p 1)

omit hg hcap in
theorem rep_get {p : ℕ} (hp : p < X.length) : Rep n X.toArray[p]! (xs.getD p 1) := by
  have hl := hX.length_eq
  rw [getElem!_pos _ p (by simpa using hp), List.getElem_toArray,
    List.getD_eq_getElem _ _ (by omega)]
  exact hX.get hp (by omega)

omit hg hX in
theorem cap_get {p : ℕ} (hp : p < xs.length) :
    (conjClass (genK gens gg) (xs.getD p 1)).ncard ≤ cap :=
  hcap _ (by rw [List.getD_eq_getElem _ _ hp]; exact List.getElem_mem hp)

open Classical in
theorem findReps_spec :
    findReps n gens gensInv X cap =
      (List.range X.length).filter fun p => decide (First (genK gens gg) xs p) := by
  set K := genK gens gg
  have hl := hX.length_eq
  set FI : ℕ → Std.HashSet ℕ × Array ℕ → Prop := fun i st =>
    (∀ kk, st.1.contains kk = true ↔ ∃ p < i, ∃ z ∈ conjClass K (xs.getD p 1), keyOf n z = kk) ∧
      st.2.toList = (List.range i).filter fun p => decide (First K xs p)
  unfold findReps
  simp only [Id.run_bind, Id.run_pure]
  have H : ∀ st, FI X.toArray.size st →
      st.2.toList = (List.range X.length).filter fun p => decide (First K xs p) :=
    fun st hst => by rw [hst.2, List.size_toArray]
  have h0 : FI 0 (∅, #[]) := ⟨fun kk => by simp, rfl⟩
  refine H _ (CFSG.KS.Raw.Orb.forIn_range_idx X.toArray.size _ _ FI (FI X.toArray.size) h0 ?_
    (fun b hb => hb))
  · intro i hi st ⟨h1, h2⟩
    simp only [List.size_toArray] at hi
    have hx := rep_get hX hi
    have hkey : st.1.contains (key n X.toArray[i]!) = true ↔ ¬ First K xs i := by
      rw [h1, key_eq_keyOf hx]
      unfold First
      push Not
      constructor
      · rintro ⟨p, hp, z, hz, e⟩
        exact ⟨p, hp, conjClass_symm (by rw [← keyOf_inj e]; exact hz)⟩
      · rintro ⟨p, hp, hz⟩
        exact ⟨p, hp, _, conjClass_symm hz, rfl⟩
    split
    · rename_i hc
      have hfirst : First K xs i := by
        by_contra hf
        rw [← hkey] at hf
        rw [hf] at hc
        exact absurd hc (by decide)
      simp only [Id.run_bind, Array.forIn_pure_yield_eq_foldl, Id.run_pure]
      obtain ⟨-, -, h3, h4⟩ := conjClosure_spec hg hx (cap_get hcap (by omega))
      refine ⟨fun kk => ?_, ?_⟩
      · rw [← Array.foldl_toList, contains_foldl, h1]
        constructor
        · rintro (⟨p, hp, z, hz, e⟩ | ⟨t, ht, e⟩)
          · exact ⟨p, by omega, z, hz, e⟩
          · obtain ⟨z, hz, htz⟩ := h3 t ht
            exact ⟨i, by omega, z, hz, by rw [← e, key_eq_keyOf htz]⟩
        · rintro ⟨p, hp, z, hz, e⟩
          rcases Nat.lt_or_ge p i with hp' | hp'
          · exact Or.inl ⟨p, hp', z, hz, e⟩
          · have : p = i := by omega
            subst this
            obtain ⟨t, ht, htz⟩ := h4 z hz
            exact Or.inr ⟨t, ht, by rw [key_eq_keyOf htz, e]⟩
      · simp only [Array.toList_push, h2, List.range_succ, List.filter_append]
        simp [hfirst]
    · rename_i hc
      have hnf : ¬ First K xs i := by
        rw [← hkey]
        simpa using hc
      refine ⟨fun kk => ?_, ?_⟩
      · rw [h1]
        constructor
        · rintro ⟨p, hp, z, hz, e⟩
          exact ⟨p, by omega, z, hz, e⟩
        · rintro ⟨p, hp, z, hz, e⟩
          rcases Nat.lt_or_ge p i with hp' | hp'
          · exact ⟨p, hp', z, hz, e⟩
          · have : p = i := by omega
            subst this
            unfold First at hnf
            push Not at hnf
            obtain ⟨p', hp'', hm⟩ := hnf
            exact ⟨p', hp'', z, conjClass_trans hz (conjClass_symm hm), e⟩
      · simp only [h2, List.range_succ, List.filter_append]
        simp [hnf]

theorem classes_spec (hnd : xs.Nodup) (hmem : ∀ z, z ∈ xs ↔ z ∈ genK gens gg) :
    classOK n gens gensInv X cap = true ∧
      (classes n gens gensInv X cap).map (fun c => c.2.1.size) =
        (findReps n gens gensInv X cap).map fun p => (conjClass (genK gens gg) (xs.getD p 1)).ncard := by
  classical
  set K := genK gens gg
  have hl := hX.length_eq
  have hR := findReps_spec hg hX hcap
  have hRlt : ∀ p ∈ findReps n gens gensInv X cap, p < X.length := fun p hp => by
    rw [hR] at hp
    exact List.mem_range.1 (List.mem_filter.1 hp).1
  have hRfirst : ∀ p ∈ findReps n gens gensInv X cap, First K xs p := fun p hp => by
    rw [hR] at hp
    simpa using (List.mem_filter.1 hp).2
  have hsp := fun p (hp : p < X.length) => conjClosure_spec hg (rep_get hX hp) (cap_get hcap
    (by omega))
  set E : ℕ → List Table := fun p => (conjClosure n gens gensInv X.toArray[p]! cap).1.toList
  set L := (findReps n gens gensInv X cap).flatMap fun p => (E p).map (key n)
  have hLnd : L.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun p hp => (hsp p (hRlt p hp)).2.1, ?_⟩
    have hpw : (findReps n gens gensInv X cap).Pairwise (· < ·) := by
      rw [hR]
      exact List.pairwise_lt_range.filter _
    refine hpw.imp_of_mem fun {a b} ha hb hab => ?_
    rw [Function.onFun, List.disjoint_left]
    intro kk h1 h2
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h1
    obtain ⟨t', ht', e⟩ := List.mem_map.1 h2
    obtain ⟨z, hz, htz⟩ := (hsp a (hRlt a ha)).2.2.1 t ht
    obtain ⟨z', hz', htz'⟩ := (hsp b (hRlt b hb)).2.2.1 t' ht'
    have := eq_of_key htz' htz e
    subst this
    exact hRfirst b hb a hab (conjClass_trans (conjClass_symm hz) hz')
  have hLmem : ∀ kk, kk ∈ L ↔ kk ∈ xs.map (keyOf n) := by
    intro kk
    simp only [L, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨p, hp, t, ht, rfl⟩
      obtain ⟨z, hz, htz⟩ := (hsp p (hRlt p hp)).2.2.1 t ht
      have hxp : xs.getD p 1 ∈ K := by
        rw [← hmem, List.getD_eq_getElem _ _ (by have := hRlt p hp; omega)]
        exact List.getElem_mem _
      exact ⟨z, (hmem z).2 (conjClass_sub hxp hz), (key_eq_keyOf htz).symm⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hz
      have hex : ∃ p, p < X.length ∧ xs.getD p 1 ∈ conjClass K xs[q] :=
        ⟨q, by omega, by rw [List.getD_eq_getElem _ _ hq]; exact self_mem_conjClass _ _⟩
      set p := Nat.find hex
      obtain ⟨hp, hpc⟩ := Nat.find_spec hex
      have hfirst : First K xs p := fun p' hp' hm =>
        Nat.find_min hex hp' ⟨by omega, conjClass_trans hm hpc⟩
      have hpR : p ∈ findReps n gens gensInv X cap := by
        rw [hR]
        exact List.mem_filter.2 ⟨List.mem_range.2 hp, by simpa using hfirst⟩
      obtain ⟨t, ht, htz⟩ := (hsp p hp).2.2.2 _ (conjClass_symm hpc)
      exact ⟨p, hpR, t, ht, key_eq_keyOf htz⟩
  have hxnd : (xs.map (keyOf n)).Nodup := hnd.map fun a b h => keyOf_inj h
  have hLlen : L.length = X.length := by
    rw [((List.perm_ext_iff_of_nodup hLnd hxnd).2 hLmem).length_eq, List.length_map, hl]
  have hsizes : (classes n gens gensInv X cap).map (fun c => c.2.1.size) =
      (findReps n gens gensInv X cap).map fun p => (conjClass K (xs.getD p 1)).ncard := by
    rw [classes, List.map_map]
    apply List.map_congr_left
    intro p hp
    exact conjClosure_size hg (rep_get hX (hRlt p hp)) (cap_get hcap (by have := hRlt p hp; omega))
  refine ⟨?_, hsizes⟩
  unfold classOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hRlt, ?_⟩, ?_⟩, ?_⟩
  · intro c hc
    rw [classes] at hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    exact (hsp p (hRlt p hp)).1
  · apply keysDistinct_of
    rw [classes, List.flatMap_map, List.map_flatMap]
    exact hLnd
  · rw [← hLlen, classes, List.map_map]
    simp only [L, List.length_flatMap, List.length_map, Function.comp_def]
    rfl

end Classes

end CFSG.KS.SporSch.ClsSpec

end
