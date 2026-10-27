module

public import Certificates.Data.YamakiAmalgam
public import CFSG.Certificates.Kernel.Misc.BfsEnumSound

public section

namespace CFSG.KC.YamakiAmalgamFold

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KC.BfsEnum

section Guard

variable {α β κ : Type} [BEq κ] [LawfulBEq κ] [Hashable κ]

@[expose] def gfold (K : α → κ) (V : α → β) (l : List α) (m : Std.HashMap κ β) :
    Std.HashMap κ β :=
  l.foldl (fun m a => if m.contains (K a) then m else m.insert (K a) (V a)) m

theorem gfold_sound {K : α → κ} {V : α → β} {P : κ → β → Prop} :
    ∀ (l : List α) (m : Std.HashMap κ β), (∀ a ∈ l, P (K a) (V a)) →
      (∀ y v, m[y]? = some v → P y v) → ∀ y v, (gfold K V l m)[y]? = some v → P y v
  | [], m, _, h0 => h0
  | a :: l, m, hP, h0 => by
    unfold gfold
    rw [List.foldl_cons]
    refine gfold_sound l _ (fun b hb => hP b (List.mem_cons_of_mem a hb)) ?_
    intro y v hv
    split at hv
    · exact h0 y v hv
    · rw [Std.HashMap.getElem?_insert] at hv
      split at hv
      · rename_i he
        rw [← beq_iff_eq.1 he, ← Option.some.inj hv]
        exact hP a List.mem_cons_self
      · exact h0 y v hv

theorem gfold_mono {K : α → κ} {V : α → β} :
    ∀ (l : List α) (m : Std.HashMap κ β) (y : κ), m.contains y = true →
      (gfold K V l m).contains y = true
  | [], _, _, h => h
  | a :: l, m, y, h => by
    unfold gfold
    rw [List.foldl_cons]
    refine gfold_mono l _ y ?_
    split
    · exact h
    · rw [Std.HashMap.contains_insert, h, Bool.or_true]

theorem gfold_contains {K : α → κ} {V : α → β} :
    ∀ (l : List α) (m : Std.HashMap κ β) (a : α), a ∈ l → (gfold K V l m).contains (K a) = true
  | [], _, _, h => absurd h List.not_mem_nil
  | b :: l, m, a, h => by
    unfold gfold
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · refine gfold_mono l _ _ ?_
      split
      · assumption
      · rw [Std.HashMap.contains_insert, beq_self_eq_true, Bool.true_or]
    · exact gfold_contains l _ a h

theorem gfold_contains_iff {K : α → κ} {V : α → β} :
    ∀ (l : List α) (m : Std.HashMap κ β) (y : κ),
      (gfold K V l m).contains y = true ↔ m.contains y = true ∨ ∃ a ∈ l, K a = y
  | [], m, y => by simp [gfold]
  | a :: l, m, y => by
    unfold gfold
    rw [List.foldl_cons]
    change (gfold K V l _).contains y = true ↔ _
    rw [gfold_contains_iff l]
    constructor
    · rintro (h | ⟨b, hb, rfl⟩)
      · split at h
        · exact Or.inl h
        · rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
          rcases h with rfl | h
          · exact Or.inr ⟨a, List.mem_cons_self, rfl⟩
          · exact Or.inl h
      · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, rfl⟩
    · rintro (h | ⟨b, hb, rfl⟩)
      · refine Or.inl ?_
        split
        · exact h
        · rw [Std.HashMap.contains_insert, h, Bool.or_true]
      · rcases List.mem_cons.1 hb with rfl | hb
        · refine Or.inl ?_
          split
          · assumption
          · rw [Std.HashMap.contains_insert, beq_self_eq_true, Bool.true_or]
        · exact Or.inr ⟨b, hb, rfl⟩

theorem gfold2_spec (K : ℕ → ℕ → κ) (rs js : List ℕ) :
    (∀ y r j, (rs.foldl (fun m r => gfold (K r) (fun j => (r, j)) js m) ∅)[y]? = some (r, j) →
        r ∈ rs ∧ j ∈ js ∧ K r j = y) ∧
      ∀ y, (rs.foldl (fun m r => gfold (K r) (fun j => (r, j)) js m) ∅).contains y = true ↔
        ∃ r ∈ rs, ∃ j ∈ js, K r j = y := by
  have key : ∀ (rs' : List ℕ) (m : Std.HashMap κ (ℕ × ℕ)),
      (∀ y r j, m[y]? = some (r, j) → r ∈ rs ∧ j ∈ js ∧ K r j = y) → (∀ r ∈ rs', r ∈ rs) →
      (∀ y r j, (rs'.foldl (fun m r => gfold (K r) (fun j => (r, j)) js m) m)[y]? = some (r, j) →
        r ∈ rs ∧ j ∈ js ∧ K r j = y) ∧
      ∀ y, (rs'.foldl (fun m r => gfold (K r) (fun j => (r, j)) js m) m).contains y = true ↔
        m.contains y = true ∨ ∃ r ∈ rs', ∃ j ∈ js, K r j = y := by
    intro rs'
    induction rs' with
    | nil => intro m h0 _; simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false,
        or_false, iff_self, implies_true, and_true]; exact h0
    | cons r rs' ih =>
      intro m h0 hrs
      rw [List.foldl_cons]
      have h1 : ∀ y r' j, (gfold (K r) (fun j => (r, j)) js m)[y]? = some (r', j) →
          r' ∈ rs ∧ j ∈ js ∧ K r' j = y := by
        intro y r' j hv
        refine gfold_sound (P := fun y v => v.1 ∈ rs ∧ v.2 ∈ js ∧ K v.1 v.2 = y) js m
          (fun a ha => ⟨hrs r List.mem_cons_self, ha, rfl⟩)
          (fun y v hv => h0 y v.1 v.2 hv) y (r', j) hv
      obtain ⟨s1, s2⟩ := ih _ h1 fun r' h => hrs r' (List.mem_cons_of_mem r h)
      refine ⟨s1, fun y => ?_⟩
      rw [s2, gfold_contains_iff]
      constructor
      · rintro ((h | ⟨j, hj, rfl⟩) | ⟨r', hr', j, hj, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨r, List.mem_cons_self, j, hj, rfl⟩
        · exact Or.inr ⟨r', List.mem_cons_of_mem r hr', j, hj, rfl⟩
      · rintro (h | ⟨r', hr', j, hj, rfl⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hr' with rfl | hr'
          · exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
          · exact Or.inr ⟨r', hr', j, hj, rfl⟩
  obtain ⟨s1, s2⟩ := key rs ∅ (fun y r j h => by simp at h) fun r h => h
  exact ⟨s1, fun y => by rw [s2]; simp⟩

end Guard

theorem conjIndex1_eq (E : Enum) (R : Array (Array ℕ)) :
    conjIndex1 E R = (List.range R.size).foldl (fun m r => gfold
      (fun j => compA (compA (invA E.elems[j]!) R[r]!) E.elems[j]!) (fun j => (r, j))
      (List.range E.elems.size) m) ∅ := rfl

theorem conjIndex1_get {E : Enum} {R : Array (Array ℕ)} {y : Array ℕ} {r j : ℕ}
    (h : (conjIndex1 E R)[y]? = some (r, j)) : r < R.size ∧ j < E.elems.size ∧
      compA (compA (invA E.elems[j]!) R[r]!) E.elems[j]! = y := by
  rw [conjIndex1_eq] at h
  obtain ⟨a, b, c⟩ := (gfold2_spec _ _ _).1 y r j h
  exact ⟨List.mem_range.1 a, List.mem_range.1 b, c⟩

theorem conjIndex1_isSome {E : Enum} {R : Array (Array ℕ)} {y : Array ℕ} :
    ((conjIndex1 E R)[y]?).isSome ↔ ∃ r < R.size, ∃ j < E.elems.size,
      compA (compA (invA E.elems[j]!) R[r]!) E.elems[j]! = y := by
  rw [← Std.HashMap.contains_eq_isSome_getElem?, conjIndex1_eq, (gfold2_spec _ _ _).2]
  simp

theorem conjIndex2_eq (E : Enum) (P : Array (Array ℕ × Array ℕ)) :
    conjIndex2 E P = (List.range P.size).foldl (fun m k => gfold
      (fun j => (compA (compA (invA E.elems[j]!) P[k]!.1) E.elems[j]!,
        compA (compA (invA E.elems[j]!) P[k]!.2) E.elems[j]!)) (fun j => (k, j))
      (List.range E.elems.size) m) ∅ := rfl

theorem conjIndex2_get {E : Enum} {P : Array (Array ℕ × Array ℕ)} {y : Array ℕ × Array ℕ}
    {k j : ℕ} (h : (conjIndex2 E P)[y]? = some (k, j)) : k < P.size ∧ j < E.elems.size ∧
      (compA (compA (invA E.elems[j]!) P[k]!.1) E.elems[j]!,
        compA (compA (invA E.elems[j]!) P[k]!.2) E.elems[j]!) = y := by
  rw [conjIndex2_eq] at h
  obtain ⟨a, b, c⟩ := (gfold2_spec _ _ _).1 y k j h
  exact ⟨List.mem_range.1 a, List.mem_range.1 b, c⟩

theorem conjIndex2_isSome {E : Enum} {P : Array (Array ℕ × Array ℕ)} {y : Array ℕ × Array ℕ} :
    ((conjIndex2 E P)[y]?).isSome ↔ ∃ k < P.size, ∃ j < E.elems.size,
      (compA (compA (invA E.elems[j]!) P[k]!.1) E.elems[j]!,
        compA (compA (invA E.elems[j]!) P[k]!.2) E.elems[j]!) = y := by
  rw [← Std.HashMap.contains_eq_isSome_getElem?, conjIndex2_eq, (gfold2_spec _ _ _).2]
  simp

theorem invA_eq (t : Array ℕ) :
    invA t = (List.range' 0 64).foldl (fun r i => r.set! t[i]! i) (Array.replicate 64 0) := by
  unfold invA
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, bind_pure]
  exact forIn_foldl _ _ _ _ fun j b => rfl

theorem setFold_spec (t : Array ℕ) (hb : ∀ i < 64, t[i]! < 64)
    (hinj : ∀ i < 64, ∀ j < 64, t[i]! = t[j]! → i = j) : ∀ m ≤ 64,
    ((List.range' 0 m).foldl (fun r i => r.set! t[i]! i) (Array.replicate 64 0)).size = 64 ∧
      ∀ i < m, ((List.range' 0 m).foldl (fun r i => r.set! t[i]! i) (Array.replicate 64 0))[t[i]!]? =
        some i
  | 0, _ => ⟨by simp, fun i h => absurd h (Nat.not_lt_zero i)⟩
  | m + 1, hm => by
    obtain ⟨s, g⟩ := setFold_spec t hb hinj m (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul,
      Nat.zero_add]
    generalize (List.range' 0 m).foldl (fun r i => r.set! t[i]! i) (Array.replicate 64 0) = A at s g
    refine ⟨by simp [s], fun i hi => ?_⟩
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases he : t[m]! = t[i]!
    · have hmi := hinj _ (by omega) _ (by omega) he
      subst hmi
      rw [if_pos rfl, if_pos (by rw [s]; exact hb _ (by omega))]
    · have hlt : i < m := by
        rcases Nat.lt_or_ge i m with h | h
        · exact h
        · exact absurd (by rw [show i = m by omega]) he
      rw [if_neg he]
      exact g i hlt

theorem invA_get {t : Array ℕ} (hb : ∀ i < 64, t[i]! < 64)
    (hinj : ∀ i < 64, ∀ j < 64, t[i]! = t[j]! → i = j) {i : ℕ} (hi : i < 64) :
    (invA t)[t[i]!]! = i := by
  rw [invA_eq]
  obtain ⟨s, g⟩ := setFold_spec t hb hinj 64 le_rfl
  have e := g i hi
  generalize (List.range' 0 64).foldl (fun (r : Array ℕ) (i : ℕ) => r.set! t[i]! i)
    (Array.replicate 64 0) = A at s e ⊢
  have hk : t[i]! < A.size := by rw [s]; exact hb i hi
  rw [Array.getElem?_eq_getElem hk] at e
  rw [getElem!_pos A (t[i]!) hk]
  exact Option.some.inj e

theorem size_invA (t : Array ℕ) (hb : ∀ i < 64, t[i]! < 64)
    (hinj : ∀ i < 64, ∀ j < 64, t[i]! = t[j]! → i = j) : (invA t).size = 64 := by
  rw [invA_eq]
  exact (setFold_spec t hb hinj 64 le_rfl).1

theorem invA_comp {t : Array ℕ} (hb : ∀ i < 64, t[i]! < 64)
    (hinj : ∀ i < 64, ∀ j < 64, t[i]! = t[j]! → i = j) : compA (invA t) t = idA () :=
  ext64 (size_compA _ _) size_idA fun i hi => by
    rw [compA_get _ _ hi, invA_get hb hinj hi, idA_get hi]

theorem comp_invA {t : Array ℕ} (hb : ∀ i < 64, t[i]! < 64)
    (hinj : ∀ i < 64, ∀ j < 64, t[i]! = t[j]! → i = j) : compA t (invA t) = idA () := by
  refine ext64 (size_compA _ _) size_idA fun j hj => ?_
  obtain ⟨i, hi, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range 64)
    (t := Finset.range 64) (fun i _ => t[i]!)
    (fun i h => Finset.mem_range.2 (hb i (Finset.mem_range.1 h)))
    (fun a b ha hb' e => hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb') e)
    le_rfl j (Finset.mem_range.2 hj)
  rw [compA_get _ _ hj, idA_get hj, e, invA_get hb hinj (Finset.mem_range.1 hi)]

end CFSG.KC.YamakiAmalgamFold

end
