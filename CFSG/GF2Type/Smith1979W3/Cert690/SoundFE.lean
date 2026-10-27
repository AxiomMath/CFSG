module

public import CFSG.GF2Type.Smith1979W3.Cert690.Check
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFE2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

theorem foldl_insert_contains_aux {α : Type} [BEq α] [LawfulBEq α] [Hashable α]
    [LawfulHashable α] (f : α → α) (l : List α) (S : Std.HashSet α) (X : α) :
    (l.foldl (fun s x => s.insert (f x)) S).contains X = true ↔
      S.contains X = true ∨ ∃ x ∈ l, f x = X := by
  induction l generalizing S with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ((h | h) | ⟨d, hd, h⟩)
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨d, List.mem_cons_of_mem a hd, h⟩
    · rintro (h | ⟨d, hd, h⟩)
      · exact Or.inl (Or.inr h)
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨d, hd, h⟩

theorem foldl_insert_contains {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (l : List α) (S : Std.HashSet α) (X : α) :
    (l.foldl (fun s x => s.insert x) S).contains X = true ↔
      S.contains X = true ∨ X ∈ l := by
  simpa using foldl_insert_contains_aux id l S X

theorem hashSetOfArray_contains (A : Array ℕ) (x : ℕ) :
    (hashSetOfArray A).contains x = true ↔ x ∈ A.toList := by
  rw [hashSetOfArray, ← Array.foldl_toList, foldl_insert_contains]
  simp

theorem hashSetOfArray_size_eq_toFinset_card (A : Array ℕ) :
    (hashSetOfArray A).size = A.toList.toFinset.card := by
  let S := hashSetOfArray A
  have hnd : S.toList.Nodup := by
    have h := Std.HashSet.distinct_toList (m := S)
    have h' : S.toList.Pairwise (· ≠ ·) :=
      h.imp (fun {a b} hab hEq => by subst hEq; simp at hab)
    simpa [List.Nodup] using h'
  calc S.size = S.toList.length := Std.HashSet.length_toList.symm
    _ = S.toList.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ = A.toList.toFinset.card := by
      congr 1
      ext x
      simp only [List.mem_toFinset, Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
      exact hashSetOfArray_contains A x

theorem nodup_toList_of_hashSetOfArray_size {A : Array ℕ}
    (h : (hashSetOfArray A).size = A.size) : A.toList.Nodup := by
  have hcard : A.toList.toFinset.card = A.toList.length := by
    rw [← hashSetOfArray_size_eq_toFinset_card, h, Array.size_eq_length_toList]
  rw [List.nodup_iff_length_dedup_eq, ← List.card_toFinset]
  exact hcard

theorem array_getElem!_eq_getElem {A : Array ℕ} {i : ℕ} (h : i < A.size) : A[i]! = A[i] := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?]
  simp [h]

theorem list_toArray_getElem! {l : List ℕ} {i : ℕ} (h : i < l.length) :
    (l.toArray)[i]! = l[i]! := by
  rw [array_getElem!_eq_getElem (by simpa using h), getElem!_eq_getElem_of_lt h]
  exact List.getElem_toArray (by simpa using h)

theorem array_getElem_mem_toList {A : Array ℕ} {i : ℕ} (h : i < A.size) :
    A[i] ∈ A.toList := by
  have h' : i < A.toList.length := by simpa [Array.length_toList] using h
  rw [← Array.getElem_toList h']
  exact List.getElem_mem h'

theorem enumOK_sound {gens : List ℕ} {E : Array ℕ} {par : Array (ℕ × ℕ)}
    (h : enumOK gens E par = true) : EnumCert gens E.toList := by
  classical
  set gs := gens.toArray with hgs
  have hgsize : gs.size = gens.length := List.size_toArray
  have hgget : ∀ j (hj : j < gens.length), gs[j]! = gens[j]! := by
    intro j hj
    rw [hgs]
    exact list_toArray_getElem! hj
  unfold enumOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true, decide_eq_true_eq,
    beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hne, hone⟩, _⟩, hpar⟩, hset⟩, hclosed⟩, hinv⟩ := h
  have hpar_ne : ∀ i, i ≠ 0 → i < E.size →
      par[i]!.1 < i ∧ par[i]!.2 < gens.length ∧
        E[i]! = Code.mul (E[par[i]!.1]!) (gens[par[i]!.2]!) := by
    intro i hi0 hi
    have h := hpar i (List.mem_range.mpr hi)
    have hb : (i == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact hi0
    rw [hb, Bool.false_or] at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have h2' : par[i]!.2 < gens.length := by
      simpa [hgsize] using (of_decide_eq_true h2)
    exact ⟨of_decide_eq_true h1, h2', by
      rw [← hgget _ h2']; exact beq_iff_eq.1 h3⟩
  have hE0 : E[0]! = Code.one := hone
  have hlt : ∀ i, i < E.size → E[i]! < 2 ^ 36 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [hE0]
        exact Code.one_lt
      · have hrest := hpar_ne i hi0 hi
        have hji : par[i]!.1 < i := hrest.1
        have hj : par[i]!.2 < gens.length := hrest.2.1
        have hjeq : E[i]! = Code.mul (E[par[i]!.1]!) (gens[par[i]!.2]!) := hrest.2.2
        have hjmem : par[i]!.1 < E.size := by omega
        calc E[i]! = Code.mul (E[par[i]!.1]!) (gens[par[i]!.2]!) := hjeq
          _ < 2 ^ 36 := Code.mul_lt _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h0 : 0 < E.size := Nat.pos_of_ne_zero hne
    have hE0' : E[0]! = Code.one := hE0
    rw [array_getElem!_eq_getElem h0] at hE0'
    rw [← hE0']
    exact array_getElem_mem_toList h0
  ·
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    have hiE : i < E.size := by simpa [Array.length_toList] using hi
    rw [Array.getElem_toList (by simpa [Array.length_toList] using hiE)]
    rw [← array_getElem!_eq_getElem hiE]
    exact hlt i hiE
  ·
    exact nodup_toList_of_hashSetOfArray_size hset
  ·
    intro c hc g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    have hiE : i < E.size := by simpa [Array.length_toList] using hi
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    have hgsz : j < gs.size := by simpa [hgsize] using hj
    have hcl := hclosed i (List.mem_range.mpr hiE) j hgsz
    have hmem := (hashSetOfArray_contains E _).1 hcl
    have hcE : E.toList[i] = E[i] :=
      Array.getElem_toList (by simpa [Array.length_toList] using hiE)
    have hgj : gs[j]! = gens[j]! := hgget j hj
    simpa [hcE, array_getElem!_eq_getElem hiE, hgj] using hmem
  ·
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    have hgsz : j < gs.size := by simpa [hgsize] using hj
    have hinvj := hinv j hgsz
    rw [Array.any_eq_true] at hinvj
    obtain ⟨i, hi, hieq⟩ := hinvj
    refine ⟨E[i], ?_, ?_⟩
    · exact array_getElem_mem_toList hi
    · have hgj : gs[j] = gens[j]! := by
        rw [← array_getElem!_eq_getElem hgsz]
        exact hgget j hj
      have hieq' : Code.mul (gs[j]) (E[i]) = Code.one := beq_iff_eq.1 hieq
      rw [hgj] at hieq'
      simpa [getElem!_eq_getElem_of_lt hj] using hieq'
  ·
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    have hiE : i < E.size := by simpa [Array.length_toList] using hi
    rw [Array.getElem_toList (by simpa [Array.length_toList] using hiE)]
    rw [← array_getElem!_eq_getElem hiE]
    exact enum_reach hE0 hpar_ne i hiE

end CFSG.GF2Type.Smith1979W3.Cert690

end
