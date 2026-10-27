module

public import CFSG.ClassicalInvolution.Solomon73.YamakiModel
public import Certificates.Certificate550711

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open CFSG.Open

section Checks

theorem enumCheck_holds : enumCheck () = true := Certificates.certificate550711.1

theorem sizeCheck_holds : sizeCheck () = true := Certificates.certificate550711.2.1

theorem tablesGenCheck_holds : tablesGenCheck () = true := Certificates.certificate550711.2.2

end Checks

theorem size_wordsA (gs : Array (Array ℕ)) (ws : List (List ℕ)) :
    (wordsA gs ws).size = ws.length := by
  simp [wordsA]

theorem getElem!_wordsA (gs : Array (Array ℕ)) (ws : List (List ℕ)) {j : ℕ} (hj : j < ws.length) :
    (wordsA gs ws)[j]! = wordA gs (ws.getD j []) := by
  rw [getElem!_pos (wordsA gs ws) j (by rw [size_wordsA]; exact hj), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.getD_some]
  simp [wordsA]

theorem getD_mem {ws : List (List ℕ)} {j : ℕ} (hj : j < ws.length) : ws.getD j [] ∈ ws := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

theorem getD_mem_or_nil {ws : List (List ℕ)} (j : ℕ) : ws.getD j [] ∈ ws ∨ ws.getD j [] = [] := by
  by_cases hj : j < ws.length
  · exact Or.inl (getD_mem hj)
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

theorem mem_of_wordsIn {I : List ℕ} {ws : List (List ℕ)} (h : wordsIn I ws = true) :
    ∀ w ∈ ws, ∀ i ∈ w, i ∈ I := by
  simp only [wordsIn, List.all_eq_true, List.contains_iff_mem] at h
  exact h

theorem letters_getD {ws : List (List ℕ)} {I : List ℕ} (hws : ∀ w ∈ ws, ∀ i ∈ w, i ∈ I)
    (j : ℕ) : ∀ i ∈ ws.getD j [], i ∈ I := by
  rcases getD_mem_or_nil (ws := ws) j with h | h
  · exact hws _ h
  · rw [h]
    intro i hi
    cases hi

theorem gWords_length : gWords.length = 2 := rfl

theorem nWords_length : nWords.length = 2 := rfl

theorem hWords_length : hWords.length = 2 := rfl

theorem idxX0_spec {i : ℕ} (hi : i ∈ idxX0) : i < 12 ∧ (i ≤ 8 ∨ i = 10) := by
  simp only [idxX0, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

theorem idxN0_spec {i : ℕ} (hi : i ∈ idxN0) : i < 12 ∧ (i ≤ 8 ∨ i = 9 ∨ i = 10) := by
  simp only [idxN0, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

theorem idxHhat_spec {i : ℕ} (hi : i ∈ idxHhat) : i < 12 ∧ (i ≤ 8 ∨ i = 10 ∨ i = 11) := by
  simp only [idxHhat, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

theorem mem_idxX0 {i : Fin 12} (hi : i.val ≤ 8 ∨ i = 10) : i.val ∈ idxX0 := by
  have : i.val ≤ 8 ∨ i.val = 10 := hi.imp_right fun h => by rw [h]; rfl
  simp only [idxX0, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem mem_idxN0 {i : Fin 12} (hi : i.val ≤ 8 ∨ i = 9 ∨ i = 10) : i.val ∈ idxN0 := by
  have : i.val ≤ 8 ∨ i.val = 9 ∨ i.val = 10 :=
    hi.imp_right (Or.imp (fun h => by rw [h]; rfl) fun h => by rw [h]; rfl)
  simp only [idxN0, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem mem_idxHhat {i : Fin 12} (hi : i.val ≤ 8 ∨ i = 10 ∨ i = 11) : i.val ∈ idxHhat := by
  have : i.val ≤ 8 ∨ i.val = 10 ∨ i.val = 11 :=
    hi.imp_right (Or.imp (fun h => by rw [h]; rfl) fun h => by rw [h]; rfl)
  simp only [idxHhat, List.mem_cons, List.not_mem_nil, or_false]
  omega

@[expose] def ysp (i : ℕ) : StatedSp 3 (ZMod 2) := if h : i < 12 then yamakiSp ⟨i, h⟩ else 1

@[expose] def yword (w : List ℕ) : StatedSp 3 (ZMod 2) := (w.map ysp).prod

theorem code_ysp {i : ℕ} (hi : i < 12) : code (ysp i) = (genA ())[i]! := by
  rw [ysp, dif_pos hi, code_yamakiSp]

theorem code_yword {w : List ℕ} (hw : ∀ i ∈ w, i < 12) : code (yword w) = wordA (genA ()) w :=
  code_prod_map w fun i hi => (code_ysp (hw i hi)).symm

theorem code_yword_getD {ws : List (List ℕ)} {I : List ℕ} (hI : ∀ i ∈ I, i < 12)
    (hws : ∀ w ∈ ws, ∀ i ∈ w, i ∈ I) {j : ℕ} (hj : j < ws.length) :
    (wordsA (genA ()) ws)[j]! = code (yword (ws.getD j [])) := by
  rw [getElem!_wordsA _ _ hj, code_yword]
  intro i hi
  exact hI i (hws _ (getD_mem hj) i hi)

theorem yword_mem_X0 {w : List ℕ} (hw : ∀ i ∈ w, i ∈ idxX0) : yword w ∈ X0 := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  obtain ⟨h12, hi'⟩ := idxX0_spec (hw i hi)
  rw [ysp, dif_pos h12]
  refine yamakiSp_mem_X0 ?_
  rcases hi' with h | rfl
  · exact Or.inl h
  · exact Or.inr rfl

theorem yword_mem_N0 {w : List ℕ} (hw : ∀ i ∈ w, i ∈ idxN0) : yword w ∈ N0 := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  obtain ⟨h12, hi'⟩ := idxN0_spec (hw i hi)
  rw [ysp, dif_pos h12]
  refine yamakiSp_mem_N0 ?_
  rcases hi' with h | rfl | rfl
  · exact Or.inl h
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem yword_mem_Hhat {w : List ℕ} (hw : ∀ i ∈ w, i ∈ idxHhat) : yword w ∈ Hhat := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  obtain ⟨h12, hi'⟩ := idxHhat_spec (hw i hi)
  rw [ysp, dif_pos h12]
  refine yamakiSp_mem_Hhat ?_
  rcases hi' with h | rfl | rfl
  · exact Or.inl h
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

@[expose] def gfam (j : ℕ) : StatedSp 3 (ZMod 2) := yword (gWords.getD j [])

@[expose] def nfam (j : ℕ) : StatedSp 3 (ZMod 2) := yword (nWords.getD j [])

@[expose] def hfam (j : ℕ) : StatedSp 3 (ZMod 2) := yword (hWords.getD j [])

section Tables

theorem tablesGenCheck_spec :
    (∀ w ∈ gWords, ∀ i ∈ w, i ∈ idxX0) ∧ (∀ w ∈ nWords, ∀ i ∈ w, i ∈ idxN0) ∧
      (∀ w ∈ hWords, ∀ i ∈ w, i ∈ idxHhat) ∧
      (∀ i ∈ idxX0, ((enumX ()).lookup (genA ())[i]!).isSome) ∧
      (∀ i ∈ idxN0, ((enumN ()).lookup (genA ())[i]!).isSome) ∧
      ∀ i ∈ idxHhat, ((enumH ()).lookup (genA ())[i]!).isSome := by
  have h := tablesGenCheck_holds
  simp only [tablesGenCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨mem_of_wordsIn h1, mem_of_wordsIn h2, mem_of_wordsIn h3, h4, h5, h6⟩

theorem enumCheck_spec :
    enumOK (enumX ()) (gX ()) = true ∧ enumOK (enumN ()) (gN ()) = true ∧
      enumOK (enumH ()) (gH ()) = true := by
  have h := enumCheck_holds
  simp only [enumCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem sizeCheck_spec :
    (enumX ()).elems.size = 1536 ∧ (enumN ()).elems.size = 10752 ∧
      (enumH ()).elems.size = 23040 := by
  have h := sizeCheck_holds
  simp only [sizeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem size_gX : (gX ()).size = 2 := size_wordsA _ _

theorem size_gN : (gN ()).size = 2 := size_wordsA _ _

theorem size_gH : (gH ()).size = 2 := size_wordsA _ _

theorem gX_get {j : ℕ} (hj : j < 2) : (gX ())[j]! = code (gfam j) :=
  code_yword_getD (fun _ hi => (idxX0_spec hi).1) tablesGenCheck_spec.1
    (by rw [gWords_length]; exact hj)

theorem gN_get {j : ℕ} (hj : j < 2) : (gN ())[j]! = code (nfam j) :=
  code_yword_getD (fun _ hi => (idxN0_spec hi).1) tablesGenCheck_spec.2.1
    (by rw [nWords_length]; exact hj)

theorem gH_get {j : ℕ} (hj : j < 2) : (gH ())[j]! = code (hfam j) :=
  code_yword_getD (fun _ hi => (idxHhat_spec hi).1) tablesGenCheck_spec.2.2.1
    (by rw [hWords_length]; exact hj)

theorem gfam_mem_X0 (j : ℕ) : gfam j ∈ X0 := yword_mem_X0 (letters_getD tablesGenCheck_spec.1 j)

theorem nfam_mem_N0 (j : ℕ) : nfam j ∈ N0 :=
  yword_mem_N0 (letters_getD tablesGenCheck_spec.2.1 j)

theorem hfam_mem_Hhat (j : ℕ) : hfam j ∈ Hhat :=
  yword_mem_Hhat (letters_getD tablesGenCheck_spec.2.2.1 j)

theorem mem_closure_two {E : Enum} {gs : Array (Array ℕ)} {s : ℕ → StatedSp 3 (ZMod 2)}
    (hsize : gs.size = 2) (hgs : ∀ j < 2, gs[j]! = code (s j)) (h : enumOK E gs = true)
    (x : StatedSp 3 (ZMod 2)) :
    x ∈ Subgroup.closure (s '' Set.Iio 2) ↔ (E.lookup (code x)).isSome := by
  have := mem_closure_iff_isSome (s := s) (fun j hj => hgs j (hsize ▸ hj)) h x
  rwa [hsize] at this

theorem X0_eq_closure : X0 = Subgroup.closure (gfam '' Set.Iio 2) := by
  apply le_antisymm
  · rw [X0, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have h := tablesGenCheck_spec.2.2.2.1 i.val (mem_idxX0 hi)
    rw [← code_yamakiSp] at h
    exact (mem_closure_two size_gX (fun j hj => gX_get hj) enumCheck_spec.1 _).mpr h
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact gfam_mem_X0 j

theorem N0_eq_closure : N0 = Subgroup.closure (nfam '' Set.Iio 2) := by
  apply le_antisymm
  · rw [N0, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have h := tablesGenCheck_spec.2.2.2.2.1 i.val (mem_idxN0 hi)
    rw [← code_yamakiSp] at h
    exact (mem_closure_two size_gN (fun j hj => gN_get hj) enumCheck_spec.2.1 _).mpr h
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact nfam_mem_N0 j

theorem Hhat_eq_closure : Hhat = Subgroup.closure (hfam '' Set.Iio 2) := by
  apply le_antisymm
  · rw [Hhat, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have h := tablesGenCheck_spec.2.2.2.2.2 i.val (mem_idxHhat hi)
    rw [← code_yamakiSp] at h
    exact (mem_closure_two size_gH (fun j hj => gH_get hj) enumCheck_spec.2.2 _).mpr h
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact hfam_mem_Hhat j

theorem mem_X0_iff_isSome (x : StatedSp 3 (ZMod 2)) :
    x ∈ X0 ↔ ((enumX ()).lookup (code x)).isSome := by
  rw [X0_eq_closure]
  exact mem_closure_two size_gX (fun j hj => gX_get hj) enumCheck_spec.1 x

theorem mem_N0_iff_isSome (x : StatedSp 3 (ZMod 2)) :
    x ∈ N0 ↔ ((enumN ()).lookup (code x)).isSome := by
  rw [N0_eq_closure]
  exact mem_closure_two size_gN (fun j hj => gN_get hj) enumCheck_spec.2.1 x

theorem mem_Hhat_iff_isSome (x : StatedSp 3 (ZMod 2)) :
    x ∈ Hhat ↔ ((enumH ()).lookup (code x)).isSome := by
  rw [Hhat_eq_closure]
  exact mem_closure_two size_gH (fun j hj => gH_get hj) enumCheck_spec.2.2 x

theorem exists_lt_of_isSome {E : Enum} {x : StatedSp 3 (ZMod 2)} (h : (E.lookup (code x)).isSome) :
    ∃ i < E.elems.size, E.elems[i]! = code x := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  exact ⟨i, (Enum.lookup_spec hi).1, (Enum.lookup_spec hi).2⟩

theorem exists_lt_of_mem_X0 {x : StatedSp 3 (ZMod 2)} (hx : x ∈ X0) :
    ∃ i < (enumX ()).elems.size, (enumX ()).elems[i]! = code x :=
  exists_lt_of_isSome ((mem_X0_iff_isSome x).mp hx)

theorem exists_mem_X0_of_lt {i : ℕ} (hi : i < (enumX ()).elems.size) :
    ∃ x ∈ X0, code x = (enumX ()).elems[i]! := by
  have htree : treeOK (enumX ()) (gX ()) = true := by
    have := enumCheck_spec.1
    simp only [enumOK, Bool.and_eq_true] at this
    exact this.1.1
  obtain ⟨x, hx, hxe⟩ := exists_mem_closure_of_treeOK (s := gfam)
    (fun l hl => gX_get (size_gX ▸ hl)) htree i hi
  rw [size_gX, ← X0_eq_closure] at hx
  exact ⟨x, hx, hxe⟩

theorem card_X0 : Nat.card X0 = 1536 := by
  have h := card_closure_eq (s := gfam) (fun j hj => gX_get (size_gX ▸ hj)) enumCheck_spec.1
  rw [size_gX, ← X0_eq_closure] at h
  rw [h, sizeCheck_spec.1]

theorem card_N0 : Nat.card N0 = 10752 := by
  have h := card_closure_eq (s := nfam) (fun j hj => gN_get (size_gN ▸ hj)) enumCheck_spec.2.1
  rw [size_gN, ← N0_eq_closure] at h
  rw [h, sizeCheck_spec.2.1]

theorem card_Hhat : Nat.card Hhat = 23040 := by
  have h := card_closure_eq (s := hfam) (fun j hj => gH_get (size_gH ▸ hj)) enumCheck_spec.2.2
  rw [size_gH, ← Hhat_eq_closure] at h
  rw [h, sizeCheck_spec.2.2]

end Tables

end CFSG.ClassicalInvolution.Solomon73.Yamaki
