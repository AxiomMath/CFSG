module

public import Certificates.Data.Kernel.Griess13.Packed
import all Init.Data.String.Legacy

public section

namespace CFSG.KC.G13

open String CFSG.Monster.GMS.Griess13.Co1Data

private theorem splitOnAux_one (sep : String) (c : Char) (hget : Pos.Raw.get sep 0 = c)
    (hnext : Pos.Raw.next sep 0 = ⟨1⟩) (hend : sep.rawEndPos ≤ (⟨1⟩ : Pos.Raw))
    (hsz : c.utf8Size = 1) (l m r : List Char) (acc : List String) :
    String.splitOnAux (String.ofList (l ++ m ++ r)) sep ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      acc.reverse ++ (List.splitOnPPrepend (· == c) r m.reverse).map String.ofList := by
  unfold String.splitOnAux
  simp only [List.append_assoc, atEnd_iff, rawEndPos_ofList, utf8Len_append, Pos.Raw.mk_le_mk,
    Nat.add_le_add_iff_left, (by omega : utf8Len m + utf8Len r ≤ utf8Len m ↔ utf8Len r = 0),
    utf8Len_eq_zero, List.reverse_cons, hget, hnext]
  have hz : ∀ p : Pos.Raw, p.unoffsetBy 0 = p := fun ⟨n⟩ => by simp [Pos.Raw.unoffsetBy]
  simp only [hend, ↓reduceIte, hz]
  split
  · subst r
    simpa using extract_of_valid l m []
  · obtain ⟨d, r, rfl⟩ := r.exists_cons_of_ne_nil ‹_›
    simp only [by
      simpa [-ofList_append] using
        (⟨get_of_valid (l ++ m) (d :: r), next_of_valid (l ++ m) d r,
            extract_of_valid l m (d :: r)⟩ :
          _ ∧ _ ∧ _)]
    split <;> rename_i h
    · obtain rfl : d = c := by simpa using h
      have hu : utf8Len l + (utf8Len m + d.utf8Size) - 1 = utf8Len l + utf8Len m := by omega
      have hx := extract_of_valid l m (d :: r)
      simp at hx
      simpa [Pos.Raw.unoffsetBy, hu, hx, hsz, Nat.add_assoc, List.splitOnPPrepend_cons_eq_ite] using
        splitOnAux_one sep d hget hnext hend hsz (l ++ m ++ [d]) [] r ((ofList m) :: acc)
    · simpa [Pos.Raw.unoffsetBy, List.splitOnPPrepend_cons_eq_ite, h, Nat.add_assoc] using
        splitOnAux_one sep c hget hnext hend hsz l (m ++ [d]) r acc

theorem splitOn_one (sep : String) (c : Char) (hget : Pos.Raw.get sep 0 = c)
    (hnext : Pos.Raw.next sep 0 = ⟨1⟩) (hend : sep.rawEndPos ≤ (⟨1⟩ : Pos.Raw))
    (hsz : c.utf8Size = 1) (hne : (sep == "") = false) (cs : List Char) :
    (String.ofList cs).splitOn sep = (cs.splitOn c).map String.ofList := by
  have h := splitOnAux_one sep c hget hnext hend hsz [] [] cs []
  simp only [List.nil_append, utf8Len_nil, Nat.add_zero, List.reverse_nil] at h
  unfold String.splitOn
  rw [hne, List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact h

theorem splitOn_bar (cs : List Char) : (String.ofList cs).splitOn "|" = (cs.splitOn '|').map String.ofList :=
  splitOn_one "|" '|' rfl rfl (by decide) rfl (by decide) cs

theorem splitOn_semi (cs : List Char) : (String.ofList cs).splitOn ";" = (cs.splitOn ';').map String.ofList :=
  splitOn_one ";" ';' rfl rfl (by decide) rfl (by decide) cs

theorem splitOn_eqs (cs : List Char) : (String.ofList cs).splitOn "=" = (cs.splitOn '=').map String.ofList :=
  splitOn_one "=" '=' rfl rfl (by decide) rfl (by decide) cs

theorem splitOn_caret (cs : List Char) :
    (String.ofList cs).splitOn "^" = (cs.splitOn '^').map String.ofList :=
  splitOn_one "^" '^' rfl rfl (by decide) rfl (by decide) cs

theorem splitOn_space (cs : List Char) :
    (String.ofList cs).splitOn " " = (cs.splitOn ' ').map String.ofList :=
  splitOn_one " " ' ' rfl rfl (by decide) rfl (by decide) cs

@[expose] def OkC (S : List Char) (l : List Char) : Prop := ∀ x ∈ l, x.isDigit = true ∨ x ∈ S

theorem OkC.not_mem {S l : List Char} (h : OkC S l) {c : Char} (hd : c.isDigit = false) (hS : c ∉ S) :
    c ∉ l := fun hc => by
  rcases h c hc with h | h
  · rw [hd] at h
    exact Bool.false_ne_true h
  · exact hS h

theorem OkC.mono {S T l : List Char} (h : OkC S l) (hST : ∀ x ∈ S, x ∈ T) : OkC T l :=
  fun x hx => (h x hx).imp_right (hST x)

theorem digK_ok (S : List Char) : ∀ (f n : Nat) (ds : List Char), OkC S ds → OkC S (digK f n ds)
  | 0, _, _, h => h
  | f + 1, n, ds, h => by
    have hdig : ∀ d, d < 10 → (digC d).isDigit = true := by
      intro d hd
      interval_cases d <;> rfl
    have h1 : OkC S (digC (Nat.mod n 10) :: ds) := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl (hdig _ (Nat.mod_lt _ (by omega)))
      · exact h x hx
    change OkC S (Bool.rec (motive := fun _ => List Char)
      (digK f (Nat.div n 10) (digC (Nat.mod n 10) :: ds))
      (digC (Nat.mod n 10) :: ds) (Nat.beq (Nat.div n 10) 0))
    cases Nat.beq (Nat.div n 10) 0
    · exact digK_ok S f _ _ h1
    · exact h1

theorem natC_ok (S : List Char) (n : Nat) : OkC S (natC n) :=
  digK_ok S _ _ _ fun _ h => absurd h (List.not_mem_nil)

theorem intC_ok {S : List Char} (hS : '-' ∈ S) (e : Int) : OkC S (intC e) := by
  cases e with
  | ofNat m => exact natC_ok S m
  | negSucc m =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inr hS
    · exact natC_ok S _ x hx

theorem intercalate_ok {S sep : List Char} (hs : OkC S sep) :
    ∀ {xs : List (List Char)}, (∀ l ∈ xs, OkC S l) → OkC S (sep.intercalate xs)
  | [], _ => by simp [OkC]
  | [l], h => by simpa using h l (by simp)
  | l :: l' :: zs, h => by
    rw [List.intercalate_cons_cons]
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact h l (by simp) x hx
    · exact hs x hx
    · exact intercalate_ok hs (fun m hm => h m (List.mem_cons_of_mem _ hm)) x hx

theorem sep_ok {S : List Char} {c : Char} (h : c ∈ S) : OkC S [c] := by
  intro x hx
  rw [List.mem_singleton.1 hx]
  exact Or.inr h

theorem factC_ok {S : List Char} (h1 : '-' ∈ S) (h2 : '^' ∈ S) (f : Nat × Int) : OkC S (factC f) := by
  unfold factC
  split_ifs
  · exact natC_ok S _
  · refine intercalate_ok (sep_ok h2) ?_
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact natC_ok S _
    · exact intC_ok h1 _

theorem facts_ok {S : List Char} (h1 : '-' ∈ S) (h2 : '^' ∈ S) (h3 : ' ' ∈ S) (fs : List (Nat × Int)) :
    OkC S ([' '].intercalate (fs.map factC)) :=
  intercalate_ok (sep_ok h3) fun l hl => by
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hl
    exact factC_ok h1 h2 f

theorem lineC_ok {S : List Char} (h1 : '-' ∈ S) (h2 : '^' ∈ S) (h3 : ' ' ∈ S) (h4 : '=' ∈ S)
    (l : Nat × List (Nat × Int)) : OkC S (lineC l) := by
  unfold lineC
  refine intercalate_ok (sep_ok h4) ?_
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact natC_ok S _
  · exact facts_ok h1 h2 h3 _

theorem digK_ne_nil : ∀ (f n : Nat) (ds : List Char), ds ≠ [] → digK f n ds ≠ []
  | 0, _, _, h => h
  | f + 1, n, ds, _ => by
    change Bool.rec (motive := fun _ => List Char)
      (digK f (Nat.div n 10) (digC (Nat.mod n 10) :: ds))
      (digC (Nat.mod n 10) :: ds) (Nat.beq (Nat.div n 10) 0) ≠ []
    cases Nat.beq (Nat.div n 10) 0
    · exact digK_ne_nil f _ _ (List.cons_ne_nil _ _)
    · exact List.cons_ne_nil _ _

theorem digC_eq {d : Nat} (hd : d < 10) : digC d = d.digitChar := by
  interval_cases d
  · exact (Nat.digitChar_eq_zero.2 rfl).symm
  · exact (Nat.digitChar_eq_one.2 rfl).symm
  · exact (Nat.digitChar_eq_two.2 rfl).symm
  · exact (Nat.digitChar_eq_three.2 rfl).symm
  · exact (Nat.digitChar_eq_four.2 rfl).symm
  · exact (Nat.digitChar_eq_five.2 rfl).symm
  · exact (Nat.digitChar_eq_six.2 rfl).symm
  · exact (Nat.digitChar_eq_seven.2 rfl).symm
  · exact (Nat.digitChar_eq_eight.2 rfl).symm
  · exact (Nat.digitChar_eq_nine.2 rfl).symm

theorem digK_eq : ∀ (f n : Nat) (ds : List Char), n < f → digK f n ds = Nat.toDigits 10 n ++ ds
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, n, ds, h => by
    change Bool.rec (motive := fun _ => List Char)
      (digK f (n / 10) (digC (n % 10) :: ds))
      (digC (n % 10) :: ds) (Nat.beq (n / 10) 0) = _
    rw [Nat.toDigits_eq_ite (by omega), digC_eq (Nat.mod_lt _ (by omega))]
    by_cases h0 : n / 10 = 0
    · have hb : Nat.beq (n / 10) 0 = true := Nat.beq_eq_true_eq _ _ ▸ h0
      have hn : n < 10 := by omega
      rw [hb, ite_eq_left hn, Nat.mod_eq_of_lt hn]
      rfl
    · have hb : Nat.beq (n / 10) 0 = false := by
        cases h' : Nat.beq (n / 10) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') h0
      have hn : ¬ n < 10 := by omega
      rw [hb, ite_eq_right hn, List.append_assoc]
      exact digK_eq f _ _ (by omega)

theorem natC_eq (n : Nat) : String.ofList (natC n) = Nat.repr n := by
  rw [natC, digK_eq _ _ _ (Nat.lt_succ_self n), List.append_nil, Nat.repr_eq_ofList_toDigits]

theorem natC_toNat (n : Nat) : (String.ofList (natC n)).toNat? = some n := by
  rw [natC_eq, Nat.toNat?_repr]

theorem intC_toInt (e : Int) : (String.ofList (intC e)).toInt? = some e := by
  cases e with
  | ofNat m => exact String.toInt?_eq_some_of_toNat?_eq_some (natC_toNat m)
  | negSucc m =>
    have h : String.ofList (intC (Int.negSucc m)) = "-" ++ String.ofList (natC (m + 1)) := by
      have hs : String.singleton '-' = "-" := by decide
      change String.ofList ('-' :: natC (m + 1)) = _
      rw [String.ofList_cons, hs]
    rw [h, String.toInt?_minus_append, natC_toNat]
    rfl

theorem natC_ne_nil (n : Nat) : natC n ≠ [] := by
  change Bool.rec (motive := fun _ => List Char)
    (digK n (Nat.div n 10) [digC (Nat.mod n 10)]) [digC (Nat.mod n 10)] (Nat.beq (Nat.div n 10) 0) ≠ []
  cases Nat.beq (Nat.div n 10) 0
  · exact digK_ne_nil _ _ _ (List.cons_ne_nil _ _)
  · exact List.cons_ne_nil _ _

theorem filter_pieces {xs : List (List Char)} (hne : ∀ l ∈ xs, l ≠ []) :
    (xs.map String.ofList).filter (fun s => decide (s ≠ "")) = xs.map String.ofList := by
  rw [List.filter_eq_self]
  intro s hs
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hs
  simpa [String.ofList_eq_empty_iff] using hne l hl

theorem pieces {c : Char} {xs : List (List Char)} (hx : ∀ l ∈ xs, c ∉ l) (hne : ∀ l ∈ xs, l ≠ []) :
    ((([c].intercalate xs).splitOn c).map String.ofList).filter (fun s => decide (s ≠ "")) =
      xs.map String.ofList := by
  by_cases h : xs = []
  · subst h
    simp
  · rw [List.splitOn_intercalate c hx h]
    exact filter_pieces hne

theorem pieces2 {c : Char} {a b : List Char} (ha : c ∉ a) (hb : c ∉ b) :
    ([c].intercalate [a, b]).splitOn c = [a, b] :=
  List.splitOn_intercalate c (by simp [ha, hb]) (by simp)

theorem parseFactor_factC (f : Nat × Int) : parseFactor (String.ofList (factC f)) = f := by
  obtain ⟨r, e⟩ := f
  have hr : '^' ∉ natC r := (natC_ok [] r).not_mem rfl (by simp)
  unfold factC parseFactor
  by_cases he : e = 1
  · subst he
    simp only [ite_true]
    rw [splitOn_caret, List.splitOn_eq_singleton hr]
    simp only [List.map_cons, List.map_nil, natC_toNat, Option.getD_some]
  · simp only [ite_eq_right he]
    have he' : '^' ∉ intC e := (intC_ok (S := ['-']) (by simp) e).not_mem rfl (by simp)
    rw [splitOn_caret, pieces2 hr he']
    simp only [List.map_cons, List.map_nil, natC_toNat, intC_toInt, Option.getD_some]

theorem parseFacts (fs : List (Nat × Int)) :
    ((((String.ofList ([' '].intercalate (fs.map factC))).splitOn " ").filter (· ≠ "")).map
      parseFactor) = fs := by
  rw [splitOn_space, pieces]
  · rw [List.map_map, List.map_map]
    conv_rhs => rw [← List.map_id fs]
    congr 1
    funext f
    exact parseFactor_factC f
  · intro l hl
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hl
    exact (factC_ok (S := ['-', '^']) (by simp) (by simp) f).not_mem rfl (by simp)
  · intro l hl
    obtain ⟨⟨r, e⟩, -, rfl⟩ := List.mem_map.1 hl
    unfold factC
    split_ifs
    · exact natC_ne_nil r
    · simp [natC_ne_nil]

theorem parseLine_lineC (l : Nat × List (Nat × Int)) : parseLine (String.ofList (lineC l)) = l := by
  obtain ⟨d, fs⟩ := l
  unfold lineC parseLine
  have hd : '=' ∉ natC d := (natC_ok [] d).not_mem rfl (by simp)
  have hf : '=' ∉ [' '].intercalate (fs.map factC) :=
    (facts_ok (S := ['-', '^', ' ']) (by simp) (by simp) (by simp) fs).not_mem rfl (by simp)
  rw [splitOn_eqs, pieces2 hd hf]
  simp only [List.map_cons, List.map_nil, natC_toNat, Option.getD_some]
  rw [parseFacts]

theorem parseSLP_slpC (p : SLP) : parseSLP (String.ofList (slpC p)) = p := by
  obtain ⟨ls, os⟩ := p
  unfold slpC parseSLP
  have hb : '|' ∉ [';'].intercalate (ls.map lineC) :=
    (intercalate_ok (S := ['-', '^', ' ', '=', ';']) (sep_ok (by simp)) (fun m hm => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hm
      exact lineC_ok (by simp) (by simp) (by simp) (by simp) l)).not_mem rfl (by simp)
  have ho : '|' ∉ [' '].intercalate (os.map factC) :=
    (facts_ok (S := ['-', '^', ' ']) (by simp) (by simp) (by simp) os).not_mem rfl (by simp)
  rw [splitOn_bar, pieces2 hb ho]
  simp only [List.map_cons, List.map_nil]
  rw [splitOn_semi, pieces, parseFacts]
  · rw [List.map_map, List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id ls]
    congr 1
    funext l
    exact parseLine_lineC l
  · intro m hm
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hm
    exact (lineC_ok (S := ['-', '^', ' ', '=']) (by simp) (by simp) (by simp) (by simp) l).not_mem
      rfl (by simp)
  · intro m hm
    obtain ⟨⟨d, fs⟩, -, rfl⟩ := List.mem_map.1 hm
    unfold lineC
    simp [natC_ne_nil]

theorem charsEq_sound : ∀ {a b : List Char}, charsEq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: a, y :: b, h => by
    change Bool.rec (motive := fun _ => Bool) false (charsEq a b) (Nat.beq x.toNat y.toNat) = true at h
    cases hxy : Nat.beq x.toNat y.toNat
    · rw [hxy] at h
      exact absurd h Bool.false_ne_true
    · rw [hxy] at h
      rw [Char.toNat_inj.1 (Nat.eq_of_beq_eq_true hxy), charsEq_sound h]

end CFSG.KC.G13

end
