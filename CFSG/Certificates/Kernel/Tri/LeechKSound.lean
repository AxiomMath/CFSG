module

public import Certificates.Data.Kernel.Tri.LeechK
public import CFSG.Monster.Tri.LeechLongCheckInputs
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.LenSound
public import CFSG.Certificates.Kernel.Spor.TextAtSound

public section

namespace CFSG.KC.Leech

open CFSG.KLie.CT CFSG.Monster.Tri.Leech

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, beq_iff_eq])

theorem blt_eq (a b : Nat) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.blt_eq, decide_eq_true_iff])

theorem allN_true (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem allN_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) : allN n f = allN n g :=
  Bool.eq_iff_iff.2 (by
    rw [allN_true, allN_true]
    exact forall₂_congr fun i hi => by rw [h i hi])

theorem allFrom_true {o m : Nat} {f : Nat → Bool} (h : allFrom o m f = true) :
    ∀ i, o ≤ i → i < o + m → f i = true := by
  intro i h1 h2
  have := (allN_true m _).1 h (i - o) (by omega)
  rwa [Nat.add_eq, Nat.add_sub_cancel' h1] at this

theorem range_all (n : Nat) (f : Nat → Bool) : (List.range n).all f = allN n f :=
  Bool.eq_iff_iff.2 (by rw [List.all_eq_true, allN_true]; simp [List.mem_range])

theorem toList_all (a : Array Nat) (f : Nat → Bool) : a.toList.all f = allN a.size fun i => f a[i]! :=
  Bool.eq_iff_iff.2 (by
    rw [List.all_eq_true, allN_true]
    constructor
    · intro h i hi
      rw [getElem!_pos a i hi]
      exact h _ (Array.getElem_mem_toList hi)
    · intro h x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
      have := h i (by simpa using hi)
      rwa [getElem!_pos a i (by simpa using hi)] at this)

theorem getK_eq : ∀ (l : List Nat) (i : Nat), getK l i = l[i]!
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: l, i + 1 => by
    change getK l i = (a :: l)[i + 1]!
    rw [getK_eq l i]
    simp

theorem arr_getK (a : Array Nat) (i : Nat) : a[i]! = getK a.toList i := by
  rw [getK_eq]
  rcases a with ⟨l⟩
  by_cases h : i < l.length
  · rw [getElem!_pos _ i (by simpa using h), getElem!_pos l i h]
    rfl
  · rw [getElem!_neg _ i (by simpa using h), getElem!_neg l i h]

theorem memL_iff (l : List Nat) (x : Nat) : memL l x = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memL]
  | cons a l ih =>
    change orB (Nat.beq a x) (memL l x) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih, Nat.beq_eq, List.mem_cons]
    exact ⟨fun h => h.elim (fun e => Or.inl e.symm) Or.inr,
      fun h => h.elim (fun e => Or.inl e.symm) Or.inr⟩

section Checks

variable {klev : ByteArray} {vs par lev : Array Nat} {n : Nat} {V PA LV : Nat → Nat}

theorem treeOK_eq (hv : vs.size = n)
    (eV : ∀ i < n, vs[i]! = V i) (eP : ∀ i < n, par[i]! = PA i) (eL : ∀ i < n, lev[i]! = LV i) :
    CFSG.Monster.Tri.Leech.treeOK klev vs par lev = allN n (treeAt (shortHit klev) n V PA LV) := by
  unfold CFSG.Monster.Tri.Leech.treeOK
  rw [hv, range_all]
  refine allN_congr fun i hi => ?_
  unfold treeAt
  rw [eP i hi, eV i hi, eL i hi, orB_eq, andB_eq, andB_eq, beq_eq, beq_eq, blt_eq]
  by_cases hpi : PA i < n
  · rw [eL _ hpi, eV _ hpi, Bool.and_assoc]
    rfl
  · simp [hpi]

theorem long_eq (hv : vs.size = n)
    (eV : ∀ i < n, vs[i]! = V i) (eP : ∀ i < n, par[i]! = PA i) (eL : ∀ i < n, lev[i]! = LV i)
    (w : Nat) :
    (CFSG.Monster.Tri.Leech.treeOK klev vs par lev && treeNeOK vs par w) =
      allN n (longAt (shortHit klev) n w V PA LV) := by
  rw [treeOK_eq hv eV eP eL]
  unfold treeNeOK
  rw [hv, range_all]
  refine Bool.eq_iff_iff.2 ?_
  rw [Bool.and_eq_true, allN_true, allN_true, allN_true]
  have key : ∀ i < n, (treeAt (shortHit klev) n V PA LV i = true ∧
      (i == 0 || vs[i]! ^^^ vs[par[i]!]! != w) = true) ↔
        longAt (shortHit klev) n w V PA LV i = true := by
    intro i hi
    unfold treeAt longAt
    rw [eV i hi, eP i hi]
    by_cases h0 : i = 0
    · subst h0
      simp [orB_eq]
    · by_cases hpi : PA i < n
      · rw [eV _ hpi]
        simp only [orB_eq, andB_eq, notB_eq, beq_eq, blt_eq, Bool.or_eq_true, Bool.and_eq_true,
          beq_iff_eq, h0, false_or, decide_eq_true_iff, bne_iff_ne, ne_eq, Bool.not_eq_true']
        constructor
        · rintro ⟨⟨a1, a2, a3⟩, a4⟩
          refine ⟨a1, a2, a3, ?_⟩
          simpa using a4
        · rintro ⟨a1, a2, a3, a4⟩
          refine ⟨⟨a1, a2, a3⟩, ?_⟩
          simpa using a4
      · simp [orB_eq, andB_eq, blt_eq, h0, hpi]
  exact ⟨fun ⟨h1, h2⟩ i hi => (key i hi).1 ⟨h1 i hi, h2 i hi⟩,
    fun h => ⟨fun i hi => ((key i hi).2 (h i hi)).1, fun i hi => ((key i hi).2 (h i hi)).2⟩⟩

theorem sortedOK_eq (hv : vs.size = n) (eV : ∀ i < n, vs[i]! = V i) :
    sortedOK vs = allN n (sortedAt n V) := by
  unfold sortedOK
  rw [hv, range_all]
  refine allN_congr fun i hi => ?_
  unfold sortedAt
  rw [orB_eq, beq_eq, blt_eq]
  by_cases h : i + 1 = n
  · simp [h]
  · rw [eV i hi, eV (i + 1) (by omega)]

theorem nbrOK_eq {nbr : Array Nat} {NB : Nat → Nat} (hv : nbr.size = 4600)
    (eV : ∀ i < 4600, nbr[i]! = NB i) :
    nbrOK klev nbr =
      andB (allN 4600 (sortedAt 4600 NB)) (allN 4600 (nbrAt (shortHit klev) NB)) := by
  unfold nbrOK
  rw [sortedOK_eq hv eV, hv, range_all, andB_eq]
  have e : allN 4600 (fun i => shortHit klev nbr[i]! && shortHit klev (nbr[i]! ^^^ 12288)) =
      allN 4600 (nbrAt (shortHit klev) NB) := by
    refine allN_congr fun i hi => ?_
    unfold nbrAt
    rw [eV i hi, andB_eq]
    rfl
  rw [e, beq_self_eq_true, Bool.true_and]

theorem muOK_eq {nbr : Array Nat} {NB W : Nat → Nat} {m b : Nat} (hn : nbr.size = n)
    (eN : ∀ i < n, nbr[i]! = NB i) (hm : vs.size = m) (eW : ∀ i < m, vs[i]! = W i) :
    muOK klev nbr b vs = andB (allN m (sortedAt m W))
      (andB (allN m (muVsAt (shortHit klev) b W))
        (allN n (muNbrAt (shortHit klev) b NB vs.toList))) := by
  unfold muOK
  rw [sortedOK_eq hm eW, toList_all, toList_all, hm, hn, andB_eq, andB_eq, Bool.and_assoc]
  congr 2
  · refine allN_congr fun i hi => ?_
    unfold muVsAt
    rw [eW i hi, andB_eq, andB_eq, Bool.and_assoc]
    rfl
  · refine allN_congr fun i hi => ?_
    unfold muNbrAt
    rw [eN i hi, orB_eq, notB_eq]
    congr 1
    exact Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff, memL_iff])

end Checks

theorem hexNum_eq (b : ByteArray) (o : Nat) :
    ∀ w, CFSG.Monster.Tri.Leech.hexNum b o w = CFSG.Monster.B.Co2.Native.hexAt b o w
  | 0 => rfl
  | w + 1 => by
    unfold CFSG.Monster.Tri.Leech.hexNum
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := hexNum_eq b o w
    unfold CFSG.Monster.Tri.Leech.hexNum at ih
    rw [ih]
    rfl

theorem toUTF8_size {cs : List Char} (h : ∀ c ∈ cs, c.toNat < 128) :
    (String.ofList cs).toUTF8.size = cs.length := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode,
    CFSG.KS.Text.flatMap_ascii' cs h, List.size_toByteArray, List.length_map]

theorem hexTable_bind {cs : List Char} {d n w N : Nat} {F : Nat → Nat}
    (h : CFSG.KC.Misc.HexFlat.hexFlat cs d n w N F = true)
    (hl : CFSG.KS.Len.lenK cs = d * (n * N)) (ha : CFSG.KS.Text.asciiK cs = true) :
    (CFSG.Monster.Tri.Leech.hexTable d (String.ofList cs)).size = n * N ∧
      ∀ x < n * N, (CFSG.Monster.Tri.Leech.hexTable d (String.ofList cs))[x]! =
        CFSG.KC.Enum.pg w (CFSG.KS.mask w) (F (x / n)) (x % n) := by
  have hd : 0 < d ∧ 0 < n := by
    unfold CFSG.KC.Misc.HexFlat.hexFlat at h
    have h' : andB (Nat.blt 0 d) (andB (Nat.blt 0 n)
        (CFSG.KC.Misc.HexFlat.run d n w N F cs 0 0 0 0 0)) = true := h
    simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h'
    exact ⟨h'.1, h'.2.1⟩
  rw [CFSG.KS.Len.lenK_eq] at hl
  have hsz : (String.ofList cs).toUTF8.size = d * (n * N) := by
    rw [toUTF8_size (CFSG.KS.Text.asciiK_spec ha), hl]
  have hs : (CFSG.Monster.Tri.Leech.hexTable d (String.ofList cs)).size = n * N := by
    simp only [CFSG.Monster.Tri.Leech.hexTable, Array.size_ofFn, hsz]
    exact Nat.mul_div_cancel_left _ hd.1
  refine ⟨hs, fun x hx => ?_⟩
  have hj : x / n < N := (Nat.div_lt_iff_lt_mul hd.2).2 (by rw [Nat.mul_comm]; exact hx)
  have hi : x % n < n := Nat.mod_lt _ hd.2
  have e := congrArg (fun a => a[x % n]!) (CFSG.KC.Misc.HexFlat.hexTable_sound h (x / n) hj)
  simp only [CFSG.Monster.B.Co2.Native.hexTable, CFSG.KS.Raw.unpack] at e
  rw [getElem!_pos _ _ (by simpa using hi), getElem!_pos _ _ (by simpa using hi),
    Array.getElem_ofFn, Array.getElem_ofFn] at e
  rw [getElem!_pos _ _ (by rw [hs]; exact hx)]
  simp only [CFSG.Monster.Tri.Leech.hexTable, Array.getElem_ofFn]
  rw [hexNum_eq, ← e, Nat.div_add_mod]

end CFSG.KC.Leech

end
