module

public import Certificates.Data.Kernel.SporSch.TitsGraph
public import CFSG.Certificates.Kernel.SporSch.TitsPrimSound
public import CFSG.Sporadic.Schreier.TitsGraphCheckInputs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits
open CFSG.SectionRank.Native.Tits (bsearch)

@[expose] def nbrDataG (n m : ℕ) (L : Array ℕ) : Array (List (ℕ × ℕ)) :=
  (List.range m).foldl (fun acc v =>
    [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)].foldl (fun acc kk =>
      acc.modify L[3 * v + kk.1]! fun l => l ++ [(L[3 * v + kk.2]!, v)])
      acc) (Array.replicate n [])

theorem titsNbrData_eq : titsNbrData = nbrDataG 1755 2925 titsLinePtArr := rfl

@[expose] def nbrRow (l : List (ℕ × ℕ)) : Array ℕ :=
  ((l.map Prod.fst).mergeSort fun a b => decide (a ≤ b)).toArray

@[expose] def lineRow (l : List (ℕ × ℕ)) : Array ℕ :=
  ((l.mergeSort fun a b => decide (a.1 ≤ b.1)).map Prod.snd).toArray

theorem titsNbr_eq : titsNbr = titsNbrData.map nbrRow := rfl

theorem titsNbrLine_eq : titsNbrLine = titsNbrData.map lineRow := rfl

@[expose] def nbrColorsG (nbr : Array (Array ℕ)) (col : Array ℕ) (x : ℕ) : List ℕ :=
  ((nbr[x]!).toList.map fun w => col[w]!).mergeSort fun a b => decide (a ≤ b)

@[expose] def sigCodeG (B : ℕ) (nbr : Array (Array ℕ)) (col : Array ℕ) (x : ℕ) : ℕ :=
  (nbrColorsG nbr col x).foldl (fun acc a => acc * B + a) col[x]!

@[expose] def refineStepG (n B : ℕ) (nbr : Array (Array ℕ)) (col : Array ℕ) : Array ℕ :=
  relabel (Array.ofFn (n := n) fun x => sigCodeG B nbr col x)

theorem refineStep_eq : refineStep = refineStepG 1755 1756 titsNbr := rfl

private theorem strictB_eqG (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem blt_iffG {a b : Nat} : Nat.blt a b = true ↔ a < b := by
  simp [Nat.blt_eq]

private theorem beq_iffG {a b : Nat} : Nat.beq a b = true ↔ a = b := by
  simp

private theorem mem_dedupSorted : ∀ (l : List ℕ) (a : ℕ), a ∈ dedupSorted l ↔ a ∈ l
  | a :: b :: l, x => by
    rw [dedupSorted]
    split_ifs with h
    · rw [mem_dedupSorted (b :: l) x, h]
      simp
    · rw [List.mem_cons, mem_dedupSorted (b :: l) x]
      simp
  | [], _ => Iff.rfl
  | [_], _ => Iff.rfl

private theorem dedupSorted_lt : ∀ (l : List ℕ), l.Pairwise (· ≤ ·) →
    (dedupSorted l).Pairwise (· < ·)
  | a :: b :: l, hl => by
    rw [dedupSorted]
    have ht := dedupSorted_lt (b :: l) hl.of_cons
    split_ifs with h
    · exact ht
    · refine List.Pairwise.cons (fun x hx => ?_) ht
      rw [mem_dedupSorted] at hx
      have hab : a ≤ b := List.rel_of_pairwise_cons hl List.mem_cons_self
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := List.rel_of_pairwise_cons hl.of_cons hx
        omega
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _

private theorem sorted_le (l : List ℕ) : (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) :=
  (List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) l).imp
    (fun h => by simpa using h)

private theorem numCells_eq (v : Array ℕ) : numCells v = v.toList.toFinset.card := by
  unfold numCells sortedValues
  rw [List.size_toArray]
  have hn := (dedupSorted_lt _ (sorted_le v.toList)).imp (fun h => Nat.ne_of_lt h)
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext a
  simp only [List.mem_toFinset, mem_dedupSorted, List.mem_mergeSort]

private theorem numK_values {n w C k REP : Nat} (h : numK n w C k REP = true) :
    (unpack n w C).toList.toFinset = Finset.range k := by
  unfold numK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  ext c
  simp only [List.mem_toFinset, Finset.mem_range, Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x < n := by simpa [unpack] using hx
    have := blt_iffG.1 (allN_spec h1 x hx')
    rw [pgW_eq] at this
    simpa [unpack] using this
  · intro hc
    have := allN_spec h2 c hc
    rw [strictB_eqG] at this
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 this
    have a := blt_iffG.1 a
    have b := beq_iffG.1 b
    rw [pgW_eq] at b
    exact ⟨_, by simpa [unpack] using a, by simpa [unpack] using b⟩

theorem numK_sound {n w C k REP : Nat} (h : numK n w C k REP = true) :
    numCells (unpack n w C) = k := by
  rw [numCells_eq, numK_values h, Finset.card_range]

theorem distK_sound {n w C REP : Nat} (h : numK n w C n REP = true) :
    ((unpack n w C).toList.mergeSort fun a b => decide (a ≤ b)).Pairwise (· < ·) := by
  have hv := numK_values h
  have hnd : (unpack n w C).toList.Nodup := by
    have e : (((unpack n w C).toList : Multiset ℕ).toFinset).card =
        Multiset.card ((unpack n w C).toList : Multiset ℕ) := by
      change ((unpack n w C).toList.toFinset).card = _
      rw [hv, Finset.card_range, Multiset.coe_card]
      simp [unpack]
    exact Multiset.coe_nodup.1 (Multiset.toFinset_card_eq_card_iff_nodup.1 e)
  have hn : ((unpack n w C).toList.mergeSort fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.2 hnd
  exact ((sorted_le _).and hn).imp fun ⟨h1, h2⟩ => Nat.lt_of_le_of_ne h1 h2

private theorem forIn_invB {β : Type} (R : Nat → β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    ∀ k a (init : β), a + k ≤ E → R a init → R (a + k) (forIn (List.range' a k) init f)
  | 0, _, _, _, h => h
  | k + 1, a, init, hE, h => by
    obtain ⟨b', hb, hR⟩ := hf a init (by omega) h
    rw [List.range'_succ, List.forIn_cons, hb]
    have e : a + (k + 1) = a + 1 + k := by omega
    rw [e]
    exact forIn_invB R E f hf k (a + 1) b' (by omega) hR

private theorem forIn_rngB {β : Type} (k : Nat) (init : β) (f : Nat → β → Id (ForInStep β)) :
    forIn (m := Id) [0:k] init f = forIn (List.range' 0 k) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hl : List.range' [0:k].start [0:k].size [0:k].step = List.range' 0 k := by
    simp [Std.Legacy.Range.size]
  rw [hl]

private theorem bsearch_get {pts : Array Nat} (hs : ∀ i j, i < j → j < pts.size → pts[i]! < pts[j]!)
    (hsz : pts.size < 2 ^ 64) {c : Nat} (hc : c < pts.size) : bsearch pts pts[c]! = c := by
  have hmono : ∀ i j, i ≤ j → j < pts.size → pts[i]! ≤ pts[j]! := fun i j hij hj => by
    rcases Nat.lt_or_eq_of_le hij with h | rfl
    · exact Nat.le_of_lt (hs i j h hj)
    · exact Nat.le_refl _
  let v := pts[c]!
  let R : Nat → Nat × Nat → Prop := fun j s => s.1 ≤ s.2 ∧ s.2 ≤ pts.size ∧
    (∀ i < s.1, pts[i]! < v) ∧ (∀ i, s.2 ≤ i → i < pts.size → v ≤ pts[i]!) ∧
    s.2 - s.1 ≤ pts.size / 2 ^ j
  have step : ∀ j (s : Nat × Nat), j < 64 → R j s → ∃ b',
      (if s.fst < s.snd then
        if pts[(s.fst + s.snd) / 2]! < v then
          (pure (ForInStep.yield ((s.fst + s.snd) / 2 + 1, s.snd)) : Id (ForInStep (Nat × Nat)))
        else pure (ForInStep.yield (s.fst, (s.fst + s.snd) / 2))
      else pure (ForInStep.yield (s.fst, s.snd))) = pure (.yield b') ∧ R (j + 1) b' := by
    intro j ⟨lo, hi⟩ _ ⟨h1, h2, h3, h4, h5⟩
    have hd : pts.size / 2 ^ (j + 1) = pts.size / 2 ^ j / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    simp only at h1 h2 h3 h4 h5 ⊢
    by_cases hlt : lo < hi
    · rw [ite_eq_left hlt]
      by_cases hm : pts[(lo + hi) / 2]! < v
      · rw [ite_eq_left hm]
        refine ⟨_, rfl, by omega, h2, fun i hi' => ?_, h4, ?_⟩
        · rcases Nat.lt_or_ge i lo with h | h
          · exact h3 i h
          · exact Nat.lt_of_le_of_lt (hmono i _ (by omega) (by omega)) hm
        · rw [hd]
          omega
      · rw [ite_eq_right hm]
        refine ⟨_, rfl, by omega, by omega, h3, fun i hi' hi2 => ?_, ?_⟩
        · exact Nat.le_trans (Nat.le_of_not_lt hm) (hmono _ i hi' hi2)
        · rw [hd]
          omega
    · rw [ite_eq_right hlt]
      exact ⟨_, rfl, h1, h2, h3, h4, by omega⟩
  unfold bsearch
  simp only [Id.run]
  have hR := forIn_invB R 64 _ step 64 0 (0, pts.size) (by omega)
    ⟨Nat.zero_le _, Nat.le_refl _, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi hi' => absurd hi' (by omega), by simp⟩
  rw [← forIn_rngB] at hR
  generalize forIn (m := Id) [0:64] (0, pts.size) _ = s at hR ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  have h0 : pts.size / 2 ^ (0 + 64) = 0 := Nat.div_eq_of_lt (by simpa using hsz)
  rw [h0] at h5
  have hlo : s.1 = c := by
    rcases Nat.lt_trichotomy s.1 c with h | h | h
    · have := h4 s.1 (by omega) (by omega)
      have := hs s.1 c h hc
      omega
    · exact h
    · have := h3 c h
      omega
  change (if (decide (s.1 < pts.size) && pts[s.1]! == pts[c]!) = true then s.1 else pts.size) = c
  rw [hlo]
  simp [hc]

private theorem bIf_imp {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    c = true → t = true := by
  cases c
  · intro h'
    exact absurd h' Bool.false_ne_true
  · intro _
    exact h

private theorem testBit_orRec (g : Nat → Nat) : ∀ m i,
    (Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.lor acc (Nat.shiftLeft 1 (g j))) m).testBit
      i = true → ∃ j < m, g j = i
  | 0, i, h => by
    change Nat.testBit 0 i = true at h
    simp at h
  | m + 1, i, h => by
    change (Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Nat.lor acc (Nat.shiftLeft 1 (g j))) m ||| 1 <<< g m).testBit i = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, e⟩ := testBit_orRec g m i h
      exact ⟨j, by omega, e⟩
    · refine ⟨m, by omega, ?_⟩
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h
      simpa using h

private theorem foldl_range_rec (init B : Nat) (g : Nat → Nat) : ∀ m,
    ((List.range m).map g).foldl (fun acc a => acc * B + a) init =
      Nat.rec (motive := fun _ => Nat) init (fun j acc => Nat.add (Nat.mul acc B) (g j)) m
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append, foldl_range_rec init B g m]
    rfl

private theorem smono_of_adj {d : Nat} {g : Nat → Nat} (h : ∀ j, j + 1 < d → g j < g (j + 1)) :
    ∀ i j, i < j → j < d → g i < g j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
    · exact Nat.lt_trans (ih hij (by omega)) (h j hj)
    · exact h i hj

private theorem pairwise_lt_of_adj {d : Nat} {g : Nat → Nat}
    (h : ∀ j, j + 1 < d → g j < g (j + 1)) : ((List.range d).map g).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem fun {i j} _ hj hij =>
    smono_of_adj h i j hij (List.mem_range.1 hj)

private theorem pairwise_le_of_adj {d : Nat} {g : Nat → Nat} (h : ∀ j, j + 1 < d → g j ≤ g (j + 1)) :
    ((List.range d).map g).Pairwise (· ≤ ·) := by
  have hm : ∀ i j, i ≤ j → j < d → g i ≤ g j := by
    intro i j hij hj
    induction j with
    | zero =>
      have : i = 0 := by omega
      rw [this]
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hij) with hij' | rfl
      · exact Nat.le_trans (ih (by omega) (by omega)) (h j hj)
      · exact Nat.le_refl _
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem fun {i j} _ hj hij =>
    hm i j (Nat.le_of_lt hij) (List.mem_range.1 hj)

private theorem range_map_perm {d : Nat} {π : Nat → Nat} (hlt : ∀ j < d, π j < d)
    (hon : ∀ i < d, ∃ j < d, π j = i) : List.Perm ((List.range d).map π) (List.range d) := by
  have himg : (Finset.range d).image π = Finset.range d := by
    ext i
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hlt j hj
    · intro hi
      exact hon i hi
  have hinj : Set.InjOn π (Finset.range d) :=
    Finset.injOn_of_card_image_eq (by rw [himg])
  have hnd : ((List.range d).map π).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hinj (by simpa using ha) (by simpa using hb) e)
      List.nodup_range
  refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun i => ?_
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hlt j hj
  · exact hon i

theorem refK_sound {n d B w NB C C' SC PI REP k : Nat} {nbr : Array (Array ℕ)}
    (hn : nbr = Array.ofFn (n := n) (fun u => Array.ofFn (n := d) fun i => pgW w NB (d * u + i)))
    (h : refK n d B w NB C C' SC PI REP k = true) :
    refineStepG n B nbr (unpack n w C) = unpack n w C' := by
  unfold refK at h
  simp only [bAnd_iff] at h
  obtain ⟨hn32, -, hkn, hP, hR⟩ := h
  have hn32 : n < 4294967296 := blt_iffG.1 hn32
  have hkn : k ≤ n := Nat.le_of_ble_eq_true hkn
  have hPt : ∀ x < n, pgW w C' x < k ∧
      codeK B d w SC C x = codeK B d w SC C (pgW w REP (pgW w C' x)) ∧
      permBits d PI x = mask d ∧ ∀ j < d, pgW 4 PI (d * x + j) < d ∧
        pgW w NB (d * x + pgW 4 PI (d * x + j)) < n ∧
        pgW w SC (d * x + j) = pgW w C (pgW w NB (d * x + pgW 4 PI (d * x + j))) ∧
        (j + 1 < d → pgW w SC (d * x + j) ≤ pgW w SC (d * x + j + 1)) := by
    intro x hx
    have := allN_spec hP x hx
    unfold refPtK at this
    simp only [strictB_eqG, bAnd_iff] at this
    obtain ⟨h1, h2, h3, h4⟩ := this
    refine ⟨blt_iffG.1 h1, beq_iffG.1 h2, beq_iffG.1 h3, fun j hj => ?_⟩
    have := allN_spec h4 j hj
    unfold refNbK at this
    simp only [strictB_eqG, bAnd_iff] at this
    obtain ⟨a, b, c, e⟩ := this
    refine ⟨blt_iffG.1 a, blt_iffG.1 b, beq_iffG.1 c, fun hj1 => ?_⟩
    exact Nat.le_of_ble_eq_true (bIf_imp e (blt_iffG.2 hj1))
  have hRp : ∀ c < k, pgW w REP c < n ∧ pgW w C' (pgW w REP c) = c ∧
      (c + 1 < k → codeK B d w SC C (pgW w REP c) < codeK B d w SC C (pgW w REP (c + 1))) := by
    intro c hc
    have := allN_spec hR c hc
    unfold refRepK at this
    simp only [strictB_eqG, bAnd_iff] at this
    obtain ⟨a, b, e⟩ := this
    exact ⟨blt_iffG.1 a, beq_iffG.1 b, fun hc1 => blt_iffG.1 (bIf_imp e (blt_iffG.2 hc1))⟩
  have hcol : ∀ y < n, (unpack n w C)[y]! = pgW w C y := fun y hy => by
    rw [unpackW_get hy, pgW_eq]
  have hsig : ∀ x < n, sigCodeG B nbr (unpack n w C) x = codeK B d w SC C x := by
    intro x hx
    obtain ⟨-, -, hpb, hj⟩ := hPt x hx
    let π := fun j => pgW 4 PI (d * x + j)
    have hlt : ∀ j < d, π j < d := fun j hj' => (hj j hj').1
    have hon : ∀ i < d, ∃ j < d, π j = i := by
      intro i hi
      have hb : (permBits d PI x).testBit i = true := by
        rw [hpb]
        unfold mask
        change ((1 <<< d) - 1).testBit i = true
        rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
        simpa using hi
      exact testBit_orRec (fun j => pgW 4 PI (Nat.add (Nat.mul d x) j)) d i hb
    have hnb : ∀ i < d, pgW w NB (d * x + i) < n := by
      intro i hi
      obtain ⟨j, hj', rfl⟩ := hon i hi
      exact (hj j hj').2.1
    have hrow : (nbr[x]!).toList.map (fun y => (unpack n w C)[y]!) =
        (List.range d).map (fun i => pgW w C (pgW w NB (d * x + i))) := by
      rw [hn, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, Array.toList_ofFn]
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.length_map, List.length_ofFn] at h1
        rw [List.getElem_map, List.getElem_ofFn, List.getElem_map, List.getElem_range,
          hcol _ (hnb i h1)]
    let S := (List.range d).map (fun j => pgW w SC (d * x + j))
    have hS : S = ((List.range d).map π).map (fun i => pgW w C (pgW w NB (d * x + i))) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j hj'
      exact (hj j (List.mem_range.1 hj')).2.2.1
    have hperm : List.Perm S ((List.range d).map (fun i => pgW w C (pgW w NB (d * x + i)))) := by
      rw [hS]
      exact (range_map_perm hlt hon).map _
    have hsorted : S.Pairwise (· ≤ ·) := pairwise_le_of_adj fun j hj1 => (hj j (by omega)).2.2.2 hj1
    have hms : nbrColorsG nbr (unpack n w C) x = S := by
      unfold nbrColorsG
      rw [hrow]
      exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2)
        (sorted_le _) hsorted ((List.mergeSort_perm _ _).trans hperm.symm)
    unfold sigCodeG
    rw [hms, hcol x hx]
    exact foldl_range_rec _ B _ d
  let code := fun x => codeK B d w SC C x
  let T := (List.range k).map (fun c => code (pgW w REP c))
  have hT : T.Pairwise (· < ·) := pairwise_lt_of_adj fun j hj => (hRp j (by omega)).2.2 hj
  obtain ⟨v, hvd⟩ : ∃ v, v = Array.ofFn (n := n) fun x => sigCodeG B nbr (unpack n w C) x :=
    ⟨_, rfl⟩
  have hsv : (sortedValues v).toList = T := by
    unfold sortedValues
    rw [List.toList_toArray]
    have h1 := dedupSorted_lt _ (sorted_le v.toList)
    refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (Nat.lt_trans h1 h2)
      (Nat.lt_irrefl a)) h1 hT ?_
    refine (List.perm_ext_iff_of_nodup (h1.imp Nat.ne_of_lt) (hT.imp Nat.ne_of_lt)).2 fun a => ?_
    rw [mem_dedupSorted, List.mem_mergeSort]
    simp only [hvd, Array.toList_ofFn, List.mem_ofFn, T, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨h1, h2, -⟩ := hPt x hx
      exact ⟨_, h1, by rw [hsig x hx, h2]⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨h1, -, -⟩ := hRp c hc
      exact ⟨⟨_, h1⟩, hsig _ h1⟩
  unfold refineStepG relabel
  rw [← hvd]
  apply Array.ext
  · simp [hvd, unpack]
  · intro x h1 h2
    simp only [Array.size_map, hvd, Array.size_ofFn] at h1
    have hR : (unpack n w C')[x]'h2 = pgW w C' x := by
      simp only [unpack, Array.getElem_ofFn, pgW_eq]
    have hvx : v[x]'(by rw [hvd]; simpa using h1) = codeK B d w SC C x := by
      simp only [hvd, Array.getElem_ofFn]
      exact hsig x h1
    rw [Array.getElem_map, hvx, hR]
    obtain ⟨hc, hcode, -⟩ := hPt x h1
    have hTc : T[pgW w C' x]! = codeK B d w SC C x := by
      rw [getElem!_pos _ _ (by simpa [T] using hc)]
      simp only [T, List.getElem_map, List.getElem_range]
      exact hcode.symm
    have hsz : (sortedValues v).size = k := by
      rw [← Array.length_toList, hsv]
      simp [T]
    have hget : (sortedValues v)[pgW w C' x]! = T[pgW w C' x]! := by
      rw [getElem!_pos _ _ (by rw [hsz]; exact hc), getElem!_pos _ _ (by simpa [T] using hc),
        ← Array.getElem_toList]
      simp only [hsv]
    have hs : ∀ i j, i < j → j < (sortedValues v).size →
        (sortedValues v)[i]! < (sortedValues v)[j]! := by
      intro i j hij hj
      rw [getElem!_pos _ i (by omega), getElem!_pos _ j hj, ← Array.getElem_toList,
        ← Array.getElem_toList]
      simp only [hsv]
      exact List.pairwise_iff_getElem.1 hT i j _ _ hij
    rw [← hTc, ← hget]
    exact bsearch_get hs (by omega) (by rw [hsz]; exact hc)


private theorem foldl_rows {α : Type} (E : List (ℕ × α)) (A : Array (List α)) :
    (E.foldl (fun acc e => acc.modify e.1 fun l => l ++ [e.2]) A).size = A.size ∧
    ∀ u < A.size, (E.foldl (fun acc e => acc.modify e.1 fun l => l ++ [e.2]) A)[u]! =
      A[u]! ++ (E.filter fun e => e.1 = u).map (·.2) := by
  induction E using List.reverseRecOn with
  | nil => exact ⟨rfl, fun u _ => by simp⟩
  | append_singleton E e ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [h1], fun u hu => ?_⟩
    have hs : u < ((E.foldl (fun acc e => acc.modify e.1 fun l => l ++ [e.2]) A).modify e.1
        fun l => l ++ [e.2]).size := by simp [h1, hu]
    rw [getElem!_pos _ u hs, Array.getElem_modify, List.filter_append]
    have := h2 u hu
    rw [getElem!_pos _ u (by rw [h1]; exact hu)] at this
    rw [this]
    by_cases e1 : e.1 = u
    · simp [e1]
    · simp [e1]

private theorem pairs_eq : ([(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)] : List (ℕ × ℕ)) =
    (List.range 6).map fun kk => (pairFst kk, pairSnd kk) := by
  decide

private theorem pair_facts : ∀ kk < 6, pairFst kk < 3 ∧ pairSnd kk < 3 ∧ pairFst kk ≠ pairSnd kk := by
  decide

private theorem pair_inj : ∀ kk < 6, ∀ kk' < 6, pairFst kk = pairFst kk' →
    pairSnd kk = pairSnd kk' → kk = kk' := by
  decide

theorem nbrK_sound {n m d wB wL NB NL PW : Nat} {LP : Nat → Nat} {L : Array ℕ}
    (hL : ∀ j < 3 * m, L[j]! = LP j) (h : nbrK n m d wB wL LP NB NL PW = true) :
    (nbrDataG n m L).map nbrRow =
        Array.ofFn (n := n) (fun u => Array.ofFn (n := d) fun i => pgW wB NB (d * u + i)) ∧
      (nbrDataG n m L).map lineRow =
        Array.ofFn (n := n) (fun u => Array.ofFn (n := d) fun i => pgW wL NL (d * u + i)) := by
  unfold nbrK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, hnd, hR, hLn⟩ := h
  have hnd : n * d = 6 * m := beq_iffG.1 hnd
  have hRow : ∀ u < n, ∀ i < d, pgW wB NB (d * u + i) < n ∧ pgW wL NL (d * u + i) < m ∧
      (i + 1 < d → pgW wB NB (d * u + i) < pgW wB NB (d * u + i + 1)) := by
    intro u hu i hi
    have := allN_spec (allN_spec hR u hu) i hi
    unfold nbrRowK at this
    simp only [strictB_eqG, bAnd_iff] at this
    obtain ⟨a, b, c⟩ := this
    exact ⟨blt_iffG.1 a, blt_iffG.1 b, fun hi1 => blt_iffG.1 (bIf_imp c (blt_iffG.2 hi1))⟩
  let a := fun t => LP (3 * (t / 6) + pairFst (t % 6))
  let b := fun t => LP (3 * (t / 6) + pairSnd (t % 6))
  have hLine : ∀ t < 6 * m, a t < n ∧ (∀ i < 3, ∀ i' < 3,
        LP (3 * (t / 6) + i) = LP (3 * (t / 6) + i') → i = i') ∧
      pgW 4 PW t < d ∧ pgW wB NB (d * a t + pgW 4 PW t) = b t ∧
      pgW wL NL (d * a t + pgW 4 PW t) = t / 6 := by
    intro t ht
    have hv : t / 6 < m := by omega
    have := allN_spec hLn (t / 6) hv
    unfold nbrLineK at this
    simp only [strictB_eqG, bAnd_iff] at this
    obtain ⟨a0, a1, a2, d01, d02, d12, hp⟩ := this
    have hkk := allN_spec hp (t % 6) (Nat.mod_lt _ (by omega))
    unfold nbrPairK at hkk
    simp only [strictB_eqG, bAnd_iff] at hkk
    obtain ⟨p1, p2, p3⟩ := hkk
    have e6 : Nat.add (Nat.mul 6 (t / 6)) (t % 6) = t := Nat.div_add_mod t 6
    rw [e6] at p1 p2 p3
    have n01 : LP (3 * (t / 6)) ≠ LP (3 * (t / 6) + 1) := fun e => by
      have : Nat.beq (LP (Nat.mul 3 (t / 6))) (LP (Nat.succ (Nat.mul 3 (t / 6)))) = true :=
        beq_iffG.2 e
      rw [this] at d01
      exact Bool.false_ne_true d01
    have n02 : LP (3 * (t / 6)) ≠ LP (3 * (t / 6) + 2) := fun e => by
      have : Nat.beq (LP (Nat.mul 3 (t / 6))) (LP (Nat.add (Nat.mul 3 (t / 6)) 2)) = true :=
        beq_iffG.2 e
      rw [this] at d02
      exact Bool.false_ne_true d02
    have n12 : LP (3 * (t / 6) + 1) ≠ LP (3 * (t / 6) + 2) := fun e => by
      have : Nat.beq (LP (Nat.succ (Nat.mul 3 (t / 6)))) (LP (Nat.add (Nat.mul 3 (t / 6)) 2)) =
        true := beq_iffG.2 e
      rw [this] at d12
      exact Bool.false_ne_true d12
    have hpt : ∀ i < 3, LP (3 * (t / 6) + i) < n := by
      intro i hi
      interval_cases i
      · exact blt_iffG.1 a0
      · exact blt_iffG.1 a1
      · exact blt_iffG.1 a2
    refine ⟨hpt _ (pair_facts _ (Nat.mod_lt _ (by omega))).1, fun i hi i' hi' e => ?_,
      blt_iffG.1 p1, beq_iffG.1 p2, beq_iffG.1 p3⟩
    interval_cases i <;> interval_cases i' <;> simp_all
  have hb_ne : ∀ t < 6 * m, a t ≠ b t := by
    intro t ht e
    have hf := pair_facts (t % 6) (Nat.mod_lt _ (by omega))
    exact hf.2.2 ((hLine t ht).2.1 _ hf.1 _ hf.2.1 e)
  have hev_inj : ∀ t < 6 * m, ∀ t' < 6 * m, t / 6 = t' / 6 → a t = a t' → b t = b t' →
      t = t' := by
    intro t ht t' ht' hv ea eb
    have hf := pair_facts (t % 6) (Nat.mod_lt _ (by omega))
    have hf' := pair_facts (t' % 6) (Nat.mod_lt _ (by omega))
    have I := (hLine t ht).2.1
    simp only [a, b] at ea eb
    rw [← hv] at ea eb
    have := pair_inj _ (Nat.mod_lt t (by omega)) _ (Nat.mod_lt t' (by omega))
      (I _ hf.1 _ hf'.1 ea) (I _ hf.2.1 _ hf'.2.1 eb)
    have := Nat.div_add_mod t 6
    have := Nat.div_add_mod t' 6
    omega
  let E := (List.range (6 * m)).map fun t => (a t, (b t, t / 6))
  have hE : nbrDataG n m L = E.foldl (fun acc e => acc.modify e.1 fun l => l ++ [e.2])
      (Array.replicate n []) := by
    unfold nbrDataG
    have hflat : ∀ m' ≤ m, (List.range m').flatMap (fun v =>
        ([(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)] : List (ℕ × ℕ)).map
          fun kk => (L[3 * v + kk.1]!, (L[3 * v + kk.2]!, v))) =
        (List.range (6 * m')).map fun t => (a t, (b t, t / 6)) := by
      intro m' hm'
      induction m' with
      | zero => rfl
      | succ m' ih =>
        have e6 : 6 * (m' + 1) = 6 * m' + 6 := by ring
        rw [List.range_succ, List.flatMap_append, ih (by omega), List.flatMap_singleton, e6,
          List.range_add, List.map_append, List.map_map,
          pairs_eq, List.map_map]
        congr 1
        apply List.map_congr_left
        intro kk hk
        have hk : kk < 6 := List.mem_range.1 hk
        have e1 : (6 * m' + kk) / 6 = m' := by omega
        have e2 : (6 * m' + kk) % 6 = kk := by omega
        have hf := pair_facts kk hk
        simp only [Function.comp, a, b, e1, e2]
        rw [hL _ (by omega), hL _ (by omega)]
    have hEdef : E = (List.range (6 * m)).map fun t => (a t, (b t, t / 6)) := rfl
    rw [hEdef, ← hflat m le_rfl, List.foldl_flatMap]
    congr 1
  obtain ⟨hsz, hrow⟩ := foldl_rows E (Array.replicate n [])
  rw [Array.size_replicate] at hsz hrow
  let ψ := fun t => d * a t + pgW 4 PW t
  have hψ : ∀ s < n * d, ∃ t < 6 * m, ψ t = s := by
    have hinj : ∀ t < 6 * m, ∀ t' < 6 * m, ψ t = ψ t' → t = t' := by
      intro t ht t' ht' e
      obtain ⟨-, -, p, e1, e2⟩ := hLine t ht
      obtain ⟨-, -, p', e1', e2'⟩ := hLine t' ht'
      have hd : 0 < d := by omega
      have ha : a t = a t' := by
        have := congrArg (· / d) e
        simp only [ψ] at this
        rwa [Nat.mul_add_div hd, Nat.mul_add_div hd, Nat.div_eq_of_lt p, Nat.div_eq_of_lt p',
          Nat.add_zero, Nat.add_zero] at this
      have hp : pgW 4 PW t = pgW 4 PW t' := by
        simp only [ψ, ha] at e
        omega
      have hv : t / 6 = t' / 6 := by rw [← e2, ← e2', ha, hp]
      have hb : b t = b t' := by rw [← e1, ← e1', ha, hp]
      exact hev_inj t ht t' ht' hv ha hb
    have himg : (Finset.range (6 * m)).image ψ = Finset.range (n * d) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
        obtain ⟨t, ht, rfl⟩ := hx
        obtain ⟨h1, -, h2, -⟩ := hLine t ht
        calc d * a t + pgW 4 PW t < d * a t + d := by omega
          _ = d * (a t + 1) := by ring
          _ ≤ d * n := Nat.mul_le_mul_left _ h1
          _ = n * d := Nat.mul_comm _ _
      · rw [Finset.card_image_of_injOn (fun i hi j hj e => hinj i (by simpa using hi)
          j (by simpa using hj) e), Finset.card_range, Finset.card_range, hnd]
    intro s hs
    have : s ∈ (Finset.range (6 * m)).image ψ := by
      rw [himg]
      simpa using hs
    simpa using this
  let T := fun u => (List.range d).map fun i => (pgW wB NB (d * u + i), pgW wL NL (d * u + i))
  have hTlt : ∀ u < n, ((T u).map Prod.fst).Pairwise (· < ·) := by
    intro u hu
    rw [List.map_map]
    exact pairwise_lt_of_adj fun j hj => (hRow u hu j (by omega)).2.2 hj
  have hperm : ∀ u < n, List.Perm (nbrDataG n m L)[u]! (T u) := by
    intro u hu
    rw [hE, hrow u hu]
    simp only [getElem!_pos (Array.replicate n ([] : List (ℕ × ℕ))) u (by simpa using hu),
      Array.getElem_replicate, List.nil_append]
    have hEnd : E.Nodup := List.Nodup.map_on (fun t ht t' ht' e => by
      simp only [Prod.mk.injEq] at e
      exact hev_inj t (List.mem_range.1 ht) t' (List.mem_range.1 ht') e.2.2 e.1 e.2.1)
      List.nodup_range
    have h1 : ((E.filter fun e => e.1 = u).map (·.2)).Nodup := by
      refine List.Nodup.map_on (fun x hx y hy e => ?_) (hEnd.filter _)
      rw [List.mem_filter] at hx hy
      have := of_decide_eq_true hx.2
      have := of_decide_eq_true hy.2
      exact Prod.ext (by omega) e
    have h2 : (T u).Nodup := List.Nodup.of_map Prod.fst ((hTlt u hu).imp Nat.ne_of_lt)
    refine (List.perm_ext_iff_of_nodup h1 h2).2 fun x => ?_
    simp only [List.mem_map, List.mem_filter, E, List.mem_range, decide_eq_true_eq, T]
    constructor
    · rintro ⟨_, ⟨⟨t, ht, rfl⟩, hu'⟩, rfl⟩
      obtain ⟨-, -, p, e1, e2⟩ := hLine t ht
      simp only at hu'
      refine ⟨pgW 4 PW t, p, ?_⟩
      rw [← hu', e1, e2]
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨t, ht, e⟩ := hψ (d * u + i) (by
        calc d * u + i < d * u + d := by omega
          _ = d * (u + 1) := by ring
          _ ≤ d * n := Nat.mul_le_mul_left _ hu
          _ = n * d := Nat.mul_comm _ _)
      obtain ⟨-, -, p, e1, e2⟩ := hLine t ht
      have hd : 0 < d := by omega
      have ha : a t = u := by
        have := congrArg (· / d) e
        simp only [ψ] at this
        rwa [Nat.mul_add_div hd, Nat.mul_add_div hd, Nat.div_eq_of_lt p, Nat.div_eq_of_lt hi,
          Nat.add_zero, Nat.add_zero] at this
      have hp : pgW 4 PW t = i := by
        simp only [ψ, ha] at e
        omega
      refine ⟨_, ⟨⟨t, ht, rfl⟩, ha⟩, ?_⟩
      rw [← ha, ← hp, e1, e2]
  have hsz' : (nbrDataG n m L).size = n := by rw [hE, hsz]
  refine ⟨?_, ?_⟩
  · apply Array.ext
    · simp [hsz']
    · intro u h1 h2
      simp only [Array.size_map, hsz'] at h1
      rw [Array.getElem_map, Array.getElem_ofFn]
      have hp := hperm u h1
      rw [getElem!_pos _ u (by rw [hsz']; exact h1)] at hp
      unfold nbrRow
      have : (((nbrDataG n m L)[u]).map Prod.fst).mergeSort (fun a b => decide (a ≤ b)) =
          (T u).map Prod.fst :=
        List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2) (sorted_le _)
          ((hTlt u h1).imp Nat.le_of_lt) ((List.mergeSort_perm _ _).trans (hp.map _))
      rw [this]
      apply Array.ext
      · simp [T]
      · intro i _ _
        simp [T]
  · apply Array.ext
    · simp [hsz']
    · intro u h1 h2
      simp only [Array.size_map, hsz'] at h1
      rw [Array.getElem_map, Array.getElem_ofFn]
      have hp := hperm u h1
      rw [getElem!_pos _ u (by rw [hsz']; exact h1)] at hp
      unfold lineRow
      have hlt := hTlt u h1
      rw [List.pairwise_map] at hlt
      have hs := List.pairwise_mergeSort (le := fun a b : ℕ × ℕ => decide (a.1 ≤ b.1))
        (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega)
        (nbrDataG n m L)[u]
      have hms := List.mergeSort_perm (nbrDataG n m L)[u] (fun a b : ℕ × ℕ => decide (a.1 ≤ b.1))
      have : (nbrDataG n m L)[u].mergeSort (fun a b : ℕ × ℕ => decide (a.1 ≤ b.1)) = T u := by
        refine List.Perm.eq_of_pairwise (le := fun a b : ℕ × ℕ => decide (a.1 ≤ b.1) = true)
          (fun x y hx hy h1 h2 => ?_) hs (hlt.imp fun h => by simp; omega) (hms.trans hp)
        have hx' := (hms.trans hp).subset hx
        simp only [T, List.mem_map, List.mem_range] at hx' hy
        obtain ⟨i, hi, rfl⟩ := hx'
        obtain ⟨j, hj, rfl⟩ := hy
        simp only [decide_eq_true_eq] at h1 h2
        have hij : i = j := by
          rcases Nat.lt_trichotomy i j with h | h | h
          · have := List.pairwise_iff_getElem.1 hlt i j (by simpa [T] using hi) (by simpa [T] using hj) h
            simp only [T, List.getElem_map, List.getElem_range] at this
            omega
          · exact h
          · have := List.pairwise_iff_getElem.1 hlt j i (by simpa [T] using hj) (by simpa [T] using hi) h
            simp only [T, List.getElem_map, List.getElem_range] at this
            omega
        rw [hij]
      rw [this]
      apply Array.ext
      · simp [T]
      · intro i _ _
        simp [T]

theorem cellSize_eq {w C x : Nat} (hx : x < 1755) :
    cellSize (unpack 1755 w C) x = cntK 1755 w C (pgW w C x) := by
  rw [← cntK_sound, cellSize, labelCount, ← List.countP_eq_length_filter, unpackW_get hx, pgW_eq]

end CFSG.KS.SporSch

end
