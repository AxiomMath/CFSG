module

public import Certificates.Data.Kernel.EvenSporP12.Defs
import all CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Check

public section

namespace CFSG.KC.EvenSporP12

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

@[expose] def Ent (a : Array Nat) : Prop := ∀ v ∈ a.toList, v < 16

@[expose] def Val (n : Nat) (a : Array Nat) : Prop := a.size = n ∧ Ent a

@[expose] def entB (a : Array Nat) : Bool := a.toList.all (· < 16)

theorem ent_of_entB {a : Array Nat} (h : entB a = true) : Ent a := by
  intro v hv
  simp only [entB, List.all_eq_true, decide_eq_true_eq] at h
  exact h v hv

theorem all_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem encL_dig : ∀ (l : List Nat), (∀ v ∈ l, v < 16) → ∀ i, encL l / 16 ^ i % 16 = l.getD i 0
  | [], _, i => by simp [encL]
  | x :: xs, h, 0 => by
    have hx : x < 16 := h x List.mem_cons_self
    simp only [encL, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | x :: xs, h, i + 1 => by
    have hx : x < 16 := h x List.mem_cons_self
    have ih := encL_dig xs (fun v hv => h v (List.mem_cons_of_mem _ hv)) i
    have e : (x + 16 * encL xs) / 16 = encL xs := by omega
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    simp only [encL, List.getD_cons_succ]
    rw [e]
    exact ih

theorem getElem!_eq_getD (a : Array Nat) (j : Nat) : a[j]! = a.toList.getD j 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : j < a.size
  · rw [getElem!_pos a j h]
    simp [h]
  · rw [getElem!_neg a j h]
    simp [h]

theorem dig_enc {a : Array Nat} (h : Ent a) (j : Nat) : dig (enc a) j = a[j]! := by
  rw [getElem!_eq_getD]
  exact encL_dig _ h j

theorem lt_of_ent {a : Array Nat} (h : Ent a) (j : Nat) : a[j]! < 16 := by
  rw [getElem!_eq_getD, List.getD_eq_getElem?_getD]
  cases hj : a.toList[j]? with
  | none => simp
  | some v => simpa using h v (List.mem_of_getElem? hj)

theorem ent_ofFn {n : Nat} {f : Fin n → Nat} (h : ∀ i, f i < 16) : Ent (Array.ofFn f) := by
  intro v hv
  simp only [Array.toList_ofFn, List.mem_ofFn] at hv
  obtain ⟨i, rfl⟩ := hv
  exact h i

theorem ofFn_eq_map_range {n : Nat} {f : Fin n → Nat} {g : Nat → Nat} (h : ∀ i : Fin n, f i = g i) :
    List.ofFn f = (List.range n).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [h]

variable {n : Nat}

theorem ent_pmul {x y : Array Nat} (hx : Ent x) : Ent (pmul n x y) :=
  ent_ofFn fun _ => lt_of_ent hx _

theorem size_pmul (x y : Array Nat) : (pmul n x y).size = n := by
  simp [pmul]

theorem val_pmul {x y : Array Nat} (hx : Ent x) : Val n (pmul n x y) :=
  ⟨size_pmul x y, ent_pmul hx⟩

theorem val_pid (hn : n ≤ 16) : Val n (pid n) :=
  ⟨by simp [pid], ent_ofFn fun i => by have := i.2; omega⟩

theorem enc_pmul {x y : Array Nat} (hx : Ent x) (hy : Ent y) :
    enc (pmul n x y) = pmulK n (enc x) (enc y) := by
  rw [enc, pmul, Array.toList_ofFn, ofFn_eq_map_range (g := fun i => x[y[i]!]!) fun _ => rfl,
    pmulK]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [dig_enc hy, dig_enc hx]

theorem enc_pid : enc (pid n) = pidK n := by
  have e : List.ofFn (fun i : Fin n => (i : Nat)) = (List.range n).map id :=
    ofFn_eq_map_range fun _ => rfl
  rw [enc, pid, Array.toList_ofFn, e, List.map_id, pidK]

theorem pmul_eq_iff {x y z w : Array Nat} :
    pmul n x y = pmul n z w ↔ ∀ i < n, x[y[i]!]! = z[w[i]!]! := by
  unfold pmul
  constructor
  · intro h i hi
    have := congrArg (fun a : Array Nat => a[i]!) h
    simpa [getElem!_pos, hi] using this
  · intro h
    apply Array.ext (by simp)
    intro i h1 h2
    simp only [Array.getElem_ofFn]
    exact h i (by simpa using h1)

theorem pmul_eq_pid_iff {x : Array Nat} : pmul n x x = pid n ↔ ∀ i < n, x[x[i]!]! = i := by
  unfold pmul pid
  constructor
  · intro h i hi
    have := congrArg (fun a : Array Nat => a[i]!) h
    simpa [getElem!_pos, hi] using this
  · intro h
    apply Array.ext (by simp)
    intro i h1 h2
    simp only [Array.getElem_ofFn]
    exact h i (by simpa using h1)

theorem commB_eq {x y : Array Nat} (hx : Ent x) (hy : Ent y) :
    commB n x y = commK n (enc x) (enc y) := by
  rw [Bool.eq_iff_iff]
  simp only [commB, beq_iff_eq, commK, List.all_eq_true, List.mem_range, pmul_eq_iff,
    dig_enc hx, dig_enc hy]

theorem sqB_eq {x : Array Nat} (hx : Ent x) : sqB n x = sqK n (enc x) := by
  rw [Bool.eq_iff_iff]
  simp only [sqB, beq_iff_eq, sqK, List.all_eq_true, List.mem_range, pmul_eq_pid_iff,
    dig_enc hx]

theorem enc_inj {a b : Array Nat} (ha : Val n a) (hb : Val n b) (h : enc a = enc b) : a = b := by
  apply Array.ext (ha.1.trans hb.1.symm)
  intro i h1 h2
  have := congrArg (fun P => dig P i) h
  simp only [dig_enc ha.2, dig_enc hb.2] at this
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at this

theorem beq_eq {a b : Array Nat} (ha : Val n a) (hb : Val n b) : (a == b) = (enc a == enc b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, enc_inj ha hb⟩

theorem contains_eq {L : List (Array Nat)} {a : Array Nat} (hL : ∀ b ∈ L, Val n b)
    (ha : Val n a) : L.contains a = (L.map enc).contains (enc a) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · intro h
    exact ⟨a, h, rfl⟩
  · rintro ⟨b, hb, he⟩
    rwa [← enc_inj (hL b hb) ha he]

theorem allDistinct_eq : ∀ {L : List (Array Nat)}, (∀ b ∈ L, Val n b) →
    allDistinct L = allDistinctK (L.map enc)
  | [], _ => rfl
  | x :: xs, hL => by
    simp only [allDistinct, allDistinctK, List.map_cons]
    rw [contains_eq (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (hL x List.mem_cons_self),
      allDistinct_eq fun b hb => hL b (List.mem_cons_of_mem _ hb)]

theorem ent_getD {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g) (l : Nat) : Ent (G.getD l #[]) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : G[l]? with
  | none => intro v hv; simp at hv
  | some g => simpa using hG g (List.mem_of_getElem? h)

theorem enc_getD (G : List (Array Nat)) (l : Nat) : enc (G.getD l #[]) = (G.map enc).getD l 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases G[l]? <;> rfl

theorem wordArr_props (hn : n ≤ 16) {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g) :
    ∀ w : List Nat, Val n (wordArr n G w) ∧ enc (wordArr n G w) = wordK n (G.map enc) w
  | [] => ⟨val_pid hn, enc_pid⟩
  | l :: w => by
    have ih := wordArr_props hn hG w
    have e1 : wordArr n G (l :: w) = pmul n (G.getD l #[]) (wordArr n G w) := rfl
    have e2 : wordK n (G.map enc) (l :: w) = pmulK n ((G.map enc).getD l 0) (wordK n (G.map enc) w) :=
      rfl
    rw [e1, e2]
    refine ⟨val_pmul (ent_getD hG l), ?_⟩
    rw [enc_pmul (ent_getD hG l) ih.1.2, ih.2, enc_getD]

theorem map_wordK (hn : n ≤ 16) {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g) (L : List (List Nat)) :
    L.map (wordK n (G.map enc)) = (L.map (wordArr n G)).map enc := by
  rw [List.map_map]
  apply List.map_congr_left
  intro w _
  exact (wordArr_props hn hG w).2.symm

theorem val_map_wordArr (hn : n ≤ 16) {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g)
    (L : List (List Nat)) : ∀ v ∈ L.map (wordArr n G), Val n v := by
  intro v hv
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hv
  exact (wordArr_props hn hG w).1

@[expose] def Rel (n : Nat) (acc : Array (Array Nat × List Nat)) (accK : List (Nat × List Nat)) :
    Prop :=
  accK = acc.toList.map (fun p => (enc p.1, p.2)) ∧ ∀ p ∈ acc.toList, Val n p.1

theorem rel_step {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g) {x : Array Nat} (hx : Ent x)
    (w : List Nat) (k : Nat) {acc : Array (Array Nat × List Nat)} {accK : List (Nat × List Nat)}
    (h : Rel n acc accK) :
    Rel n (let y := pmul n x (G.getD k #[])
      if acc.any (fun e => e.1 == y) then acc else acc.push (y, w ++ [k]))
      (stepK n (G.map enc) (enc x) w accK k) := by
  have hy : Val n (pmul n x (G.getD k #[])) := val_pmul hx
  have hey : enc (pmul n x (G.getD k #[])) = pmulK n (enc x) ((G.map enc).getD k 0) := by
    rw [enc_pmul hx (ent_getD hG k), enc_getD]
  have hany : acc.any (fun e => e.1 == pmul n x (G.getD k #[])) =
      accK.any (fun e => e.1 == pmulK n (enc x) ((G.map enc).getD k 0)) := by
    rw [h.1, List.any_map, ← Array.any_toList]
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨e, he, hb⟩
      refine ⟨e, he, ?_⟩
      simp only [Function.comp_def]
      rw [← hey, ← beq_eq (h.2 e he) hy]
      exact hb
    · rintro ⟨e, he, hb⟩
      refine ⟨e, he, ?_⟩
      simp only [Function.comp_def] at hb
      rw [← hey, ← beq_eq (h.2 e he) hy] at hb
      exact hb
  simp only [stepK]
  rw [hany]
  split
  · exact h
  · refine ⟨?_, ?_⟩
    · rw [h.1, Array.toList_push, List.map_append, List.map_singleton, hey]
    · intro p hp
      rw [Array.toList_push, List.mem_append] at hp
      rcases hp with hp | hp
      · exact h.2 p hp
      · simp only [List.mem_singleton] at hp
        subst hp
        exact hy

theorem rel_fold {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g) {x : Array Nat} (hx : Ent x)
    (w : List Nat) : ∀ (L : List Nat) {acc : Array (Array Nat × List Nat)}
    {accK : List (Nat × List Nat)}, Rel n acc accK →
    Rel n (L.foldl (fun acc k =>
        let y := pmul n x (G.getD k #[])
        if acc.any (fun e => e.1 == y) then acc else acc.push (y, w ++ [k])) acc)
      (L.foldl (stepK n (G.map enc) (enc x) w) accK)
  | [], _, _, h => h
  | k :: L, _, _, h => by
    simp only [List.foldl_cons]
    exact rel_fold hG hx w L (rel_step hG hx w k h)

def goA (n : Nat) (G : List (Array Nat)) :
    Nat → Nat → Array (Array Nat × List Nat) → Array (Array Nat × List Nat)
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
    if h : i < acc.size then
      let x := acc[i].1
      let w := acc[i].2
      let acc' := (List.range G.length).foldl (fun acc k =>
        let y := pmul n x (G.getD k #[])
        if acc.any (fun e => e.1 == y) then acc else acc.push (y, w ++ [k])) acc
      goA n G fuel (i + 1) acc'
    else acc

theorem wordsOf_eq_goA (n : Nat) (G : List (Array Nat)) :
    wordsOf n G = (goA n G 2000 0 #[(pid n, [])]).toList.map (·.2) := by
  unfold wordsOf
  apply congrArg (fun a : Array (Array Nat × List Nat) => a.toList.map (·.2))
  generalize (0 : Nat) = i
  generalize (#[(pid n, [])] : Array (Array Nat × List Nat)) = acc
  generalize 2000 = f
  induction f generalizing i acc with
  | zero => rfl
  | succ f ih =>
    rw [goA]
    simp only [← ih]
    rfl

theorem rel_go (hn : n ≤ 16) {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g) :
    ∀ (fuel i : Nat) {acc : Array (Array Nat × List Nat)} {accK : List (Nat × List Nat)},
    Rel n acc accK → Rel n (goA n G fuel i acc) (goK n (G.map enc) fuel i accK)
  | 0, _, _, _, h => by
    simp only [goA, goK]
    exact h
  | fuel + 1, i, acc, accK, h => by
    have hsz : accK.length = acc.size := by rw [h.1, List.length_map, Array.length_toList]
    simp only [goA, goK, hsz]
    by_cases hi : i < acc.size
    · rw [dif_pos hi, if_pos hi]
      have hget : accK.getD i (0, []) = (enc acc[i].1, acc[i].2) := by
        rw [h.1, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
          getElem?_pos acc i hi]
        rfl
      rw [hget, List.length_map]
      apply rel_go hn hG fuel (i + 1)
      exact rel_fold hG (h.2 acc[i] (Array.getElem_mem_toList hi)).2 acc[i].2 _ h
    · rw [dif_neg hi, if_neg hi]
      exact h

theorem wordsOf_eq (hn : n ≤ 16) {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g) :
    wordsOf n G = wordsOfK n (G.map enc) := by
  have h0 : Rel n #[(pid n, [])] [(pidK n, [])] := by
    refine ⟨?_, ?_⟩
    · simp [enc_pid]
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact val_pid hn
  have h := rel_go hn hG 2000 0 h0
  rw [wordsOf_eq_goA, wordsOfK, h.1, List.map_map]
  rfl

theorem enumOK_eq (hn : n ≤ 16) {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g) (L : List (List Nat)) :
    enumOK n G L = enumOKK n (G.map enc) L := by
  have hV := val_map_wordArr hn hG L
  simp only [enumOK, enumOKK]
  rw [map_wordK hn hG L, List.length_map, allDistinct_eq hV]
  congr 2
  apply all_congr'
  intro k _
  rw [List.all_map (f := enc)]
  apply all_congr'
  intro v hv
  simp only [Function.comp_def]
  rw [contains_eq hV (val_pmul (hV v hv).2), enc_pmul (hV v hv).2 (ent_getD hG k), enc_getD]

theorem elemAbOK_eq {EG : List (Array Nat)} (hE : ∀ g ∈ EG, Ent g) :
    elemAbOK n EG = elemAbOKK n (EG.map enc) := by
  simp only [elemAbOK, elemAbOKK, List.all_map, Function.comp_def]
  congr 1
  · exact all_congr' fun x hx => sqB_eq (hE x hx)
  · apply all_congr'
    intro x hx
    apply all_congr'
    intro y hy
    exact commB_eq (hE x hx) (hE y hy)

theorem filter_comm_eq {L : List (Array Nat)} (hL : ∀ b ∈ L, Val n b) {x : Array Nat} (hx : Ent x) :
    (L.map enc).filter (commK n (enc x)) = (L.filter (commB n x)).map enc := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro y hy
  exact (commB_eq hx (hL y hy).2).symm

theorem tripleK_eq {Cx : List (Array Nat)} (hC : ∀ b ∈ Cx, Val n b) :
    tripleK n (Cx.map enc) = (triple n Cx).map enc := by
  simp only [tripleK, triple]
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro y hy
  simp only [Function.comp_def]
  rw [filter_comm_eq hC (hC y hy).2, List.length_map, sqB_eq (hC y hy).2]

theorem countOK_eq (hn : n ≤ 16) {PV EV : List (Array Nat)} (hP : ∀ b ∈ PV, Val n b)
    (hE : ∀ b ∈ EV, Val n b) : countOK n PV EV = countOKK n (PV.map enc) (EV.map enc) := by
  simp only [countOK, countOKK, List.all_map, Function.comp_def]
  apply all_congr'
  intro x hx
  have hC : ∀ b ∈ PV.filter (commB n x), Val n b := fun b hb => hP b (List.mem_filter.1 hb).1
  have hcnt : countAt n PV x = countAtK n (PV.map enc) (enc x) := by
    simp only [countAt, countAtK]
    rw [filter_comm_eq hP (hP x hx).2, tripleK_eq hC, List.length_map]
  rw [beq_eq (hP x hx) (val_pid hn), enc_pid, sqB_eq (hP x hx).2, contains_eq hE (hP x hx), hcnt]

theorem order8OK_eq (hn : n ≤ 16) {G : List (Array Nat)} (hG : ∀ g ∈ G, Ent g) (w : List Nat) :
    order8OK n G w = order8OKK n (G.map enc) w := by
  have hg := wordArr_props hn hG w
  have h2 : Val n (pmul n (wordArr n G w) (wordArr n G w)) := val_pmul hg.1.2
  have h4 := val_pmul (n := n) (y := pmul n (wordArr n G w) (wordArr n G w)) h2.2
  have h8 := val_pmul (n := n)
    (y := pmul n (pmul n (wordArr n G w) (wordArr n G w)) (pmul n (wordArr n G w) (wordArr n G w)))
    h4.2
  simp only [order8OK, order8OKK, bne]
  rw [beq_eq h4 (val_pid hn), beq_eq h8 (val_pid hn), enc_pmul h4.2 h4.2, enc_pmul h2.2 h2.2,
    enc_pmul hg.1.2 hg.1.2, hg.2, enc_pid, List.length_map]

theorem normOK_eq (hn : n ≤ 16) {EV EG : List (Array Nat)} (hV : ∀ b ∈ EV, Val n b)
    (hE : ∀ g ∈ EG, Ent g) {c : Array Nat} (hc : Ent c) :
    normOK n EV EG c = normOKK n (EV.map enc) (EG.map enc) (enc c) := by
  have hcc : Val n (pmul n c c) := val_pmul hc
  have hccc : Val n (pmul n c (pmul n c c)) := val_pmul hc
  simp only [normOK, normOKK, List.all_map, Function.comp_def]
  rw [beq_eq hccc (val_pid hn), enc_pmul hc hcc.2, enc_pmul hc hc, enc_pid]
  congr 1
  apply all_congr'
  intro u hu
  have hcu : Val n (pmul n c u) := val_pmul hc
  rw [contains_eq hV (val_pmul hcu.2), enc_pmul hcu.2 hcc.2, enc_pmul hc (hE u hu), enc_pmul hc hc]

theorem size_swapsArr (n : Nat) : ∀ w : List (Nat × Nat), (swapsArr n w).size = n
  | [] => by simp [swapsArr, pid]
  | _ :: _ => by
    simp only [swapsArr, List.foldr_cons]
    exact size_pmul _ _

theorem core_eq (hn : n ≤ 16) {PG EG CG : List (Array Nat)} (hP : ∀ g ∈ PG, Ent g)
    (hE : ∀ g ∈ EG, Val n g) (hC : ∀ g ∈ CG, Ent g) (b1 b2 b3 : Bool) :
    (b1 && b2 && b3 && enumOK n PG (wordsOf n PG) && (wordsOf n PG).length == 512 &&
      enumOK n EG (wordsOf n EG) && (wordsOf n EG).length == 64 &&
      enumOK n CG (wordsOf n CG) && (wordsOf n CG).length == 9 && elemAbOK n EG &&
      EG.all (((wordsOf n PG).map (wordArr n PG)).contains ·) && order8OK n PG gWord &&
      countOK n ((wordsOf n PG).map (wordArr n PG)) ((wordsOf n EG).map (wordArr n EG)) &&
      CG.all (normOK n ((wordsOf n EG).map (wordArr n EG)) EG)) =
    (b1 && b2 && b3 && enumOKK n (PG.map enc) (wordsOfK n (PG.map enc)) &&
      (wordsOfK n (PG.map enc)).length == 512 &&
      enumOKK n (EG.map enc) (wordsOfK n (EG.map enc)) &&
      (wordsOfK n (EG.map enc)).length == 64 &&
      enumOKK n (CG.map enc) (wordsOfK n (CG.map enc)) &&
      (wordsOfK n (CG.map enc)).length == 9 && elemAbOKK n (EG.map enc) &&
      (EG.map enc).all (((wordsOfK n (PG.map enc)).map (wordK n (PG.map enc))).contains ·) &&
      order8OKK n (PG.map enc) gWord &&
      countOKK n ((wordsOfK n (PG.map enc)).map (wordK n (PG.map enc)))
        ((wordsOfK n (EG.map enc)).map (wordK n (EG.map enc))) &&
      (CG.map enc).all (normOKK n ((wordsOfK n (EG.map enc)).map (wordK n (EG.map enc)))
        (EG.map enc))) := by
  have hE' : ∀ g ∈ EG, Ent g := fun g hg => (hE g hg).2
  have hPV := val_map_wordArr hn hP (wordsOf n PG)
  have hEV := val_map_wordArr hn hE' (wordsOf n EG)
  have hcont : (EG.all fun x => ((wordsOf n PG).map (wordArr n PG)).contains x) =
      ((EG.map enc).all fun x => (((wordsOf n PG).map (wordArr n PG)).map enc).contains x) := by
    rw [List.all_map (f := enc)]
    apply all_congr'
    intro x hx
    exact contains_eq hPV (hE x hx)
  have hnorm : (CG.all fun c => normOK n ((wordsOf n EG).map (wordArr n EG)) EG c) =
      ((CG.map enc).all fun c => normOKK n (((wordsOf n EG).map (wordArr n EG)).map enc)
        (EG.map enc) c) := by
    rw [List.all_map (f := enc)]
    apply all_congr'
    intro c hc
    exact normOK_eq hn hEV hE' (hC c hc)
  rw [map_wordK hn hP, map_wordK hn hE', ← wordsOf_eq hn hP, ← wordsOf_eq hn hE',
    ← wordsOf_eq hn hC, ← enumOK_eq hn hP, ← enumOK_eq hn hE', ← enumOK_eq hn hC,
    ← elemAbOK_eq hE', ← order8OK_eq hn hP, ← countOK_eq hn hPV hEV, ← hcont, ← hnorm]

theorem p12Check_eq (hn : n ≤ 16) (hP : (pGenSw.map (swapsArr n)).all entB = true)
    (hE : (eGenSw.map (swapsArr n)).all entB = true)
    (hC : (cGenSw.map (swapsArr n)).all entB = true) :
    p12Check n () = p12CheckK n := by
  have hE' : ∀ g ∈ eGenSw.map (swapsArr n), Ent g :=
    fun g hg => ent_of_entB (List.all_eq_true.1 hE g hg)
  have hEGV : ∀ g ∈ eGenSw.map (swapsArr n), Val n g := by
    intro g hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact ⟨size_swapsArr n w, hE' _ hg⟩
  exact core_eq hn (fun g hg => ent_of_entB (List.all_eq_true.1 hP g hg)) hEGV
    (fun g hg => ent_of_entB (List.all_eq_true.1 hC g hg)) _ _ _

end CFSG.KC.EvenSporP12
