module

public import Certificates.Data.Kernel.HD4Q2K
public import Certificates.Data.Sylow185.D42Center
public import CFSG.Certificates.Kernel.HTD42QSound
import CFSG.Certificates.Kernel.D4PlaneSound

public section

namespace CFSG.KC.HD4Q2K

open CFSG.AGLEmbedding CFSG.KC.HTD42Q HuppertD4Q2
open CFSG.AGLEmbedding.ChevOuter (Pr)

theorem size_mulP (p q : Pr) : (ChevOuter.mulP p q).1.size = 64 := D4Two.size_mulArr _ _

theorem size_oneP : ChevOuter.oneP.1.size = 64 := D4Two.size_oneArr

theorem size_wordP (w : List Nat) : (ChevOuter.wordP w).1.size = 64 := by
  cases w with
  | nil => exact size_oneP
  | cons s w => exact size_mulP _ _

theorem size_getD {L : List Pr} (hL : ∀ x ∈ L, x.1.size = 64) (i : Nat) :
    (L.getD i ChevOuter.oneP).1.size = 64 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[i]? with
  | none => exact size_oneP
  | some x => exact hL x (List.mem_of_getElem? h)

theorem size_foldl {β : Type} (g : Pr → β → Pr) (hg : ∀ a i, (g a i).1.size = 64) :
    ∀ (l : List β) (acc : Pr), acc.1.size = 64 → (l.foldl g acc).1.size = 64
  | [], _, h => h
  | x :: l, acc, _ => by
    rw [List.foldl_cons]
    exact size_foldl g hg l (g acc x) (hg acc x)

theorem size_powsP {x : Pr} (hx : x.1.size = 64) : ∀ z ∈ powsP x, z.1.size = 64 := by
  intro z hz
  simp only [powsP, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact size_oneP
  · exact hx
  · exact size_mulP _ _

theorem size_planeP (u v : Pr) : ∀ x ∈ planeP u v, x.1.size = 64 := by
  intro x hx
  simp only [planeP, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨a, -, b, -, rfl⟩ := hx
  exact size_mulP _ _

theorem size_mapWordP (L : List (List Nat)) : ∀ x ∈ L.map ChevOuter.wordP, x.1.size = 64 := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact size_wordP w

theorem encQ_oneQ : encQ ChevOuter.oneP = oneQ := encQ_oneP

theorem atQ_map (L : List Pr) (i : Nat) : atQ (L.map encQ) i = encQ (L.getD i ChevOuter.oneP) := by
  rw [atQ, ← encQ_oneQ, List.getD_map]

theorem eqQ_iff {a b : Nat × Nat} : eqQ a b = true ↔ a = b :=
  ⟨eq_of_eqQ, fun h => h ▸ eqQ_self a⟩

theorem eqQ_enc {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64) :
    eqQ (encQ p) (encQ q) = (p == q) := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  exact ⟨eq_of_eqQ_enc hp hq, fun h => h ▸ eqQ_self _⟩

theorem enc_inj {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64) (h : encQ p = encQ q) : p = q :=
  eq_of_eqQ_enc hp hq (h ▸ eqQ_self _)

theorem memQ_iff {x : Nat × Nat} {L : List (Nat × Nat)} : memQ x L = true ↔ x ∈ L := by
  unfold memQ
  rw [qrec_any (fun a => eqQ a x), List.any_eq_true]
  constructor
  · rintro ⟨a, ha, h⟩
    exact eq_of_eqQ h ▸ ha
  · intro h
    exact ⟨x, h, eqQ_self x⟩

theorem mem_map_enc {L : List Pr} (hL : ∀ x ∈ L, x.1.size = 64) {y : Pr} (hy : y.1.size = 64) :
    encQ y ∈ L.map encQ ↔ y ∈ L := by
  constructor
  · intro h
    obtain ⟨z, hz, e⟩ := List.mem_map.1 h
    exact enc_inj (hL z hz) hy e ▸ hz
  · exact List.mem_map_of_mem

theorem memQ_enc {L : List Pr} (hL : ∀ x ∈ L, x.1.size = 64) {y : Pr} (hy : y.1.size = 64) :
    memQ (encQ y) (L.map encQ) = L.contains y := by
  rw [Bool.eq_iff_iff, memQ_iff, mem_map_enc hL hy, List.contains_iff_mem]

theorem nodupQ_nodup : ∀ {L : List (Nat × Nat)}, nodupQ L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    have e : nodupQ (a :: l) = (!memQ a l && nodupQ l) := qrec_and _ _
    rw [e, Bool.and_eq_true] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, nodupQ_nodup h.2⟩
    rw [← memQ_iff] at ha
    rw [ha] at h
    exact Bool.false_ne_true h.1

theorem eqLQ_iff : ∀ (L M : List (Nat × Nat)), eqLQ L M = true ↔ L = M
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => ⟨fun h => Bool.noConfusion h, nofun⟩
  | _ :: _, [] => ⟨fun h => Bool.noConfusion h, nofun⟩
  | a :: L, b :: M => by
    have e : eqLQ (a :: L) (b :: M) = (eqQ a b && eqLQ L M) := qrec_and _ _
    rw [e, Bool.and_eq_true, eqQ_iff, eqLQ_iff L M, List.cons.injEq]

theorem mem_zip_of {α β : Type} {l : List α} {m : List β} (h : l.length = m.length) {x : α}
    (hx : x ∈ l) : ∃ y, (x, y) ∈ l.zip m := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hi' : i < (l.zip m).length := by
    rw [List.length_zip, ← h, Nat.min_self]
    exact hi
  refine ⟨m[i]'(h ▸ hi), ?_⟩
  have := List.getElem_mem hi'
  rwa [List.getElem_zip] at this

theorem mem_of_atQ {L : List (Nat × Nat)} {t : Nat} {v : Nat × Nat} (h : atQ L t = v) (hv : v ≠ oneQ) :
    v ∈ L := by
  unfold atQ at h
  rw [List.getD_eq_getElem?_getD] at h
  cases e : L[t]? with
  | none =>
    rw [e] at h
    exact absurd h.symm hv
  | some z =>
    rw [e, Option.getD_some] at h
    exact h ▸ List.mem_of_getElem? e

theorem blt_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem beq_of_nbeq {a b : Nat} (h : Nat.beq a b = true) : (a == b) = true :=
  beq_iff_eq.2 (Nat.eq_of_beq_eq_true h)

theorem cube1P_eq {x : Pr} (hx : x.1.size = 64) : cube1P x = cubeQ (encQ x) := by
  unfold cube1P cubeQ
  rw [← encQ_mulP, ← encQ_mulP, ← encQ_oneP, eqQ_enc (size_mulP _ _) size_oneP]

theorem commP_eq {x y : Pr} (hx : x.1.size = 64) (hy : y.1.size = 64) :
    commP x y = eqQ (mulQ (encQ x) (encQ y)) (mulQ (encQ y) (encQ x)) := by
  unfold commP
  rw [← encQ_mulP, ← encQ_mulP, eqQ_enc (size_mulP _ _) (size_mulP _ _)]

theorem map_powsP (x : Pr) : (powsP x).map encQ = powsQ (encQ x) := by
  simp only [powsP, powsQ, List.map_cons, List.map_nil, encQ_mulP, encQ_oneQ]

theorem map_planeP (u v : Pr) : (planeP u v).map encQ = planeQ9 (encQ u) (encQ v) := by
  simp only [planeP, planeQ9, powsP, powsQ, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.map_append, List.append_nil, List.cons_append, List.nil_append, encQ_mulP,
    encQ_oneQ]

theorem isPairP_eq {x y : Pr} (hx : x.1.size = 64) (hy : y.1.size = 64) :
    isPairP x y = isPairQ (encQ x) (encQ y) := by
  unfold isPairP isPairQ
  rw [← map_powsP, memQ_enc (size_powsP hx) hy, cube1P_eq hx, cube1P_eq hy, commP_eq hx hy,
    ← encQ_oneQ, eqQ_enc hx size_oneP]
  rfl

theorem bne_false {p q : Pr} (h : (p != q) = true) : (p == q) = false := by
  revert h
  unfold bne
  cases (p == q) <;> simp

section Twin

variable {ls : List Nat} (hL : ∀ i < 18, D4PlaneP.packA (D4Two.letterArr i) = ls.getD i 0)

include hL

theorem gens_enc : (sGenP ()).map encQ = gensQ ls := by
  rw [sGenP, gensQ]
  simp only [List.map_cons, List.map_nil, encQ_wordP hL]

omit hL in
theorem size_sGenP : ∀ g ∈ sGenP (), g.1.size = 64 := by
  intro g hg
  rw [sGenP] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> exact size_wordP _

omit hL in
theorem size_foldl_sStep (gens : List Pr) : ∀ (par : List (Nat × Nat)) (acc : List Pr),
    (∀ x ∈ acc, x.1.size = 64) → ∀ x ∈ par.foldl (sStep gens) acc, x.1.size = 64
  | [], _, h => h
  | _ :: par, acc, h => size_foldl_sStep gens par _ fun x hx => by
    simp only [sStep, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h x hx
    · exact size_mulP _ _

omit hL in
theorem size_sElems : ∀ x ∈ sElems (), x.1.size = 64 := fun x hx =>
  size_foldl_sStep (sGenP ()) sBfs [ChevOuter.oneP]
    (fun y hy => by
      rw [List.mem_singleton] at hy
      exact hy ▸ size_oneP) x hx

theorem sElems_enc {es : List (Nat × Nat)} (hE : enumQ ls es = true) :
    (sElems ()).map encQ = es := by
  simp only [enumQ, Bool.and_eq_true, List.all_eq_true] at hE
  obtain ⟨⟨hlen, h0⟩, hk⟩ := hE
  have hlen' : es.length = sBfs.length + 1 := Nat.eq_of_beq_eq_true hlen
  have hstep : ∀ n (hn : n < sBfs.length), sBfs[n].1 ≤ n ∧
      es[n + 1]'(by omega) = mulQ (atQ es sBfs[n].1) (atQ (gensQ ls) sBfs[n].2) := by
    intro n hn
    have hz : n < ((sBfs.zip es.tail).zipIdx).length := by
      rw [List.length_zipIdx, List.length_zip, List.length_tail, hlen']
      omega
    have := hk _ (List.getElem_mem hz)
    simp only [List.getElem_zipIdx, List.getElem_zip, List.getElem_tail, Nat.zero_add,
      Bool.and_eq_true, Nat.ble_eq] at this
    exact ⟨by omega, eq_of_eqQ this.2⟩
  have key : ∀ n, n ≤ sBfs.length →
      ((sBfs.take n).foldl (sStep (sGenP ())) [ChevOuter.oneP]).map encQ = es.take (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [List.take_zero, List.foldl_nil, List.map_cons, List.map_nil, encQ_oneQ, List.take_succ,
        List.take_zero, List.nil_append, List.getElem?_eq_getElem (by omega), Option.toList_some,
        ← eq_of_eqQ h0, atQ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some]
    | succ n ih =>
      intro hn
      obtain ⟨hp, he⟩ := hstep n (by omega)
      rw [List.take_succ, List.foldl_append, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.foldl_cons, List.foldl_nil, sStep, List.map_append, List.map_cons, List.map_nil,
        encQ_mulP, ← atQ_map, ← atQ_map, ih (by omega), gens_enc hL,
        List.take_succ (l := es) (i := n + 1), List.getElem?_eq_getElem (by omega),
        Option.toList_some, he, atQ, atQ, D4PlaneP.getD_take _ _ _ _ (by omega)]
      rfl
  have e := key sBfs.length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega)] at e
  exact e

theorem sylowCheck_of {es : List (Nat × Nat)} (hE : enumQ ls es = true) (hS : sylowQ ls es = true) :
    sylowCheck () = true := by
  have hEs := sElems_enc hL hE
  have hgE := size_sElems
  have hgs := gens_enc hL
  unfold sylowQ at hS
  unfold sylowCheck
  dsimp only at hS ⊢
  generalize sElems () = E at hEs hgE ⊢
  generalize sGenP () = gs at hgs ⊢
  subst hEs
  rw [← hgs, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at hS
  obtain ⟨⟨h1, h2⟩, h3⟩ := hS
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨?_, List.Nodup.of_map encQ (nodupQ_nodup h2)⟩, fun x hx => ?_⟩
  · rw [List.length_map] at h1
    exact Nat.eq_of_beq_eq_true h1
  · have h4 := h3 (encQ x) (List.mem_map_of_mem hx)
    rw [List.all_eq_true] at h4 ⊢
    intro g hg
    have h5 := h4 (encQ g) (List.mem_map_of_mem hg)
    rwa [← encQ_mulP, memQ_enc hgE (size_mulP _ _)] at h5

theorem map_classR1 : (classR1P ()).map encQ = classR1.map (wordQ ls) := by
  simp only [classR1P, List.map_map, Function.comp_def, encQ_wordP hL]

theorem map_classR2 : (classR2P ()).map encQ = classR2.map (wordQ ls) := by
  simp only [classR2P, List.map_map, Function.comp_def, encQ_wordP hL]

omit hL in
theorem size_classR1P : ∀ x ∈ classR1P (), x.1.size = 64 := size_mapWordP classR1

omit hL in
theorem size_classR2P : ∀ x ∈ classR2P (), x.1.size = 64 := size_mapWordP classR2

theorem rowOK_eq (E R1 R2 : List Pr) (hgE : ∀ x ∈ E, x.1.size = 64) (hg1 : ∀ x ∈ R1, x.1.size = 64)
    (hg2 : ∀ x ∈ R2, x.1.size = 64) (row : Nat × Nat × Nat × List Nat) :
    rowOK E R1 R2 row = rowQ ls (E.map encQ) (R1.map encQ) (R2.map encQ) row
      (planeQ9 (atQ (E.map encQ) row.1) (atQ (E.map encQ) row.2.1)) := by
  unfold rowOK rowQ
  simp only [atQ_map, List.length_map, ← encQ_wordP hL, ← encQ_mulP, ← encQ_oneQ, ← map_planeP,
    blt_decide]
  rw [eqQ_enc (size_mulP _ _) size_oneP, memQ_enc (size_planeP _ _) (size_mulP _ _),
    memQ_enc (size_planeP _ _) (size_mulP _ _), isPairP_eq (size_getD hgE _) (size_getD hgE _)]

omit hL in
theorem prs_planes {E : List Pr} {prs : List (List (Nat × Nat))} (hP : prsQ (E.map encQ) prs = true) :
    prs = (planeRows.map fun row => planeP (E.getD row.1 ChevOuter.oneP)
      (E.getD row.2.1 ChevOuter.oneP)).map (List.map encQ) := by
  simp only [prsQ, Bool.and_eq_true, List.all_eq_true] at hP
  obtain ⟨hlen, hpl⟩ := hP
  have hlen' : prs.length = planeRows.length := Nat.eq_of_beq_eq_true hlen
  apply List.ext_getElem (by rw [List.length_map, List.length_map, hlen'])
  intro r h1 h2
  have hz : r < (planeRows.zip prs).length := by
    rw [List.length_zip, hlen', Nat.min_self, ← hlen']
    exact h1
  have := hpl _ (List.getElem_mem hz)
  simp only [List.getElem_zip] at this
  rw [List.getElem_map, List.getElem_map, ← (eqLQ_iff _ _).1 this, map_planeP, atQ_map, atQ_map]

theorem rowsCheck_of {es : List (Nat × Nat)} {prs : List (List (Nat × Nat))} {R1 R2 : List (Nat × Nat)}
    (hE : enumQ ls es = true) (hP : prsQ es prs = true) (hR : rowsQ ls es prs R1 R2 = true) :
    rowsCheck () = true := by
  have hEs := sElems_enc hL hE
  have hgE := size_sElems
  unfold rowsQ at hR
  unfold prsQ at hP
  unfold rowsCheck
  dsimp only
  generalize sElems () = E at hEs hgE ⊢
  subst hEs
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, eqLQ_iff, eqLQ_iff] at hR
  obtain ⟨⟨⟨h121, h1⟩, h2⟩, hrows⟩ := hR
  rw [Bool.and_eq_true] at hP
  obtain ⟨hlen, hpl⟩ := hP
  have hlen' : prs.length = planeRows.length := Nat.eq_of_beq_eq_true hlen
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨Nat.eq_of_beq_eq_true h121, fun row hrow => ?_⟩
  obtain ⟨P, hmem⟩ := mem_zip_of hlen'.symm hrow
  have hp1 := List.all_eq_true.1 hpl (row, P) hmem
  have hr := List.all_eq_true.1 hrows (row, P) hmem
  dsimp only at hp1 hr
  have hPe := (eqLQ_iff _ _).1 hp1
  rw [rowOK_eq hL E (classR1P ()) (classR2P ()) hgE size_classR1P size_classR2P row, map_classR1 hL,
    map_classR2 hL, h1, h2, hPe]
  exact hr

end Twin

theorem coverQ_cons (m : Rec) (rest : List Rec) :
    coverQ (m :: rest) = ((!m.2.2.1 || rest.all (pairQ m)) && coverQ rest) :=
  (qrec_and _ _).trans (by rw [qrec_imp, qrec_all]; rfl)

theorem coverQ_pairwise : ∀ {L : List Rec}, coverQ L = true →
    L.Pairwise fun m n => m.2.2.1 = true → pairQ m n = true
  | [], _ => List.Pairwise.nil
  | m :: rest, h => by
    rw [coverQ_cons, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
    refine List.pairwise_cons.2 ⟨fun n hn hm => ?_, coverQ_pairwise h.2⟩
    rcases h.1 with h1 | h1
    · rw [hm] at h1
      exact absurd h1 (by decide)
    · exact h1 n hn

theorem pairQ_eq (m n : Rec) : pairQ m n = (!n.2.2.1 || (!eqQ (mulQ m.2.1 n.2.1) (mulQ n.2.1 m.2.1) ||
    ((Nat.beq m.2.2.2.1 n.1 && Nat.beq n.2.2.2.1 m.1) || shareQ m.2.2.2.2 n.2.2.2.2))) :=
  (qrec_imp _ _).trans (by rw [qrec_imp])

theorem shareQ_spec : ∀ {pk pl : List (Nat × Nat)}, shareQ pk pl = true →
    ∃ a ∈ pk, ∃ b ∈ pl, a.1 = b.1
  | [], _, h => absurd h Bool.false_ne_true
  | a :: pk, pl, h => by
    have e : shareQ (a :: pk) pl = (pl.any (fun b => Nat.beq a.1 b.1) || shareQ pk pl) :=
      (qrec_or _ _).trans (by rw [qrec_any (fun b : Nat × Nat => Nat.beq a.1 b.1)]; rfl)
    rw [e, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨b, hb, h⟩ | h
    · exact ⟨a, List.mem_cons_self, b, hb, Nat.eq_of_beq_eq_true h⟩
    · obtain ⟨c, hc, b, hb, h⟩ := shareQ_spec h
      exact ⟨c, List.mem_cons_of_mem _ hc, b, hb, h⟩

theorem recQ_spec {es : List (Nat × Nat)} {prs : List (List (Nat × Nat))} {m : Rec}
    (h : recQ es prs m = true) :
    m.2.2.1 = (cubeQ m.2.1 && !eqQ m.2.1 oneQ) ∧ atQ es m.2.2.2.1 = mulQ m.2.1 m.2.1 ∧
      ∀ p ∈ m.2.2.2.2, p.1 < prs.length ∧ atQ (prs.getD p.1 []) p.2 = m.2.1 := by
  simp only [recQ, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, -⟩, h3⟩, h4⟩ := h
  exact ⟨h1, eq_of_eqQ h3, fun p hp => ⟨(h4 p hp).1, eq_of_eqQ (h4 p hp).2⟩⟩

theorem recs_spec {es : List (Nat × Nat)} {prs : List (List (Nat × Nat))} {recs : List Rec}
    (hM : recsQ es prs recs = true) :
    recs.map (fun m => m.2.1) = es ∧ ∀ m ∈ recs, atQ es m.1 = m.2.1 ∧ recQ es prs m = true := by
  simp only [recsQ, Bool.and_eq_true, List.all_eq_true] at hM
  obtain ⟨h1, h2⟩ := hM
  have hmap := (eqLQ_iff _ _).1 h1
  refine ⟨hmap, fun m hm => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hm
  have hz : k < recs.zipIdx.length := by
    rw [List.length_zipIdx]
    exact hk
  have := h2 _ (List.getElem_mem hz)
  simp only [List.getElem_zipIdx, Nat.zero_add, Bool.and_eq_true] at this
  obtain ⟨hb, hr⟩ := this
  refine ⟨?_, hr⟩
  rw [Nat.eq_of_beq_eq_true hb, ← hmap, atQ, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk]
  rfl

theorem cover_pair {E : List Pr} {planes : List (List Pr)} {prs : List (List (Nat × Nat))}
    (hgE : ∀ x ∈ E, x.1.size = 64) (hgp : ∀ P ∈ planes, ∀ x ∈ P, x.1.size = 64)
    (hprs : prs = planes.map (List.map encQ)) {x y : Pr} (hx : x ∈ E) (hy : y ∈ E)
    (nx : eqQ (encQ x) oneQ = false) (ny : eqQ (encQ y) oneQ = false) {m n : Rec}
    (hmx : m.2.1 = encQ x) (hny : n.2.1 = encQ y)
    (hm : recQ (E.map encQ) prs m = true) (hn : atQ (E.map encQ) n.1 = n.2.1)
    (hD : m.2.2.2.1 = n.1 ∨ ∃ a ∈ m.2.2.2.2, ∃ b ∈ n.2.2.2.2, a.1 = b.1)
    (hnr : recQ (E.map encQ) prs n = true) :
    (powsP x).contains y = true ∨ ∃ P ∈ planes, x ∈ P ∧ y ∈ P := by
  obtain ⟨-, hsq, hpl⟩ := recQ_spec hm
  obtain ⟨-, -, hpl'⟩ := recQ_spec hnr
  rcases hD with hD | ⟨a, ha, b, hb, hab⟩
  · left
    rw [hD, hn, hny, hmx, ← encQ_mulP] at hsq
    have e := enc_inj (hgE y hy) (size_mulP _ _) hsq
    rw [List.contains_iff_mem, e]
    simp [powsP]
  · right
    obtain ⟨hr, hax⟩ := hpl a ha
    obtain ⟨-, hby⟩ := hpl' b hb
    rw [← hab] at hby
    have hr' : a.1 < planes.length := by rw [hprs, List.length_map] at hr; exact hr
    have hget : prs.getD a.1 [] = (planes[a.1]'hr').map encQ := by
      rw [hprs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hr']
      rfl
    have hP := List.getElem_mem hr'
    refine ⟨planes[a.1]'hr', hP, ?_, ?_⟩
    · rw [hget, hmx] at hax
      have := mem_of_atQ hax fun e => by rw [e, eqQ_self] at nx; exact Bool.noConfusion nx
      exact (mem_map_enc (hgp _ hP) (hgE x hx)).1 this
    · rw [hget, hny] at hby
      have := mem_of_atQ hby fun e => by rw [e, eqQ_self] at ny; exact Bool.noConfusion ny
      exact (mem_map_enc (hgp _ hP) (hgE y hy)).1 this

theorem cover_core {E : List Pr} {planes : List (List Pr)} {prs : List (List (Nat × Nat))}
    {recs : List Rec} (hgE : ∀ x ∈ E, x.1.size = 64) (hgp : ∀ P ∈ planes, ∀ x ∈ P, x.1.size = 64)
    (hprs : prs = planes.map (List.map encQ)) (hM : recsQ (E.map encQ) prs recs = true)
    (hC : coverQ recs = true) {x y : Pr} (hx : x ∈ E) (hy : y ∈ E) (cx : cube1P x = true)
    (cy : cube1P y = true) (nx : (x != ChevOuter.oneP) = true) (ny : (y != ChevOuter.oneP) = true) :
    coveredP planes x y = true := by
  have hgx := hgE x hx
  have hgy := hgE y hy
  obtain ⟨hmap, hrs⟩ := recs_spec hM
  have hpw := coverQ_pairwise hC
  have nx' : eqQ (encQ x) oneQ = false := by rw [← encQ_oneQ, eqQ_enc hgx size_oneP]; exact bne_false nx
  have ny' : eqQ (encQ y) oneQ = false := by rw [← encQ_oneQ, eqQ_enc hgy size_oneP]; exact bne_false ny
  rw [cube1P_eq hgx] at cx
  rw [cube1P_eq hgy] at cy
  have hrec : ∀ z ∈ E, ∃ k, ∃ hk : k < recs.length, recs[k].2.1 = encQ z := by
    intro z hz
    have h1 : encQ z ∈ recs.map fun m => m.2.1 := by rw [hmap]; exact List.mem_map_of_mem hz
    obtain ⟨m, hm, e⟩ := List.mem_map.1 h1
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hm
    exact ⟨k, hk, e⟩
  obtain ⟨i, hi, hix⟩ := hrec x hx
  obtain ⟨j, hj, hjy⟩ := hrec y hy
  have hcb : ∀ k (hk : k < recs.length) (z : Pr), recs[k].2.1 = encQ z → cubeQ (encQ z) = true →
      eqQ (encQ z) oneQ = false → recs[k].2.2.1 = true := by
    intro k hk z e c n
    rw [(recQ_spec (hrs _ (List.getElem_mem hk)).2).1, e, c, n]
    rfl
  unfold coveredP
  rw [Bool.or_eq_true, Bool.or_eq_true]
  by_cases hxy : x = y
  · left; left
    rw [List.contains_iff_mem, ← hxy]
    simp [powsP]
  by_cases hc : commP x y = true
  swap
  · left; right
    simpa using hc
  rw [commP_eq hgx hgy, eqQ_iff] at hc
  have hij : i ≠ j := by
    rintro rfl
    exact hxy (enc_inj hgx hgy (hix.symm.trans hjy))
  have hD : recs[i].2.2.2.1 = recs[j].1 ∨
      ∃ a ∈ recs[i].2.2.2.2, ∃ b ∈ recs[j].2.2.2.2, a.1 = b.1 := by
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have hp := List.pairwise_iff_getElem.1 hpw i j hi hj h (hcb i hi x hix cx nx')
      rw [pairQ_eq, hcb j hj y hjy cy ny', hix, hjy, hc, eqQ_self] at hp
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true] at hp
      rcases hp with ⟨h1, -⟩ | h1
      · exact Or.inl (Nat.eq_of_beq_eq_true h1)
      · exact Or.inr (shareQ_spec h1)
    · have hp := List.pairwise_iff_getElem.1 hpw j i hj hi h (hcb j hj y hjy cy ny')
      rw [pairQ_eq, hcb i hi x hix cx nx', hix, hjy, ← hc, eqQ_self] at hp
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true] at hp
      rcases hp with ⟨-, h1⟩ | h1
      · exact Or.inl (Nat.eq_of_beq_eq_true h1)
      · obtain ⟨b, hb, a, ha, e⟩ := shareQ_spec h1
        exact Or.inr ⟨a, ha, b, hb, e.symm⟩
  rcases cover_pair hgE hgp hprs hx hy nx' ny' hix hjy (hrs _ (List.getElem_mem hi)).2
      (hrs _ (List.getElem_mem hj)).1 hD (hrs _ (List.getElem_mem hj)).2 with h | h
  · left; left
    exact h
  · right
    rw [List.any_eq_true]
    obtain ⟨P, hP, h1, h2⟩ := h
    refine ⟨P, hP, ?_⟩
    rw [Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem]
    exact ⟨h1, h2⟩

theorem cover_gen (E : List Pr) (hgE : ∀ x ∈ E, x.1.size = 64) {es : List (Nat × Nat)}
    {prs : List (List (Nat × Nat))} {recs : List Rec} (hEs : E.map encQ = es)
    (hP : prsQ es prs = true) (hM : recsQ es prs recs = true) (hC : coverQ recs = true) :
    (let Om := (E.filter cube1P).filter fun x => x != ChevOuter.oneP
     let planes := planeRows.map fun row =>
       planeP (E.getD row.1 ChevOuter.oneP) (E.getD row.2.1 ChevOuter.oneP)
     Om.all fun x => Om.all fun y => coveredP planes x y) = true := by
  subst hEs
  have hgp : ∀ P ∈ planeRows.map (fun row =>
      planeP (E.getD row.1 ChevOuter.oneP) (E.getD row.2.1 ChevOuter.oneP)), ∀ x ∈ P,
      x.1.size = 64 := by
    intro P hP
    obtain ⟨row, -, rfl⟩ := List.mem_map.1 hP
    exact size_planeP _ _
  dsimp only
  rw [List.all_eq_true]
  intro x hx
  rw [List.all_eq_true]
  intro y hy
  simp only [List.mem_filter] at hx hy
  exact cover_core hgE hgp (prs_planes hP) hM hC hx.1.1 hy.1.1 hx.1.2 hy.1.2 hx.2 hy.2

section Twin2

variable {ls : List Nat} (hL : ∀ i < 18, D4PlaneP.packA (D4Two.letterArr i) = ls.getD i 0)

include hL

theorem coverCheck_of {es : List (Nat × Nat)} {prs : List (List (Nat × Nat))} {recs : List Rec}
    (hE : enumQ ls es = true) (hP : prsQ es prs = true) (hM : recsQ es prs recs = true)
    (hC : coverQ recs = true) : coverCheck () = true := by
  have hEs := sElems_enc hL hE
  have hgE := size_sElems
  unfold coverCheck
  generalize sElems () = E at hEs hgE ⊢
  exact cover_gen E hgE hEs hP hM hC

theorem planeCoverCheck_of {es : List (Nat × Nat)} {prs : List (List (Nat × Nat))}
    {R1 R2 : List (Nat × Nat)} {recs : List Rec} (hE : enumQ ls es = true)
    (hS : sylowQ ls es = true) (hP : prsQ es prs = true) (hR : rowsQ ls es prs R1 R2 = true)
    (hM : recsQ es prs recs = true) (hC : coverQ recs = true) : planeCoverCheck () = true := by
  unfold planeCoverCheck
  rw [sylowCheck_of hL hE hS, rowsCheck_of hL hE hP hR, coverCheck_of hL hE hP hM hC]
  all_goals rfl

theorem map_wordQ (L : List (List Nat)) : L.map (wordQ ls) = (L.map ChevOuter.wordP).map encQ := by
  simp only [List.map_map, Function.comp_def, encQ_wordP hL]

theorem map_invQ (L : List (List Nat)) :
    L.map (fun w => wordQ ls (invW w)) = (L.map fun w => ChevOuter.wordP (invW w)).map encQ := by
  simp only [List.map_map, Function.comp_def, encQ_wordP hL]

omit hL in
theorem foldl_slp (gens invs : List Pr) : ∀ (ids : List Nat) (acc : Pr),
    ids.foldl (fun a i => mulQ a (if i % 2 = 0 then atQ (gens.map encQ) (i / 2)
      else atQ (invs.map encQ) (i / 2))) (encQ acc) =
    encQ (ids.foldl (fun a i => ChevOuter.mulP a (if i % 2 = 0 then gens.getD (i / 2) ChevOuter.oneP
      else invs.getD (i / 2) ChevOuter.oneP)) acc)
  | [], _ => rfl
  | i :: ids, acc => by
    rw [List.foldl_cons, List.foldl_cons, ← foldl_slp gens invs ids, encQ_mulP, apply_ite encQ,
      atQ_map, atQ_map]

omit hL in
theorem slp_enc (gens invs : List Pr) (ids : List Nat) :
    slpQ (gens.map encQ) (invs.map encQ) ids = encQ (slpP gens invs ids) := by
  unfold slpQ slpP
  rw [← encQ_oneQ]
  exact foldl_slp gens invs ids ChevOuter.oneP

omit hL in
theorem size_slpP (gens invs : List Pr) (ids : List Nat) : (slpP gens invs ids).1.size = 64 := by
  unfold slpP
  exact size_foldl _ (fun _ _ => size_mulP _ _) ids _ size_oneP

theorem cls_ne (w : List Nat) (h : (!eqQ (wordQ ls w) oneQ) = true) :
    (ChevOuter.wordP w != ChevOuter.oneP) = true := by
  rw [← encQ_wordP hL, ← encQ_oneQ, eqQ_enc (size_wordP _) size_oneP] at h
  unfold bne
  exact h

theorem cls_frob (W : List (List Nat)) (h : W.all (fun w => Nat.beq (wordQ ls w).2 0) = true) :
    W.all (fun w => (ChevOuter.wordP w).2 == 0) = true := by
  rw [List.all_eq_true] at h ⊢
  intro w hw
  have h1 := h w hw
  rw [← encQ_wordP hL] at h1
  exact beq_of_nbeq h1

theorem cls_fix (r : List Nat) (W : List (List Nat))
    (h : (W.map (wordQ ls)).all (fun s => eqQ (mulQ (wordQ ls r) s) (mulQ s (wordQ ls r))) = true) :
    (W.map ChevOuter.wordP).all (fun s => ChevOuter.mulP (ChevOuter.wordP r) s ==
      ChevOuter.mulP s (ChevOuter.wordP r)) = true := by
  rw [List.all_map, List.all_eq_true] at h ⊢
  intro w hw
  have h1 := h w hw
  simp only [Function.comp_apply, ← encQ_wordP hL, ← encQ_mulP] at h1 ⊢
  rwa [eqQ_enc (size_mulP _ _) (size_mulP _ _)] at h1

theorem cls_inv (W : List (List Nat))
    (h : ((W.map (wordQ ls)).zip (W.map fun w => wordQ ls (invW w))).all
      (fun q => eqQ (mulQ q.1 q.2) oneQ) = true) :
    W.all (fun w => ChevOuter.mulP (ChevOuter.wordP w) (ChevOuter.wordP (invW w)) == ChevOuter.oneP) =
      true := by
  rw [List.zip_map', List.all_map, List.all_eq_true] at h
  rw [List.all_eq_true]
  intro w hw
  have h1 := h w hw
  simp only [Function.comp_apply, ← encQ_wordP hL, ← encQ_mulP, ← encQ_oneQ] at h1
  rwa [eqQ_enc (size_mulP _ _) size_oneP] at h1

theorem cls_slp (W : List (List Nat)) (S : List (Nat × List Nat))
    (h : S.all (fun x => Nat.blt x.1 18 && eqQ (slpQ (W.map (wordQ ls))
      (W.map fun w => wordQ ls (invW w)) x.2) (D4PlaneP.letP ls x.1, 0)) = true) :
    S.all (fun x => decide (x.1 < 18) && slpP (W.map ChevOuter.wordP)
      (W.map fun w => ChevOuter.wordP (invW w)) x.2 == (D4Two.letterArr x.1, 0)) = true := by
  rw [List.all_eq_true] at h ⊢
  intro x hx
  have h1 := h x hx
  rw [Bool.and_eq_true] at h1 ⊢
  refine ⟨by rw [← blt_decide]; exact h1.1, ?_⟩
  have h2 := h1.2
  rw [map_wordQ hL, map_invQ hL, slp_enc, ← D4PlaneP.packA_letterArr hL, ← encQ_mk,
    eqQ_enc (q := (D4Two.letterArr x.1, 0)) (size_slpP _ _ _) (D4PlaneP.size_letterArr _)] at h2
  exact h2

omit hL in
theorem cls_cov (S : List (Nat × List Nat))
    (h : (List.range 18).all (fun k => S.any fun x => Nat.beq x.1 k) = true) :
    (List.range 18).all (fun k => S.any fun x => x.1 == k) = true := by
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have h1 := h k hk
  rw [List.any_eq_true] at h1 ⊢
  obtain ⟨x, hx, e⟩ := h1
  exact ⟨x, hx, beq_of_nbeq e⟩

theorem classCheck_of {cg ci : List (List (Nat × Nat))} {i : Nat} (h : classQ ls cg ci i = true) :
    classCheck i = true := by
  unfold classQ at h
  dsimp only at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hg, hi⟩, hr1⟩, hr2⟩, hfr⟩, hc1⟩, hc2⟩, hinv⟩, hslp⟩, hcov⟩ := h
  rw [eqLQ_iff] at hg hi
  rw [← hg, List.map_append, List.take_left' (List.length_map _)] at hc1
  rw [← hg, List.map_append, List.drop_left' (List.length_map _)] at hc2
  rw [← hg, ← hi] at hinv hslp
  unfold classCheck
  dsimp only
  rw [cls_ne hL _ hr1, cls_ne hL _ hr2, cls_frob hL _ hfr, cls_fix hL _ _ hc1, cls_fix hL _ _ hc2,
    cls_inv hL _ hinv, cls_slp hL _ _ hslp, cls_cov _ hcov]
  all_goals rfl

theorem classChecks_of {cg ci : List (List (Nat × Nat))}
    (h : (List.range 6).all (classQ ls cg ci) = true) : classChecks () = true := by
  unfold classChecks
  rw [List.all_eq_true] at h ⊢
  exact fun i hi => classCheck_of hL (h i hi)

omit hL in
theorem center_gen {E gs : List Pr} {es G : List (Nat × Nat)} (hEs : E.map encQ = es)
    (hgE : ∀ x ∈ E, x.1.size = 64) (hgs : gs.map encQ = G) (hgg : ∀ g ∈ gs, g.1.size = 64)
    (h : (let C := es.filter fun z => G.all fun g => eqQ (mulQ z g) (mulQ g z)
      Nat.beq C.length 3 && C.all fun z => Nat.beq z.2 0) = true) :
    (decide ((E.filter fun z => gs.all fun g => commP z g).length = 3) &&
      (E.filter fun z => gs.all fun g => commP z g).all fun z => z.2 == 0) = true := by
  subst hEs hgs
  have hf : (E.map encQ).filter (fun z => (gs.map encQ).all fun g => eqQ (mulQ z g) (mulQ g z)) =
      (E.filter fun z => gs.all fun g => commP z g).map encQ := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro z hz
    simp only [Function.comp_apply, List.all_map]
    exact D4PlaneP.all_congr_mem fun g hg => (commP_eq (hgE z hz) (hgg g hg)).symm
  dsimp only at h
  rw [hf, List.length_map, List.all_map, Bool.and_eq_true] at h
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun z hz => ?_⟩
  rw [List.all_eq_true] at h
  exact beq_of_nbeq (h.2 z hz)

theorem centerCheck_of {es : List (Nat × Nat)} (hE : enumQ ls es = true) (hS : sylowQ ls es = true)
    (h : centerQ ls es = true) : centerCheck () = true := by
  have hEs := sElems_enc hL hE
  have hgE := size_sElems
  have hgs := gens_enc hL
  have hgg := size_sGenP
  unfold centerCheck centralP
  dsimp only
  rw [sylowCheck_of hL hE hS, Bool.true_and]
  unfold centerQ at h
  generalize sElems () = E at hEs hgE ⊢
  generalize sGenP () = gs at hgs hgg ⊢
  exact center_gen hEs hgE hgs hgg h

end Twin2

end CFSG.KC.HD4Q2K

end
