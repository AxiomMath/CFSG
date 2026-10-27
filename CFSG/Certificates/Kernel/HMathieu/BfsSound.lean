module

public import Certificates.Data.Kernel.HMathieu.Bfs
public import CFSG.Quasithin.Background.HMathieuArr
public import Std.Data.HashMap.Lemmas
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu

theorem vpK_spec {p : Nat} (h : vpK p = true) : p >>> 120 = 0 ∧ ∀ i < 24, pg 5 (mask 5) p i < 24 := by
  unfold vpK at h
  rw [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  refine ⟨h.1, fun i hi => ?_⟩
  have := h.2 i (List.mem_range.2 hi)
  rwa [Nat.blt_eq] at this

theorem vpK_of {p : Nat} (h1 : p >>> 120 = 0) (h2 : ∀ i < 24, pg 5 (mask 5) p i < 24) :
    vpK p = true := by
  unfold vpK
  rw [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true]
  refine ⟨h1, fun i hi => ?_⟩
  rw [Nat.blt_eq]
  exact h2 i (List.mem_range.1 hi)

theorem pg_pc24 (p q : Nat) {i : Nat} (hi : i < 24) :
    pg 5 (mask 5) (pc24 p q) i = pg 5 (mask 5) p (pg 5 (mask 5) q i) :=
  PF.pg_pcomp (by norm_num) hi

theorem vpK_pc24 {p q : Nat} (hp : vpK p = true) (hq : vpK q = true) : vpK (pc24 p q) = true := by
  refine vpK_of (PF.pcomp_shr p q (by norm_num) (by norm_num)) fun i hi => ?_
  rw [pg_pc24 p q hi]
  exact (vpK_spec hp).2 _ ((vpK_spec hq).2 i hi)

theorem pg_id {i : Nat} (hi : i < 24) : pg 5 (mask 5) (pidn 24 5) i = i :=
  PF.pg_pidn (by norm_num) (by norm_num) hi

theorem vpK_id : vpK (pidn 24 5) = true :=
  vpK_of (PF.pidn_shr (by norm_num) (by norm_num)) fun i hi => by rw [pg_id hi]; exact hi

theorem eq_of_pg {p q : Nat} (hp : vpK p = true) (hq : vpK q = true)
    (h : ∀ i < 24, pg 5 (mask 5) p i = pg 5 (mask 5) q i) : p = q :=
  PF.eq_of_fields (n := 24) (by norm_num) (vpK_spec hp).1 (vpK_spec hq).1 h

theorem size_unpk (p : Nat) : (unpk p).size = 24 := by simp [unpk]

theorem unpk_get (p : Nat) {i : Nat} (hi : i < 24) : (unpk p)[i]! = pg 5 (mask 5) p i := by
  rw [getElem!_pos (unpk p) i (by rw [size_unpk]; exact hi)]
  simp [unpk]

theorem unpk_inj {p q : Nat} (hp : vpK p = true) (hq : vpK q = true) (h : unpk p = unpk q) :
    p = q :=
  eq_of_pg hp hq fun i hi => by rw [← unpk_get p hi, ← unpk_get q hi, h]

theorem compArr_unpk (p : Nat) {q : Nat} (hq : vpK q = true) :
    compArr (unpk p) (unpk q) = unpk (pc24 p q) := by
  apply Array.ext (by simp [compArr, size_unpk])
  intro i h1 h2
  have hi : i < 24 := by simpa [size_unpk] using h2
  rw [← getElem!_pos (unpk (pc24 p q)) i h2, unpk_get _ hi, pg_pc24 p q hi]
  simp only [compArr, Array.getElem_map]
  rw [← getElem!_pos (unpk q) i (by rw [size_unpk]; exact hi), unpk_get q hi,
    unpk_get p ((vpK_spec hq).2 i hi)]

theorem range_eq_unpk : Array.range 24 = unpk (pidn 24 5) := by
  apply Array.ext (by simp [size_unpk])
  intro i h1 h2
  have hi : i < 24 := by simpa using h1
  rw [← getElem!_pos (unpk _) i h2, unpk_get _ hi, pg_id hi, Array.getElem_range]

@[expose] def BRel (st : Array (Array Nat) × Std.HashMap (Array Nat) Nat × List (Array Nat))
    (sp : List Nat × List Nat) : Prop :=
  st.1 = (sp.1.reverse.map unpk).toArray ∧ (∀ y, st.2.1.contains y = true ↔ y ∈ sp.1.map unpk) ∧
    (∀ p ∈ sp.1, vpK p = true) ∧ st.2.2 = sp.2.map unpk ∧ ∀ p ∈ sp.2, vpK p = true

theorem brel_gen {st : Array (Array Nat) × Std.HashMap (Array Nat) Nat × List (Array Nat)}
    {sp : List Nat × List Nat} (h : BRel st sp) {x g : Nat} (hx : vpK x = true)
    (hg : vpK g = true) :
    BRel (if st.2.1.contains (compArr (unpk g) (unpk x)) then st
      else (st.1.push (compArr (unpk g) (unpk x)),
        st.2.1.insert (compArr (unpk g) (unpk x)) st.1.size,
        compArr (unpk g) (unpk x) :: st.2.2))
      (if sp.1.contains (pc24 g x) then sp else (pc24 g x :: sp.1, pc24 g x :: sp.2)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [compArr_unpk g hx]
  have hy := vpK_pc24 hg hx
  have hc : st.2.1.contains (unpk (pc24 g x)) = sp.1.contains (pc24 g x) := by
    rw [Bool.eq_iff_iff, h2, List.contains_iff_mem, List.mem_map]
    constructor
    · rintro ⟨p, hp, e⟩
      rwa [← unpk_inj (h3 p hp) hy e]
    · intro hm
      exact ⟨_, hm, rfl⟩
  rw [hc]
  cases sp.1.contains (pc24 g x)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, fun y => ?_, ?_, ?_, ?_⟩
    · simp [h1, List.reverse_cons]
    · rw [Std.HashMap.contains_insert, Bool.or_eq_true, h2, beq_iff_eq]
      simp [eq_comm]
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hy
      · exact h3 p hp
    · simp [h4]
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hy
      · exact h5 p hp
  · exact ⟨h1, h2, h3, h4, h5⟩

theorem brel_point {gs : List Nat} (hgs : ∀ g ∈ gs, vpK g = true) {x : Nat} (hx : vpK x = true) :
    ∀ (st : Array (Array Nat) × Std.HashMap (Array Nat) Nat × List (Array Nat))
      (sp : List Nat × List Nat), BRel st sp →
      BRel ((gs.map unpk).foldl (fun st' g =>
          if st'.2.1.contains (compArr g (unpk x)) then st'
          else (st'.1.push (compArr g (unpk x)), st'.2.1.insert (compArr g (unpk x)) st'.1.size,
            compArr g (unpk x) :: st'.2.2)) st) (bfsStep gs sp x) := by
  induction gs with
  | nil => intro st sp h; exact h
  | cons g gs ih =>
    intro st sp h
    rw [List.map_cons, List.foldl_cons]
    unfold bfsStep
    rw [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) _ _
      (brel_gen h hx (hgs g List.mem_cons_self))

theorem brel_round {gs : List Nat} (hgs : ∀ g ∈ gs, vpK g = true) :
    ∀ (fr : List Nat), (∀ p ∈ fr, vpK p = true) →
      ∀ (st : Array (Array Nat) × Std.HashMap (Array Nat) Nat × List (Array Nat))
      (sp : List Nat × List Nat), BRel st sp →
      BRel ((fr.map unpk).foldl (fun st x => (gs.map unpk).foldl (fun st' g =>
          if st'.2.1.contains (compArr g x) then st'
          else (st'.1.push (compArr g x), st'.2.1.insert (compArr g x) st'.1.size,
            compArr g x :: st'.2.2)) st) st) (fr.foldl (bfsStep gs) sp) := by
  intro fr
  induction fr with
  | nil => intro _ st sp h; exact h
  | cons x fr ih =>
    intro hfr st sp h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    exact ih (fun p hp => hfr p (List.mem_cons_of_mem x hp)) _ _
      (brel_point hgs (hfr x List.mem_cons_self) st sp h)

theorem go_eq {gs : List Nat} (hgs : ∀ g ∈ gs, vpK g = true) :
    ∀ (fuel : Nat) (acc : Array (Array Nat)) (seen : Std.HashMap (Array Nat) Nat)
      (racc fr : List Nat), BRel (acc, seen, []) (racc, []) → (∀ p ∈ fr, vpK p = true) →
      bfsClosure.go (gs.map unpk) fuel acc seen (fr.map unpk) =
        ((bfsP gs fuel racc fr).reverse.map unpk).toArray := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc seen racc fr h _
    rw [bfsClosure.go, bfsP]
    exact h.1
  | succ f ih =>
    intro acc seen racc fr h hfr
    cases fr with
    | nil =>
      rw [List.map_nil, bfsClosure.go, bfsP]
      exact h.1
    | cons x xs =>
      have R := brel_round hgs (x :: xs) hfr _ _ h
      rw [List.map_cons, bfsClosure.go, bfsP]
      · rw [← List.map_cons]
        generalize List.foldl (bfsStep gs) (racc, []) (x :: xs) = sp at R ⊢
        generalize List.foldl _ (acc, seen, []) (List.map unpk (x :: xs)) = st at R ⊢
        obtain ⟨a, s, n⟩ := st
        obtain ⟨r1, r2⟩ := sp
        obtain ⟨h1, h2, h3, h4, h5⟩ := R
        simp only at h1 h2 h3 h4 h5 ⊢
        rw [h4, ← List.map_reverse]
        exact ih a s r1 r2.reverse ⟨h1, h2, h3, rfl, by simp⟩
          (fun p hp => h5 p (List.mem_reverse.1 hp))
      · simp

theorem bfsClosure_eq {gs : List Nat} (hgs : ∀ g ∈ gs, vpK g = true) (fuel : Nat) :
    bfsClosure 24 (gs.map unpk) fuel =
      ((bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse.map unpk).toArray := by
  unfold bfsClosure
  simp only
  rw [range_eq_unpk, ← List.map_singleton (f := unpk)]
  refine go_eq hgs fuel _ _ [pidn 24 5] [pidn 24 5] ⟨rfl, fun y => ?_, ?_, rfl, by simp⟩ ?_
  · simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
      beq_iff_eq, List.map_cons, List.map_nil, List.mem_singleton]
    exact eq_comm
  · simpa using vpK_id
  · simpa using vpK_id

end CFSG.KC.HMathieu

end
