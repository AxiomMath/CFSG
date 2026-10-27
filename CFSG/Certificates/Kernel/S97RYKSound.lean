module

public import Certificates.Data.Kernel.S97RYK
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.SporSch.TblSound
public import CFSG.Certificates.Kernel.LocalQTPermWCodes

public section

namespace CFSG.KC.S97RYK

open CFSG.KC.Enum CFSG.KC.LQT.PW CFSG.KS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.CGT.Timmesfeld75.WCCheck CFSG.LargeExtraspecial.S11.PairCheck

variable {n : Nat}

theorem strictK_eq {α : Type} (y : Nat) (k : Nat → α) : strictK y k = k y := by
  cases y <;> rfl

theorem bIfK_eq {α : Type} (c : Bool) (t e : α) : bIfK c t e = if c then t else e := by
  cases c <;> rfl

theorem forceL_eq {α : Type} : ∀ (L : List Nat) (k : List Nat → α), forceL L k = k L
  | [], _ => rfl
  | x :: L, k => by
    change strictK x (fun y => forceL L fun L' => k (y :: L')) = k (x :: L)
    rw [strictK_eq, forceL_eq L]

theorem memK_iff (S : List Nat) (y : Nat) : memK S y = true ↔ y ∈ S := by
  induction S with
  | nil =>
    refine ⟨fun h => ?_, fun h => absurd h List.not_mem_nil⟩
    exact absurd h Bool.false_ne_true
  | cons a S ih =>
    have e : memK (a :: S) y = bIf(Nat.beq a y, true, memK S y) := rfl
    rw [e, List.mem_cons]
    cases h : Nat.beq a y
    · have : a ≠ y := fun e' => by rw [e', Nat.beq_refl] at h; cases h
      change memK S y = true ↔ _
      rw [ih]
      exact ⟨Or.inr, fun h' => h'.resolve_left (Ne.symm this)⟩
    · exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h).symm, fun _ => rfl⟩

theorem validT_iff {t : Table} : validT n t = true ↔ t.size = n ∧ ∀ i < n, ap t i < n := by
  unfold validT
  rw [bAnd_iff, Raw.Orb.allN_iff]
  simp only [Nat.beq_eq, Nat.blt_eq]

theorem ap_compT' (P Q : Table) {i : Nat} (hi : i < n) : ap (compT n P Q) i = ap P (ap Q i) := by
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem validT_compT {P Q : Table} (hP : validT n P = true) (hQ : validT n Q = true) :
    validT n (compT n P Q) = true := by
  rw [validT_iff] at hP hQ ⊢
  refine ⟨by simp [compT], fun i hi => ?_⟩
  rw [ap_compT' P Q hi]
  exact hP.2 _ (hQ.2 i hi)

theorem ap_idT (hn : n < 2 ^ 32) {i : Nat} (hi : i < n) : ap (idT n) i = i := by
  unfold ap idT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega)]

theorem validT_idT (hn : n < 2 ^ 32) : validT n (idT n) = true := by
  rw [validT_iff]
  refine ⟨by simp [idT], fun i hi => ?_⟩
  rw [ap_idT hn hi]
  exact hi

theorem fld_encK (t : Table) :
    PF.Fld 5 (encK n t) (fun i => if i < n then Nat.mod (ap t i) 32 else 0) :=
  PF.fld_ofFnW 5 _ (fun i => Nat.mod_lt _ (by norm_num)) n

theorem pg_encK {t : Table} {i : Nat} (hi : i < n) : pg 5 (mask 5) (encK n t) i = ap t i % 32 := by
  have h := PF.pg_of_fld (i := i) (fld_encK (n := n) t)
    (by simp only [hi, ↓reduceIte]; exact Nat.mod_lt _ (by norm_num))
  simp only [hi, ↓reduceIte] at h
  exact h

theorem imgW_encK_lt {t : Table} {i : Nat} (hi : i < n) : imgW 5 (encK n t) i = ap t i % 32 :=
  pg_encK hi

theorem imgW_encK_ge {t : Table} {i : Nat} (hi : ¬i < n) : imgW 5 (encK n t) i = 0 := by
  rw [encK, ofFnW_eq]
  exact imgW_orW_none (fun i _ => Nat.mod_lt _ (by norm_num)) fun j hj e => hi (e ▸ hj)

theorem encK_compT (h32 : n < 32) {P Q : Table} (hQ : validT n Q = true) :
    encK n (compT n P Q) = mulK n (encK n P) (encK n Q) := by
  have hQ' := (validT_iff.1 hQ).2
  have hm : PF.Fld 5 (mulK n (encK n P) (encK n Q))
      (fun i => if i < n then imgW 5 (encK n P) (imgW 5 (encK n Q) i) else 0) :=
    PF.fld_ofFnW 5 _ (fun i => by rw [PF.imgW_eq]; exact PF.pg_lt _ _ _) n
  refine PF.eq_of_fld (by norm_num) (fld_encK _) (PF.fld_congr hm fun i => ?_)
  by_cases hi : i < n
  · simp only [hi, ↓reduceIte, PF.imgW_eq]
    have hq := hQ' i hi
    rw [pg_encK hi, Nat.mod_eq_of_lt (by omega), pg_encK hq, ap_compT' P Q hi]
    rfl
  · simp only [hi, ↓reduceIte]

theorem encK_inj (h32 : n < 32) {P Q : Table} (hP : validT n P = true) (hQ : validT n Q = true)
    (h : encK n P = encK n Q) : P = Q := by
  obtain ⟨hPs, hPr⟩ := validT_iff.1 hP
  obtain ⟨hQs, hQr⟩ := validT_iff.1 hQ
  have hap : ∀ i < n, ap P i = ap Q i := fun i hi => by
    have e := congrArg (fun X => pg 5 (mask 5) X i) h
    simp only [pg_encK hi] at e
    rwa [Nat.mod_eq_of_lt (by have := hPr i hi; omega),
      Nat.mod_eq_of_lt (by have := hQr i hi; omega)] at e
  apply Array.ext (by rw [hPs, hQs])
  intro i h1 h2
  have e := hap i (by omega)
  unfold ap at e
  rw [getElem!_pos P i h1, getElem!_pos Q i h2] at e
  exact UInt32.toNat_inj.1 e

theorem beq_encK (h32 : n < 32) {P Q : Table} (hP : validT n P = true) (hQ : validT n Q = true) :
    (P == Q) = Nat.beq (encK n P) (encK n Q) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  exact ⟨fun h => h ▸ rfl, encK_inj h32 hP hQ⟩

theorem memL_encK (h32 : n < 32) {E : List Table} {t : Table} (hE : ∀ x ∈ E, validT n x = true)
    (ht : validT n t = true) : memL E t = memK (E.map (encK n)) (encK n t) := by
  rw [Bool.eq_iff_iff, memK_iff, memL, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by rw [beq_iff_eq.1 e]⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, beq_iff_eq.2 (encK_inj h32 (hE x hx) ht e)⟩

theorem commT_encK (h32 : n < 32) {x y : Table} (hx : validT n x = true) (hy : validT n y = true) :
    commT n x y = commK n (encK n x) (encK n y) := by
  unfold commT commK
  rw [beq_encK h32 (validT_compT hx hy) (validT_compT hy hx), encK_compT h32 hy,
    encK_compT h32 hx]

theorem encK_conjT (h32 : n < 32) {g gi x : Table} (hx : validT n x = true)
    (hgi : validT n gi = true) :
    encK n (conjT n g gi x) = mulK n (mulK n (encK n g) (encK n x)) (encK n gi) := by
  unfold conjT
  rw [encK_compT h32 hgi, encK_compT h32 hx]

theorem validT_conjT {g gi x : Table} (hg : validT n g = true) (hx : validT n x = true)
    (hgi : validT n gi = true) : validT n (conjT n g gi x) = true :=
  validT_compT (validT_compT hg hx) hgi

theorem map_eq_compT (L T : Table) (hT : T.size = n) :
    T.map (fun t => L[t.toNat]!) = compT n L T := by
  apply Array.ext (by simp [compT, hT])
  intro i h1 h2
  have hi : i < T.size := by simpa using h1
  simp only [Array.getElem_map, compT, Array.getElem_ofFn]
  rw [getElem!_pos T i hi]

theorem wK_eq {D : Data} (hn : D.n < 32) (hg : ∀ l, validT D.n (D.gens l) = true)
    (w : List Int) : encK D.n (wT D w) = wK D w ∧ validT D.n (wT D w) = true := by
  induction w with
  | nil => exact ⟨rfl, validT_idT (by omega)⟩
  | cons l w ih =>
    obtain ⟨e, hv⟩ := ih
    have hw : wT D (l :: w) = compT D.n (D.gens l) (wT D w) := by
      change (wordT D.n D.gens w).map (fun t => (D.gens l)[t.toNat]!) = _
      exact map_eq_compT _ _ (wordT_size _ _ _)
    rw [hw]
    refine ⟨?_, validT_compT (hg l) hv⟩
    rw [encK_compT hn hv, e]
    rfl

theorem eltK_eq (h32 : n < 32) : ∀ (L : List Table), (∀ x ∈ L, validT n x = true) → ∀ m,
    encK n (eltT n L m) = eltK n (encK n (idT n)) (L.map (encK n)) m ∧
      validT n (eltT n L m) = true
  | [], _, _ => ⟨rfl, validT_idT (by omega)⟩
  | s :: ss, hL, m => by
    obtain ⟨e, hv⟩ := eltK_eq h32 ss (fun x hx => hL x (List.mem_cons_of_mem _ hx)) (m / 2)
    have hs := hL s List.mem_cons_self
    have hif : validT n (if m % 2 = 1 then s else idT n) = true := by
      split_ifs
      · exact hs
      · exact validT_idT (by omega)
    refine ⟨?_, validT_compT hif hv⟩
    change encK n (compT n (if m % 2 = 1 then s else idT n) (eltT n ss (m / 2))) =
      mulK n (if m % 2 = 1 then encK n s else encK n (idT n))
        (eltK n (encK n (idT n)) (ss.map (encK n)) (m / 2))
    rw [encK_compT h32 hv, e, apply_ite (encK n)]

theorem exists_rep {y : Table} (hv : validT n y = true)
    (hi : ∀ i < n, ∀ j < n, ap y i = ap y j → i = j) :
    ∃ g : Equiv.Perm (Fin n), Rep n y g := by
  have hlt := (validT_iff.1 hv).2
  let f : Fin n → Fin n := fun i => ⟨ap y i, hlt i i.2⟩
  have hf : Function.Injective f := fun a b h => by
    have h' : (⟨ap y a, hlt a a.2⟩ : Fin n) = ⟨ap y b, hlt b b.2⟩ := h
    exact Fin.ext (hi a a.2 b b.2 (Fin.mk.inj_iff.1 h'))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun i hi' => ?_⟩
  rw [idx_of_lt _ hi']
  rfl

theorem invT_facts (h32 : n < 32) {y : Table} (hv : validT n y = true)
    (hi : ∀ i < n, ∀ j < n, ap y i = ap y j → i = j) :
    invOK n y (invT n y) = true ∧ validT n (invT n y) = true ∧
      encK n (invT n y) = invW n 5 (encK n y) := by
  obtain ⟨g, hg⟩ := exists_rep hv hi
  have hn : n < 2 ^ 32 := by omega
  have hR := Tbl.invT_rep hn hg
  have hvi : validT n (invT n y) = true := by
    rw [validT_iff]
    refine ⟨Tbl.invT_size n y, fun i hi' => ?_⟩
    rw [hR i hi']
    exact idx_lt _ hi'
  refine ⟨Tbl.invOK_invT hn hg, hvi, ?_⟩
  apply eq_of_imgW (w := 5) (by norm_num)
  intro k
  rw [invW_eq]
  have hlt := (validT_iff.1 hv).2
  have hp : ∀ i < n, ∀ j < n, imgW 5 (encK n y) i = imgW 5 (encK n y) j → i = j := by
    intro i hi' j hj e
    rw [imgW_encK_lt hi', imgW_encK_lt hj, Nat.mod_eq_of_lt (by have := hlt i hi'; omega),
      Nat.mod_eq_of_lt (by have := hlt j hj; omega)] at e
    exact hi i hi' j hj e
  by_cases hk : k < n
  · have hik := idx_lt g⁻¹ hk
    have hpk : imgW 5 (encK n y) (idx n g⁻¹ k) = k := by
      rw [imgW_encK_lt hik, hg _ hik, idx_idx_inv, Nat.mod_eq_of_lt (by omega)]
    rw [imgW_orW_of (fun i hi' => by change i < 2 ^ 5; omega) hp hik hpk, imgW_encK_lt hk,
      hR k hk, Nat.mod_eq_of_lt (by omega)]
  · rw [imgW_encK_ge hk, imgW_orW_none (fun i hi' => by change i < 2 ^ 5; omega)]
    intro i hi' e
    rw [imgW_encK_lt hi', Nat.mod_eq_of_lt (by have := hlt i hi'; omega)] at e
    exact hk (e ▸ hlt i hi')

theorem injK_spec (h32 : n < 32) {y : Table} (hv : validT n y = true) (h : injK n (encK n y) = true) :
    ∀ i < n, ∀ j < n, ap y i = ap y j → i = j := by
  intro i hi j hj e
  have hlt := (validT_iff.1 hv).2
  unfold injK at h
  rw [List.all_eq_true] at h
  have h' := List.all_eq_true.1 (h i (List.mem_range.2 hi)) j (List.mem_range.2 hj)
  rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h'
  rcases h' with h' | h'
  · exact h'
  · rw [imgW_encK_lt hi, imgW_encK_lt hj, e, Nat.beq_refl] at h'
    cases h'

@[expose] noncomputable def inP (n x : Nat) (acc : List Nat × List Nat) (s : Nat) :
    List Nat × List Nat :=
  if memK acc.1 (mulK n x s) = true then acc else (mulK n x s :: acc.1, mulK n x s :: acc.2)

@[expose] def inT (n : Nat) (x : Table) (acc : List Table × List Table) (s : Table) :
    List Table × List Table :=
  let y := compT n x s
  if memL acc.1 y then acc else (y :: acc.1, y :: acc.2)

theorem stepX_eq {α : Type} (x : Nat) : ∀ (gs E F : List Nat) (k : List Nat → List Nat → α),
    stepX n x gs E F k = k (gs.foldl (inP n x) (E, F)).1 (gs.foldl (inP n x) (E, F)).2
  | [], E, F, k => rfl
  | s :: gs, E, F, k => by
    have e : stepX n x (s :: gs) E F k = strictK (mulK n x s) fun y =>
        bIfK (memK E y) (stepX n x gs E F k) (stepX n x gs (y :: E) (y :: F) k) := rfl
    rw [e, strictK_eq, bIfK_eq, List.foldl_cons]
    unfold inP
    cases memK E (mulK n x s)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact stepX_eq x gs _ _ k
    · simp only [↓reduceIte]
      exact stepX_eq x gs E F k

theorem stepFr_eq {α : Type} (gs : List Nat) : ∀ (fr E F : List Nat) (k : List Nat → List Nat → α),
    stepFr n gs fr E F k =
      k (fr.foldl (fun acc x => gs.foldl (inP n x) acc) (E, F)).1
        (fr.foldl (fun acc x => gs.foldl (inP n x) acc) (E, F)).2
  | [], E, F, k => rfl
  | x :: fr, E, F, k => by
    have e : stepFr n gs (x :: fr) E F k = stepX n x gs E F fun E F => stepFr n gs fr E F k := rfl
    rw [e, stepX_eq, stepFr_eq gs fr, List.foldl_cons]

abbrev AllV (n : Nat) (L : List Table) : Prop := ∀ x ∈ L, validT n x = true

theorem allV_cons {y : Table} {L : List Table} (hy : validT n y = true) (hL : AllV n L) :
    AllV n (y :: L) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hy
  · exact hL x hx

theorem inner_sim (h32 : n < 32) {x : Table} (hx : validT n x = true) :
    ∀ (gs : List Table), AllV n gs → ∀ (acc : List Table × List Table), AllV n acc.1 → AllV n acc.2 →
      (gs.map (encK n)).foldl (inP n (encK n x)) (acc.1.map (encK n), acc.2.map (encK n)) =
        ((gs.foldl (inT n x) acc).1.map (encK n), (gs.foldl (inT n x) acc).2.map (encK n)) ∧
      AllV n (gs.foldl (inT n x) acc).1 ∧ AllV n (gs.foldl (inT n x) acc).2
  | [], _, acc, h1, h2 => ⟨rfl, h1, h2⟩
  | s :: gs, hgs, acc, h1, h2 => by
    have hs := hgs s List.mem_cons_self
    have hgs' : AllV n gs := fun t ht => hgs t (List.mem_cons_of_mem _ ht)
    have hy := validT_compT hx hs
    have hm := memL_encK h32 h1 hy
    rw [encK_compT h32 hs] at hm
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have ei : inP n (encK n x) (acc.1.map (encK n), acc.2.map (encK n)) (encK n s) =
        ((inT n x acc s).1.map (encK n), (inT n x acc s).2.map (encK n)) := by
      unfold inP inT
      simp only
      rw [← hm]
      cases memL acc.1 (compT n x s)
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, encK_compT h32 hs]
      · simp only [↓reduceIte]
    have hv : AllV n (inT n x acc s).1 ∧ AllV n (inT n x acc s).2 := by
      unfold inT
      simp only
      cases memL acc.1 (compT n x s)
      · exact ⟨allV_cons hy h1, allV_cons hy h2⟩
      · exact ⟨h1, h2⟩
    rw [ei]
    exact inner_sim h32 hx gs hgs' _ hv.1 hv.2

theorem outer_sim (h32 : n < 32) {gs : List Table} (hgs : AllV n gs) :
    ∀ (fr : List Table), AllV n fr → ∀ (acc : List Table × List Table), AllV n acc.1 → AllV n acc.2 →
      (fr.map (encK n)).foldl (fun acc x => (gs.map (encK n)).foldl (inP n x) acc)
          (acc.1.map (encK n), acc.2.map (encK n)) =
        ((fr.foldl (fun acc x => gs.foldl (inT n x) acc) acc).1.map (encK n),
          (fr.foldl (fun acc x => gs.foldl (inT n x) acc) acc).2.map (encK n)) ∧
      AllV n (fr.foldl (fun acc x => gs.foldl (inT n x) acc) acc).1 ∧
      AllV n (fr.foldl (fun acc x => gs.foldl (inT n x) acc) acc).2
  | [], _, acc, h1, h2 => ⟨rfl, h1, h2⟩
  | x :: fr, hfr, acc, h1, h2 => by
    have hx := hfr x List.mem_cons_self
    have hfr' : AllV n fr := fun t ht => hfr t (List.mem_cons_of_mem _ ht)
    obtain ⟨e, v1, v2⟩ := inner_sim h32 hx gs hgs acc h1 h2
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e]
    exact outer_sim h32 hgs fr hfr' _ v1 v2

theorem closeRound_eq (n : Nat) (gs E fr : List Table) :
    closeRound n gs E fr = fr.foldl (fun acc x => gs.foldl (inT n x) acc) (E, []) := rfl

theorem closeK_eq (h32 : n < 32) {gs : List Table} (hgs : AllV n gs) :
    ∀ (fuel : Nat) (E fr : List Table), AllV n E → AllV n fr →
      closeK n (gs.map (encK n)) fuel (E.map (encK n)) (fr.map (encK n)) =
        (closeT n gs fuel E fr).map (encK n) ∧ AllV n (closeT n gs fuel E fr)
  | 0, E, _, hE, _ => ⟨rfl, hE⟩
  | fuel + 1, E, fr, hE, hfr => by
    have e : closeK n (gs.map (encK n)) (fuel + 1) (E.map (encK n)) (fr.map (encK n)) =
        stepFr n (gs.map (encK n)) (fr.map (encK n)) (E.map (encK n)) [] fun E F =>
          List.rec (motive := fun _ => List Nat) E (fun _ _ _ => closeK n (gs.map (encK n)) fuel E F)
            F := rfl
    obtain ⟨er, v1, v2⟩ := outer_sim h32 hgs fr hfr (E, []) hE (fun _ h => absurd h List.not_mem_nil)
    have e2 : closeT n gs (fuel + 1) E fr =
        if (closeRound n gs E fr).2.isEmpty then (closeRound n gs E fr).1
        else closeT n gs fuel (closeRound n gs E fr).1 (closeRound n gs E fr).2 := rfl
    rw [e, stepFr_eq, e2, closeRound_eq]
    simp only [List.map_nil] at er
    rw [er]
    generalize hR : fr.foldl (fun acc x => gs.foldl (inT n x) acc) (E, []) = R at v1 v2
    rcases R with ⟨R1, R2⟩
    cases R2 with
    | nil => exact ⟨rfl, v1⟩
    | cons y R2 =>
      exact closeK_eq h32 hgs fuel R1 (y :: R2) v1 v2

theorem properOK_of_K {D : Data} {fuel : Nat} {J : List Bool} {c out : List Int}
    (h : properK D fuel J c out = true) : properOK D fuel J c out = true := by
  unfold properK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h32, hgs⟩, hout⟩, hid⟩, hcl⟩, hno⟩ := h
  have hn : D.n < 2 ^ 32 := by omega
  have hgs' : AllV D.n (tabU D J ++ tabUc D J c) := fun x hx => List.all_eq_true.1 hgs x hx
  have hI : AllV D.n [idT D.n] := fun x hx => by
    rw [List.mem_singleton.1 hx]
    exact validT_idT hn
  obtain ⟨eK, hv⟩ := closeK_eq h32 hgs' fuel [idT D.n] [idT D.n] hI hI
  simp only [List.map_cons, List.map_nil] at eK
  rw [eK] at hid hcl hno
  unfold properOK
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  generalize closeT D.n (tabU D J ++ tabUc D J c) fuel [idT D.n] [idT D.n] = E at hv hid hcl hno
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [memL_encK h32 hv (validT_idT hn)]
    exact hid
  · rw [List.all_eq_true]
    intro x hx
    have hxv := hv x hx
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨(validT_iff.1 hxv).1, List.all_eq_true.2 fun s hs => ?_⟩
    have hsv := hgs' s hs
    rw [memL_encK h32 hv (validT_compT hxv hsv), encK_compT h32 hsv]
    have h1 := List.all_eq_true.1 hcl (encK D.n x) (List.mem_map_of_mem hx)
    exact List.all_eq_true.1 h1 (encK D.n s) (List.mem_map_of_mem hs)
  · rw [memL_encK h32 hv hout]
    exact hno

theorem all_congr' {α : Type} {L : List α} {p q : α → Bool} (h : ∀ a ∈ L, p a = q a) :
    L.all p = L.all q := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem any_congr' {α : Type} {L : List α} {p q : α → Bool} (h : ∀ a ∈ L, p a = q a) :
    L.any p = L.any q := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem all_map_congr {α β : Type} {L : List α} {f : α → β} {p : α → Bool} {q : β → Bool}
    (h : ∀ a ∈ L, p a = q (f a)) : L.all p = (L.map f).all q := by
  rw [List.all_map]
  exact all_congr' h

theorem any_map_congr {α β : Type} {L : List α} {f : α → β} {p : α → Bool} {q : β → Bool}
    (h : ∀ a ∈ L, p a = q (f a)) : L.any p = (L.map f).any q := by
  rw [List.any_map]
  exact any_congr' h

theorem zip_map_self {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ L : List α, (L.map f).zip (L.map g) = L.map fun a => (f a, g a)
  | [] => rfl
  | a :: L => by rw [List.map_cons, List.map_cons, List.zip_cons_cons, zip_map_self f g L,
      List.map_cons]

section Base

variable {D : Data} (h32 : D.n < 32) (hg : ∀ l, validT D.n (D.gens l) = true)
include h32 hg

theorem wT_valid (w : List Int) : validT D.n (wT D w) = true := (wK_eq h32 hg w).2

theorem encK_wT (w : List Int) : encK D.n (wT D w) = wK D w := (wK_eq h32 hg w).1

theorem pcT_valid : AllV D.n (pcT D) := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact wT_valid h32 hg w

theorem pcT_codes : (pcT D).map (encK D.n) = D.pc.map (wK D) := by
  unfold pcT
  rw [List.map_map]
  exact List.map_congr_left fun w _ => encK_wT h32 hg w

theorem el_valid (i : Nat) : validT D.n (el D i) = true :=
  (eltK_eq h32 (pcT D) (pcT_valid h32 hg) i).2

theorem encK_el (i : Nat) :
    encK D.n (el D i) = eltK D.n (encK D.n (idT D.n)) (D.pc.map (wK D)) i := by
  rw [← pcT_codes h32 hg]
  exact (eltK_eq h32 (pcT D) (pcT_valid h32 hg) i).1

theorem elts_valid : AllV D.n (elts D) := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact el_valid h32 hg i

theorem elts_codes : (elts D).map (encK D.n) =
    (List.range (2 ^ D.pc.length)).map (eltK D.n (encK D.n (idT D.n)) (D.pc.map (wK D))) := by
  unfold elts
  rw [List.map_map]
  exact List.map_congr_left fun i _ => encK_el h32 hg i

theorem eltK_fn : eltK D.n (encK D.n (idT D.n)) (D.pc.map (wK D)) = fun i => encK D.n (el D i) :=
  funext fun i => (encK_el h32 hg i).symm

theorem baseCheck_of_K
    (h : baseK D (encK D.n (idT D.n)) (D.pc.map (wK D)) (D.pc.map fun w => wK D (invWord w))
      ((List.range (2 ^ D.pc.length)).map (eltK D.n (encK D.n (idT D.n)) (D.pc.map (wK D))))
      (((List.range (2 ^ D.pc.length)).map
        (eltK D.n (encK D.n (idT D.n)) (D.pc.map (wK D)))).map (invW D.n 5))
      (D.cw.map (wK D)) (D.cw.map fun w => wK D (invWord w))
      ((D.cls.flatMap fun c => c.map Prod.fst).map
        (eltK D.n (encK D.n (idT D.n)) (D.pc.map (wK D))))
      (eltK D.n (encK D.n (idT D.n)) (D.pc.map (wK D)) D.zIdx) = true) :
    baseCheck D = true := by
  rw [← elts_codes h32 hg, eltK_fn h32 hg] at h
  have hSv := elts_valid h32 hg
  have hpv := pcT_valid h32 hg
  have hI : validT D.n (idT D.n) = true := validT_idT (by omega)
  have hz := el_valid h32 hg D.zIdx
  unfold baseK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  have hinj : ∀ x ∈ elts D, ∀ i < D.n, ∀ j < D.n, ap x i = ap x j → i = j := fun x hx =>
    injK_spec h32 (hSv x hx) (List.all_eq_true.1 h4 _ (List.mem_map_of_mem hx))
  have hpc : ∀ s ∈ pcT D, encK D.n s ∈ D.pc.map (wK D) := fun s hs => by
    rw [← pcT_codes h32 hg]
    exact List.mem_map_of_mem hs
  have hcz : ∀ x, validT D.n x = true → (pcT D).all (fun s => commT D.n x s) =
      (D.pc.map (wK D)).all (fun s => commK D.n (encK D.n x) s) := fun x hx => by
    rw [← pcT_codes h32 hg]
    exact all_map_congr fun s hs => commT_encK h32 hx (hpv s hs)
  unfold baseCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, h5⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, h12⟩, h13⟩, ?_⟩
  · exact decide_eq_true ((of_decide_eq_true h1).of_map _)
  · refine List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun s hs => ?_
    rw [memL_encK h32 hSv (validT_compT (hSv x hx) (hpv s hs)), encK_compT h32 (hpv s hs)]
    exact List.all_eq_true.1 (List.all_eq_true.1 h2 _ (List.mem_map_of_mem hx)) _ (hpc s hs)
  · refine List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun w hw => ?_
    have hwv := wT_valid h32 hg (invWord w)
    rw [memL_encK h32 hSv (validT_compT (hSv x hx) hwv), encK_compT h32 hwv, encK_wT h32 hg]
    exact List.all_eq_true.1 (List.all_eq_true.1 h3 _ (List.mem_map_of_mem hx)) _
      (List.mem_map_of_mem (f := fun w => wK D (invWord w)) hw)
  · exact List.all_eq_true.2 fun x hx => (invT_facts h32 (hSv x hx) (hinj x hx)).1
  · rw [beq_encK h32 hz hI]
    exact h6
  · rw [beq_encK h32 (validT_compT hz hz) hI, encK_compT h32 hz]
    exact h7
  · refine List.all_eq_true.2 fun s hs => ?_
    rw [commT_encK h32 hz (hpv s hs)]
    exact List.all_eq_true.1 h8 _ (hpc s hs)
  · refine List.all_eq_true.2 fun x hx => ?_
    have hx' := List.all_eq_true.1 h9 _ (List.mem_map_of_mem hx)
    rw [hcz x (hSv x hx), beq_encK h32 (hSv x hx) hI, beq_encK h32 (hSv x hx) hz]
    exact hx'
  · refine List.all_eq_true.2 fun w hw => ?_
    rw [commT_encK h32 (wT_valid h32 hg w) hz, encK_wT h32 hg]
    exact List.all_eq_true.1 h10 _ (List.mem_map_of_mem hw)
  · refine List.all_eq_true.2 fun x hx => ?_
    have hxv := hSv x hx
    have hx' := List.all_eq_true.1 h11 _ (List.mem_map_of_mem hx)
    have e3 : (D.cls.any fun c => c.any fun p => el D p.1 == x) =
        ((D.cls.flatMap fun c => c.map Prod.fst).map fun i => encK D.n (el D i)).any
          (fun y => Nat.beq y (encK D.n x)) := by
      rw [List.any_map, List.any_flatMap]
      refine any_congr' fun c _ => ?_
      rw [List.any_map]
      refine any_congr' fun p _ => ?_
      exact beq_encK h32 (el_valid h32 hg _) hxv
    have e4 : (elts D).any (fun y => !commT D.n x (conjT D.n y (invT D.n y) x)) =
        (((elts D).map (encK D.n)).zip (((elts D).map (encK D.n)).map (invW D.n 5))).any
          (fun y => !commK D.n (encK D.n x) (mulK D.n (mulK D.n y.1 (encK D.n x)) y.2)) := by
      rw [List.map_map, zip_map_self]
      refine any_map_congr fun y hy => ?_
      obtain ⟨-, hiv, hie⟩ := invT_facts h32 (hSv y hy) (hinj y hy)
      rw [commT_encK h32 hxv (validT_conjT (hSv y hy) hxv hiv), encK_conjT h32 hxv hiv, hie]
      rfl
    have e5 : (cwT D).any (fun g => !memL (elts D) (conjT D.n g.1 g.2 x) ||
          !commT D.n x (conjT D.n g.1 g.2 x)) =
        ((D.cw.map (wK D)).zip (D.cw.map fun w => wK D (invWord w))).any (fun g =>
          !memK ((elts D).map (encK D.n)) (mulK D.n (mulK D.n g.1 (encK D.n x)) g.2) ||
            !commK D.n (encK D.n x) (mulK D.n (mulK D.n g.1 (encK D.n x)) g.2)) := by
      unfold cwT
      rw [zip_map_self, List.any_map, List.any_map]
      refine any_congr' fun w _ => ?_
      have hw := wT_valid h32 hg w
      have hwi := wT_valid h32 hg (invWord w)
      simp only [Function.comp_apply]
      rw [memL_encK h32 hSv (validT_conjT hw hxv hwi), commT_encK h32 hxv (validT_conjT hw hxv hwi),
        encK_conjT h32 hxv hwi, encK_wT h32 hg, encK_wT h32 hg]
    simp only [excl]
    rw [beq_encK h32 hxv hI, beq_encK h32 hxv hz, e3, beq_encK h32 (validT_compT hxv hxv) hI,
      encK_compT h32 hxv, e4, e5]
    exact hx'
  · refine all_congr' (fun c _ => ?_) |>.trans h14
    rcases c with _ | ⟨⟨i₀, w₀⟩, c'⟩
    · rfl
    · refine all_congr' fun p _ => ?_
      have hw := wT_valid h32 hg p.2
      have hwi := wT_valid h32 hg (invWord p.2)
      rw [commT_encK h32 hw hz, beq_encK h32 (validT_conjT hw (el_valid h32 hg i₀) hwi)
        (el_valid h32 hg p.1), encK_conjT h32 (el_valid h32 hg i₀) hwi, encK_wT h32 hg,
        encK_wT h32 hg, encK_el h32 hg i₀, encK_el h32 hg p.1]

theorem memU_eq (J : List Bool) {t : Table} (ht : validT D.n t = true) :
    memU D J t = memUK D (encK D.n (idT D.n)) (D.pc.map (wK D)) J (encK D.n t) := by
  unfold memU memUK
  rw [eltK_fn h32 hg, beq_encK h32 ht (validT_idT (by omega))]
  congr 1
  exact any_congr' fun i _ => beq_encK h32 (el_valid h32 hg i) ht

theorem tabU_valid (J : List Bool) : AllV D.n (tabU D J) := by
  intro x hx
  unfold tabU at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact validT_idT (by omega)
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact el_valid h32 hg i

theorem tabU_codes (J : List Bool) : (tabU D J).map (encK D.n) =
    encK D.n (idT D.n) :: (idxU D J).map (fun i => encK D.n (el D i)) := by
  unfold tabU
  rw [List.map_cons, List.map_map]
  rfl

end Base

theorem pverdictOK_of_K {P : PData} (h32 : P.D.n < 32)
    (hg : ∀ l, validT P.D.n (P.D.gens l) = true) {J : List Bool} {v : PVerdict}
    (h : pverdictK P (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) J v = true) :
    pverdictOK P J v = true := by
  have hI : validT P.D.n (idT P.D.n) = true := validT_idT (by omega)
  cases v with
  | size => exact h
  | notClosed i j =>
    unfold pverdictK at h
    simp only [pverdictOK, verdictOK]
    rw [memU_eq h32 hg J (validT_compT (el_valid h32 hg i) (el_valid h32 hg j)),
      encK_compT h32 (el_valid h32 hg j), encK_el h32 hg, encK_el h32 hg]
    exact h
  | bad t y g =>
    unfold pverdictK at h
    simp only [pverdictOK]
    have hgv := wT_valid h32 hg g
    have hgi := wT_valid h32 hg (invWord g)
    have hyv := el_valid h32 hg y
    have e1 : (tabU P.D J).all (fun u => commT P.D.n
        (LargeExtraspecial.S11.PairCheck.conjW P.D g u) (el P.D t)) =
        ((encK P.D.n (idT P.D.n)) :: (idxU P.D J).map
          (eltK P.D.n (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)))).all (fun u =>
            commK P.D.n (mulK P.D.n (mulK P.D.n (wK P.D g) u) (wK P.D (invWord g)))
              (eltK P.D.n (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) t)) := by
      rw [eltK_fn h32 hg, ← tabU_codes h32 hg]
      refine all_map_congr fun u hu => ?_
      have huv := tabU_valid h32 hg J u hu
      unfold LargeExtraspecial.S11.PairCheck.conjW
      rw [commT_encK h32 (validT_conjT hgv huv hgi) (el_valid h32 hg t), encK_conjT h32 huv hgi,
        encK_wT h32 hg, encK_wT h32 hg]
    simp only at h
    rw [e1, beq_encK h32 (el_valid h32 hg t) hI, encK_el h32 hg t,
      memU_eq h32 hg J (t := LargeExtraspecial.S11.PairCheck.conjW P.D g (el P.D y))
        (validT_conjT hgv hyv hgi)]
    unfold LargeExtraspecial.S11.PairCheck.conjW
    rw [encK_conjT h32 hyv hgi, encK_wT h32 hg, encK_wT h32 hg, encK_el h32 hg y]
    exact h
  | good c nIdx out =>
    unfold pverdictK at h
    simp only [strictK_eq, forceL_eq] at h
    simp only [pverdictOK]
    have hcv := wT_valid h32 hg c
    have hci := wT_valid h32 hg (invWord c)
    have hUv : AllV P.D.n (tabUc P.D J c) := fun x hx => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
      exact validT_conjT hcv (tabU_valid h32 hg J u hu) hci
    have hUc : (tabUc P.D J c).map (encK P.D.n) =
        ((encK P.D.n (idT P.D.n)) :: (idxU P.D J).map
          (eltK P.D.n (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)))).map fun u =>
            mulK P.D.n (mulK P.D.n (wK P.D c) u) (wK P.D (invWord c)) := by
      rw [eltK_fn h32 hg, ← tabU_codes h32 hg]
      unfold tabUc
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun u hu => ?_
      unfold LargeExtraspecial.S11.PairCheck.conjW
      simp only [Function.comp_apply]
      rw [encK_conjT h32 (tabU_valid h32 hg J u hu) hci, encK_wT h32 hg, encK_wT h32 hg]
    have hn : ∀ i, normU P.D J c (el P.D i) =
        (((encK P.D.n (idT P.D.n)) :: (idxU P.D J).map
          (eltK P.D.n (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)))).map fun u =>
            mulK P.D.n (mulK P.D.n (wK P.D c) u) (wK P.D (invWord c))).all fun t =>
          memK (((encK P.D.n (idT P.D.n)) :: (idxU P.D J).map
            (eltK P.D.n (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)))).map fun u =>
              mulK P.D.n (mulK P.D.n (wK P.D c) u) (wK P.D (invWord c)))
            (mulK P.D.n (mulK P.D.n (eltK P.D.n (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) i)
              t) (eltK P.D.n (encK P.D.n (idT P.D.n)) (P.D.pc.map (wK P.D)) i)) := by
      intro i
      have hiv := el_valid h32 hg i
      unfold normU
      rw [← hUc]
      refine all_map_congr fun t ht => ?_
      rw [memL_encK h32 hUv (validT_conjT hiv (hUv t ht) hiv), encK_conjT h32 (hUv t ht) hiv,
        encK_el h32 hg i]
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ?_⟩, ?_⟩
    · refine (all_congr' fun i _ => ?_).trans h5
      rw [hn i]
    · rcases h6 with h6 | h6
      · exact Or.inl h6
      · exact Or.inr (properOK_of_K h6)

theorem pairCheck_of_K {P : PData} (hg : ∀ l, validT P.D.n (P.D.gens l) = true)
    (h : pairCheckK P = true) : pairCheck P = true := by
  unfold pairCheckK at h
  simp only [strictK_eq, forceL_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h32, hord⟩, hb, hv⟩ := h
  unfold pairCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by omega, hord⟩, baseCheck_of_K h32 hg hb⟩, ?_⟩
  rw [List.all_eq_true] at hv ⊢
  intro J hJ
  obtain ⟨p, hp, hpv⟩ := List.any_eq_true.1 (hv J hJ)
  rw [Bool.and_eq_true] at hpv
  exact List.any_eq_true.2 ⟨p, hp, by rw [Bool.and_eq_true]; exact ⟨hpv.1, pverdictOK_of_K h32 hg hpv.2⟩⟩

theorem gens_valid {D : Data} {L : List Table} (hmem : ∀ l, D.gens l ∈ L)
    (hL : L.all (validT D.n) = true) : ∀ l, validT D.n (D.gens l) = true := fun l =>
  List.all_eq_true.1 hL _ (hmem l)

end CFSG.KC.S97RYK

end
