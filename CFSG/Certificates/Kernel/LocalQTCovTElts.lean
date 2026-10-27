module

public import CFSG.Certificates.Kernel.LocalQTCovTParse
public import CFSG.Certificates.Kernel.LocalQTCovTPrim
public import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.LocalQTCovEqns
import CFSG.Certificates.Kernel.LocalQTCovPerm
import CFSG.Certificates.Kernel.MonsterB.Co2MatSound
import CFSG.Certificates.Kernel.LocalQTBaseWProved
import CFSG.Certificates.Kernel.LocalQTTab2KSound

public section

namespace CFSG.KC.LQT.Cov.T

open CFSG.KC.LQT.Cov CFSG.KC.LQT.Cov.Parse CFSG.KC.LQT.Cov.Perm CFSG.KC.Ord CFSG.KC.LQT.Syl CFSG.KC.Enum CFSG.KS
open CFSG.QuasithinUnique.Ch1.TitsCover CFSG.Sporadic.Schreier.Tits
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.Monster.B.Co2.Native

variable {S SI : Nat → Nat}

theorem titsDerivedArrs_size : titsDerivedArrs.size = 13 := by
  unfold titsDerivedArrs titsField1755
  exact Array.size_ofFn

private noncomputable def packedArrs (S : Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := 13) fun j : Fin 13 => CFSG.KS.Raw.unpack 1755 11 (S j)

private theorem packedArrs_size : (packedArrs S).size = 13 := by
  unfold packedArrs
  exact Array.size_ofFn

private theorem packedArrs_get {j : Nat} (hj : j < 13) :
    (packedArrs S)[j]! = CFSG.KS.Raw.unpack 1755 11 (S j) := by
  rw [packedArrs, CFSG.Sporadic.Schreier.Tits.getElem!_ofFn_of_lt]
  simpa using hj

private theorem titsDerivedArrs_eq (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j)) :
    titsDerivedArrs = packedArrs S := by
  apply Array.ext
  · rw [titsDerivedArrs_size, packedArrs_size]
  · intro i h1 h2
    rw [← getElem!_pos titsDerivedArrs i h1, ← getElem!_pos (packedArrs S) i h2,
      hS i (by rwa [titsDerivedArrs_size] at h1), packedArrs_get (by simpa [packedArrs] using h2)]

theorem wordArr_eq_unpack {S SI : Nat → Nat}
    (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j))
    (hperm : ∀ j < 13, CFSG.KC.Enum.permOK 1755 11 (mask 11) (1755 * 11) (S j) (SI j) = true)
    (hsz : CFSG.KS.Raw.szOK 1755 11 = true) {wd : List Int} (hl : CFSG.KS.Raw.lettersK 13 wd = true) :
    CFSG.Sporadic.Schreier.Tits.wordArr 1755 titsDerivedArrs wd =
      CFSG.KS.Raw.unpack 1755 11 (CFSG.KS.Raw.wordK 1755 11 (mask 11) (CFSG.KC.Enum.pidn 1755 11) S SI wd) := by
  have ht : titsDerivedArrs = packedArrs S := titsDerivedArrs_eq hS
  rw [ht]
  change wordA 1755 (packedArrs S) (CFSG.Certificates.Native.rawInvs 1755 (packedArrs S)) wd = _
  have hbase : (packedArrs S).size = 13 ∧
      ∀ j < 13, (packedArrs S)[j]! = CFSG.KS.Raw.unpack 1755 11 (S j) :=
    ⟨packedArrs_size, fun j hj => packedArrs_get hj⟩
  have hp : allN 13 (fun j => CFSG.KC.Enum.permOK 1755 11 (mask 11) (1755 * 11) (S j) (SI j)) = true :=
    CFSG.KS.Raw.Orb.allN_iff.2 hperm
  have hw : wordEqK 1755 11 (mask 11) (CFSG.KC.Enum.pidn 1755 11) S SI 13 wd
      (CFSG.KS.Raw.wordK 1755 11 (mask 11) (CFSG.KC.Enum.pidn 1755 11) S SI wd) = true := by
    rw [wordEqK]
    simp only [bAnd_iff, hsz, hl, true_and]
    exact Nat.beq_refl _
  exact (wordEqK_sound hbase hp hw).1

theorem wordK_range {S SI : Nat → Nat}
    (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j))
    (hperm : ∀ j < 13, CFSG.KC.Enum.permOK 1755 11 (mask 11) (1755 * 11) (S j) (SI j) = true)
    (hsz : CFSG.KS.Raw.szOK 1755 11 = true) {wd : List Int} (hl : CFSG.KS.Raw.lettersK 13 wd = true) :
    ∀ i < 1755, CFSG.KC.Enum.pg 11 (mask 11) (CFSG.KS.Raw.wordK 1755 11 (mask 11) (CFSG.KC.Enum.pidn 1755 11) S SI wd) i < 1755 := by
  obtain ⟨hn, hwpos⟩ := CFSG.KS.Raw.Orb.szOK_facts hsz
  induction wd with
  | nil =>
    intro i hi
    have e : CFSG.KS.Raw.wordK 1755 11 (mask 11) (CFSG.KC.Enum.pidn 1755 11) S SI [] = CFSG.KC.Enum.pidn 1755 11 := rfl
    rw [e, CFSG.KS.PF.pg_pidn hn hwpos hi]
    exact hi
  | cons z wd ih =>
    rw [CFSG.KS.Raw.Orb.lettersK_cons] at hl
    rw [Bool.and_eq_true] at hl
    obtain ⟨h1, h3⟩ := hl
    rw [Bool.and_eq_true] at h1
    obtain ⟨h1a, h1b⟩ := h1
    have h1' : Nat.blt (nat_lit 0) (CFSG.KS.Mathieu.icode z) = true := by simpa [Nat.blt_eq] using h1a
    have h2' : Nat.ble (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) 13 = true := by
      rw [Nat.ble_eq]
      simpa [Nat.shiftRight_eq_div_pow, Nat.pow_one] using h1b
    obtain ⟨-, hlet⟩ := letter_sound (n := 1755) (w := 11) (kS := 13)
      ⟨packedArrs_size, fun j hj => packedArrs_get hj⟩ hperm h1' h2'
    intro i hi
    rw [wordK_cons, CFSG.KS.PF.pg_pcomp (by norm_num) hi]
    simpa [letK] using hlet _ (ih h3 i hi)

private noncomputable def buildEGo (n w : Nat) (X : List Nat)
    (WR : List (List (List Nat))) (k : List Nat → Bool) :
    List Nat → Nat → List Nat → Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ acc => List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
      (fun x _ ih r => ih (List.cons x r)) acc [])
    (fun p _ ih c acc => strictB c fun c =>
      strictB (pcomp n w (mask w) (getK acc (Nat.sub (Nat.sub c 1) p) 0)
        (getK X (Nat.mod (lastK (getRG WR c [])) 2) 0)) fun e =>
      ih (Nat.succ c) (List.cons e acc))

private theorem buildE_eq_go (n w : Nat) (X : List Nat) (WR : List (List (List Nat)))
    (P : List Nat) (k : List Nat → Bool) :
    buildE n w X WR P k = buildEGo n w X WR k P 1 [pidn n w] := rfl

private theorem getK_rev_range {α : Type} (E : Nat → α) (d : α) {c p : Nat} (hp : p < c) :
    getK ((List.range c).reverse.map E) (c - 1 - p) d = E p := by
  rw [getK_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_reverse (by
      rw [List.length_range]
      exact Nat.lt_of_le_of_lt (Nat.sub_le (c - 1) p) (Nat.sub_lt (by omega) (by decide))),
    List.length_range,
    show c - 1 - (c - 1 - p) = p by omega, List.getElem?_range hp,
    Option.map_some, Option.getD_some]

private theorem buildEGo_rev_aux (acc r : List Nat) (k : List Nat → Bool) :
    List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
      (fun x _ ih r => ih (List.cons x r)) acc r = k (acc.reverse ++ r) := by
  induction acc generalizing r with
  | nil => rfl
  | cons x xs ih =>
    change List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
      (fun x _ ih r => ih (List.cons x r)) xs (x :: r) = _
    rw [ih, List.reverse_cons, List.append_assoc]
    rfl

private theorem buildE_go_spec_nil (n w : Nat) (X : List Nat) (WR : List (List (List Nat)))
    (P0 : List Nat) (k : List Nat → Bool) :
    ∀ (c : Nat) (acc : List Nat) (E : Nat → Nat),
      0 < c → ([] : List Nat) = P0.drop (c - 1) → acc = (List.range c).reverse.map E →
      (∀ v, 0 < v → v < c →
        E v = pcomp n w (mask w) (E (getK P0 (v - 1) 0))
          (getK X (Nat.mod (lastK (getRG WR v [])) 2) 0)) →
      (∀ v, 0 < v → v < c → getK P0 (v - 1) 0 < v) →
      ∃ E' : Nat → Nat,
        buildEGo n w X WR k [] c acc = k ((List.range c).map E') ∧
        (∀ v < c, E' v = E v) ∧
        (∀ v, 0 < v → v < c →
          E' v = pcomp n w (mask w) (E' (getK P0 (v - 1) 0))
            (getK X (Nat.mod (lastK (getRG WR v [])) 2) 0)) := by
  intro c acc E hc hsuf hacc hrec hpar
  refine ⟨E, ?_, fun v hv => rfl, ?_⟩
  · have e : buildEGo n w X WR k [] c acc = k acc.reverse := by
      change List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
        (fun x _ ih r => ih (x :: r)) acc [] = k acc.reverse
      simpa using buildEGo_rev_aux acc [] k
    rw [e, hacc, List.map_reverse, List.reverse_reverse]
  · intro v hv vlt
    exact hrec v hv (by simpa using vlt)

private theorem buildE_go_spec_p {P0 : List Nat} {acc : List Nat} {E : Nat → Nat}
    {p c : Nat} {P' : List Nat} (hc : 0 < c) (hsuf : p :: P' = P0.drop (c - 1))
    (hacc : acc = (List.range c).reverse.map E)
    (hpar : ∀ v, 0 < v → v < c + (p :: P').length → getK P0 (v - 1) 0 < v) :
    p = getK P0 (c - 1) 0 ∧ p < c ∧ getK acc (c.sub 1 - p) 0 = E p := by
  have hp_eq : p = getK P0 (c - 1) 0 := by
    have h0 : getK (P0.drop (c - 1)) 0 0 = p := by
      rw [← hsuf, getK_getD]
      rfl
    rw [← h0, getK_getD, getK_getD, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  have hpc : p < c := by
    rw [hp_eq]
    exact hpar c hc (by simp)
  refine ⟨hp_eq, hpc, ?_⟩
  rw [hacc]
  exact getK_rev_range E 0 hpc

private theorem buildE_go_spec_acc {P0 : List Nat} {n w c : Nat} {X : List Nat}
    {WR : List (List (List Nat))} {acc : List Nat} {E : Nat → Nat} {p : Nat} {P' : List Nat}
    (hc : 0 < c) (hsuf : p :: P' = P0.drop (c - 1))
    (hacc : acc = (List.range c).reverse.map E) :
    ∃ (E1 : Nat → Nat) (e : Nat),
      e = pcomp n w (mask w) (E p) (getK X (Nat.mod (lastK (getRG WR c [])) 2) 0) ∧
      P' = P0.drop c ∧
      e :: acc = (List.range (c + 1)).reverse.map E1 ∧
      E1 c = e ∧ (∀ v < c, E1 v = E v) := by
  let e := pcomp n w (mask w) (E p) (getK X (Nat.mod (lastK (getRG WR c [])) 2) 0)
  let E1 : Nat → Nat := fun v => if v = c then e else E v
  refine ⟨E1, e, rfl, ?_, ?_, by simp [E1], fun v hv => by simp [E1, show v ≠ c by omega]⟩
  · rw [show c = (c - 1) + 1 by omega, ← List.drop_drop (i := 1) (j := c - 1)]
    rw [← hsuf]
    rfl
  · rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.map_append,
      List.map_cons, List.map_nil, List.singleton_append, hacc]
    congr 1
    · simp [E1]
    · rw [List.map_congr_left]
      intro v hv
      rw [List.mem_reverse, List.mem_range] at hv
      simp [E1, show v ≠ c by omega]

private theorem buildE_go_spec_rec {P0 : List Nat} {n w c : Nat} {X : List Nat}
    {WR : List (List (List Nat))} {E E1 : Nat → Nat} {e p : Nat} {P' : List Nat}
    (he : e = pcomp n w (mask w) (E p) (getK X (Nat.mod (lastK (getRG WR c [])) 2) 0))
    (hp_eq : p = getK P0 (c - 1) 0) (hpc : p < c) (hE1c : E1 c = e)
    (hE1lt : ∀ v < c, E1 v = E v)
    (hrec : ∀ v, 0 < v → v < c →
      E v = pcomp n w (mask w) (E (getK P0 (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG WR v [])) 2) 0))
    (hpar : ∀ v, 0 < v → v < c + (p :: P').length → getK P0 (v - 1) 0 < v) :
    ∀ v, 0 < v → v < c + 1 →
      E1 v = pcomp n w (mask w) (E1 (getK P0 (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG WR v [])) 2) 0) := by
  intro v hv hvlt
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hvlt) with hlt | rfl
  · have hvne : v ≠ c := by omega
    rw [hE1lt v hlt, hrec v hv hlt]
    congr 1
    rw [hE1lt (getK P0 (v - 1) 0) (by
      have := hpar v hv (by omega)
      omega)]
  · rw [hE1c, ← hp_eq, hE1lt p hpc]
    exact he

private theorem buildE_go_spec_step {n w : Nat} {X : List Nat} {WR : List (List (List Nat))}
    (k : List Nat → Bool) {P' : List Nat} {c p : Nat} {acc : List Nat} {E : Nat → Nat}
    {e : Nat}
    (he : e = pcomp n w (mask w) (E p) (getK X (Nat.mod (lastK (getRG WR c [])) 2) 0))
    (hacc_p : getK acc (c.sub 1 - p) 0 = E p) :
    buildEGo n w X WR k (p :: P') c acc = buildEGo n w X WR k P' (c + 1) (e :: acc) := by
  have hstep : buildEGo n w X WR k (p :: P') c acc =
      strictB c (fun c =>
        strictB (pcomp n w (mask w) (getK acc (Nat.sub c 1 - p) 0)
          (getK X (Nat.mod (lastK (getRG WR c [])) 2) 0)) fun e =>
        buildEGo n w X WR k P' (c + 1) (e :: acc)) := by
    change List.rec (motive := fun _ => Nat → List Nat → Bool)
      (fun _ acc => List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
        (fun x _ ih r => ih (List.cons x r)) acc [])
      (fun p _ ih c acc => strictB c fun c =>
        strictB (pcomp n w (mask w) (getK acc (Nat.sub (Nat.sub c 1) p) 0)
          (getK X (Nat.mod (lastK (getRG WR c [])) 2) 0)) fun e =>
        ih (Nat.succ c) (List.cons e acc))
      (p :: P') c acc = _
    rfl
  rw [hstep, CFSG.KS.PF.strictB_eqP, CFSG.KS.PF.strictB_eqP, hacc_p, ← he]

private theorem buildE_go_spec (n w : Nat) (X : List Nat) (WR : List (List (List Nat)))
    (P0 : List Nat) (k : List Nat → Bool) :
    ∀ (P : List Nat) (c : Nat) (acc : List Nat) (E : Nat → Nat),
      0 < c → P = P0.drop (c - 1) → acc = (List.range c).reverse.map E →
      (∀ v, 0 < v → v < c →
        E v = pcomp n w (mask w) (E (getK P0 (v - 1) 0))
          (getK X (Nat.mod (lastK (getRG WR v [])) 2) 0)) →
      (∀ v, 0 < v → v < c + P.length → getK P0 (v - 1) 0 < v) →
      ∃ E' : Nat → Nat,
        buildEGo n w X WR k P c acc = k ((List.range (c + P.length)).map E') ∧
        (∀ v < c, E' v = E v) ∧
        (∀ v, 0 < v → v < c + P.length →
          E' v = pcomp n w (mask w) (E' (getK P0 (v - 1) 0))
            (getK X (Nat.mod (lastK (getRG WR v [])) 2) 0)) := by
  intro P
  induction P with
  | nil => simpa using buildE_go_spec_nil n w X WR P0 k
  | cons p P' ih =>
    intro c acc E hc hsuf hacc hrec hpar
    obtain ⟨hp_eq, hpc, hacc_p⟩ := buildE_go_spec_p (p := p) (P' := P') hc hsuf hacc hpar
    obtain ⟨E1, e, he, hsuf', hacc1, hE1c, hE1lt⟩ :=
      buildE_go_spec_acc (n := n) (w := w) (X := X) (WR := WR) (p := p) (P' := P') hc hsuf hacc
    have hrec1 := buildE_go_spec_rec (n := n) (w := w) (X := X) (WR := WR)
      (p := p) (P' := P') he hp_eq hpc hE1c hE1lt hrec hpar
    have hpar1 : ∀ v, 0 < v → v < c + 1 + P'.length → getK P0 (v - 1) 0 < v := by
      intro v hv hvlt
      exact hpar v hv (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hvlt)
    obtain ⟨E', hres, hagree, hrec'⟩ := ih (c + 1) (e :: acc) E1 (by omega) hsuf' hacc1
      hrec1 hpar1
    refine ⟨E', ?_, ?_, ?_⟩
    · rw [buildE_go_spec_step k he hacc_p]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hres
    · intro v hv
      rw [hagree v (by omega)]
      exact hE1lt v hv
    · intro v hv hvlt
      exact hrec' v hv (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hvlt)

theorem elaOf_nil (XA : Fin 2 → Array Nat) : elaOf XA [] = idA 1755 := by
  simp [elaOf]

theorem elaOf_append (XA : Fin 2 → Array Nat) (w : List Nat) (i : Fin 2) :
    elaOf XA (w ++ [(i : Nat)]) = compA 1755 (elaOf XA w) (XA i) := by
  simp [elaOf, List.foldl_append, List.foldl_cons, List.foldl_nil, fo_val]

private noncomputable def parGo (WR : List (List (List Nat))) :
    List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih v => strictB v fun v => CFSG.KC.Ord.andB (Nat.blt p v)
      (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (lenK (getRG WR v [])) 0))
        (CFSG.KC.Ord.andB (CFSG.KC.LQT.Syl.eqL
          (List.append (getRG WR p []) [lastK (getRG WR v [])]) (getRG WR v []))
          (ih (Nat.succ v)))))

private theorem parOK_eq (WR : List (List (List Nat))) (nV : Nat) (P : List Nat) :
    parOK WR nV P = CFSG.KC.Ord.andB (Nat.beq (Nat.succ (lenK P)) nV) (parGo WR P 1) := rfl

private theorem parGo_spec (WR : List (List (List Nat))) (P : List Nat) :
    ∀ v, parGo WR P v = true → ∀ k < P.length,
      getK P k 0 < v + k ∧ getRG WR (v + k) [] ≠ [] ∧
        getRG WR (getK P k 0) [] ++ [lastK (getRG WR (v + k) [])] =
          getRG WR (v + k) [] := by
  induction P with
  | nil => intro v hv k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons p P' ih =>
    intro v hv k hk
    have hstep : parGo WR (p :: P') v = strictB v (fun v => CFSG.KC.Ord.andB (Nat.blt p v)
        (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (lenK (getRG WR v [])) 0))
          (CFSG.KC.Ord.andB (CFSG.KC.LQT.Syl.eqL
            (List.append (getRG WR p []) [lastK (getRG WR v [])]) (getRG WR v []))
            (parGo WR P' (Nat.succ v))))) := by
      change List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun p _ ih v => strictB v fun v => CFSG.KC.Ord.andB (Nat.blt p v)
          (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (lenK (getRG WR v [])) 0))
            (CFSG.KC.Ord.andB (CFSG.KC.LQT.Syl.eqL
              (List.append (getRG WR p []) [lastK (getRG WR v [])]) (getRG WR v []))
              (ih (Nat.succ v))))) (p :: P') v = _
      rfl
    rw [hstep, CFSG.KS.PF.strictB_eqP, andB_eq', Bool.and_eq_true, Nat.blt_eq] at hv
    obtain ⟨hpv, hv⟩ := hv
    rw [andB_eq', Bool.and_eq_true] at hv
    obtain ⟨hbeq, hv⟩ := hv
    rw [notB_eq', Bool.not_eq_true'] at hbeq
    rw [andB_eq', Bool.and_eq_true] at hv
    obtain ⟨heq, hrest⟩ := hv
    rcases k with _ | k
    · refine ⟨by simpa [getK_getD] using hpv, ?_, ?_⟩
      · intro h0
        have h0' : getRG WR v [] = [] := by simpa using h0
        rw [h0'] at hbeq
        have htrue : Nat.beq (lenK ([] : List Nat)) 0 = true := by
          rw [CFSG.KC.LQT.Cov.Parse.lenK_length]
          rfl
        rw [htrue] at hbeq
        cases hbeq
      · simpa [getK_getD] using (CFSG.KC.LQT.Cov.Eqns.eqL_iff _ _).1 heq
    · have hk' : k < P'.length := by simpa using hk
      obtain ⟨hlt, hne', heq'⟩ := ih (v + 1) hrest k hk'
      refine ⟨?_, ?_, ?_⟩
      · simpa [getK_getD, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hne'
      · simpa [getK_getD, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq'

theorem parOK_spec {WR : List (List (List Nat))} {nV : Nat} {P : List Nat}
    (h : parOK WR nV P = true) :
    P.length + 1 = nV ∧ ∀ v, 0 < v → v < nV →
      getK P (v - 1) 0 < v ∧ getRG WR v [] ≠ [] ∧
        getRG WR (getK P (v - 1) 0) [] ++ [lastK (getRG WR v [])] = getRG WR v [] := by
  rw [parOK_eq, andB_eq', Bool.and_eq_true, Nat.beq_eq, CFSG.KC.LQT.Cov.Parse.lenK_length] at h
  obtain ⟨hnV, hgo⟩ := h
  refine ⟨hnV, ?_⟩
  intro v hv hvn
  have hk : v - 1 < P.length := by omega
  have := parGo_spec WR P 1 hgo (v - 1) hk
  have hv' : 1 + (v - 1) = v := by omega
  simpa [hv', getK_getD] using this

theorem lastK_lt {w : List Nat} (h : ∀ l ∈ w, l < 2) (hne : w ≠ []) : lastK w < 2 := by
  induction w with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · simpa [lastK] using h x (by simp)
    · have h' : ∀ l ∈ y :: ys, l < 2 := fun l hl => h l (by simp [hl])
      simpa [lastK] using ih h' (by simp)

private theorem getRG_words (d : CT) (hwords : d.words.length = d.nV) {v : Nat} (hv : v < d.nV) :
    getRG (rowsG d.words) v [] = d.words.getD v [] := by
  rw [getRG_rowsG_lt d.words v [] (by rw [hwords]; exact hv)]

theorem buildE_exists (d : CT) (X : List Nat) (P : List Nat) (k : List Nat → Bool)
    (hpar : parOK (rowsG d.words) d.nV P = true)
    (hbuild : buildE 1755 11 X (rowsG d.words) P k = true) :
    ∃ E : Nat → Nat,
      k ((List.range d.nV).map E) = true ∧ E 0 = pidn 1755 11 ∧
      (∀ v, 0 < v → v < d.nV →
        E v = pcomp 1755 11 (mask 11) (E (getK P (v - 1) 0))
          (getK X (Nat.mod (lastK (getRG (rowsG d.words) v [])) 2) 0)) := by
  obtain ⟨hnV, hpar'⟩ := parOK_spec hpar
  have hlenP : P.length = d.nV - 1 := by omega
  let E0 : Nat → Nat := fun _ => pidn 1755 11
  have hacc : [pidn 1755 11] = (List.range 1).reverse.map E0 := by
    simp [E0]
  have hrec : ∀ v, 0 < v → v < 1 →
      E0 v = pcomp 1755 11 (mask 11) (E0 (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG d.words) v [])) 2) 0) := by
    intro v hv hv1; omega
  have hpar0 : ∀ v, 0 < v → v < 1 + P.length → getK P (v - 1) 0 < v := by
    intro v hv hvlt
    exact (hpar' v hv (by omega)).1
  obtain ⟨E, hres, hagree, hrec'⟩ := buildE_go_spec 1755 11 X (rowsG d.words) P k P 1
    [pidn 1755 11] E0 (by omega) (by simp) hacc hrec hpar0
  refine ⟨E, ?_, by simpa [E0] using hagree 0 (by omega), ?_⟩
  · have hb' : buildEGo 1755 11 X (rowsG d.words) k P 1 [pidn 1755 11] = true := by
      rw [← buildE_eq_go]
      exact hbuild
    have hkres : k (List.map E (List.range (1 + P.length))) = true := by
      rw [← hres]
      exact hb'
    rwa [show 1 + P.length = d.nV by omega] at hkres
  · intro v hv0 hv
    exact hrec' v hv0 (by omega)

private theorem buildE_word_mem {d : CT} (hwords : d.words.length = d.nV)
    {v : Nat} (hv : v < d.nV) : d.words.getD v [] ∈ d.words := by
  rw [List.getD_eq_getElem?_getD]
  cases h : d.words[v]? with
  | none =>
    have hlt : v < d.words.length := by rw [hwords]; exact hv
    rw [List.getElem?_eq_getElem hlt] at h
    cases h
  | some w => simpa [h] using List.mem_of_getElem? h

theorem buildE_unpack (d : CT) (X : List Nat) (XA : Fin 2 → Array Nat) (P : List Nat)
    (E : Nat → Nat) (hwords : d.words.length = d.nV)
    (hletters : ∀ w ∈ d.words, ∀ l ∈ w, l < 2)
    (hpar : parOK (rowsG d.words) d.nV P = true)
    (hE0 : E 0 = pidn 1755 11)
    (hrec : ∀ v, 0 < v → v < d.nV →
      E v = pcomp 1755 11 (mask 11) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG d.words) v [])) 2) 0))
    (hX : ∀ i : Fin 2, CFSG.KS.Raw.unpack 1755 11 (getK X i 0) = XA i)
    (hXlt : ∀ i : Fin 2, ∀ j < 1755,
      CFSG.KC.Enum.pg 11 (mask 11) (getK X i 0) j < 1755)
    (hz : d.words.getD 0 [] = []) :
    ∀ v < d.nV, CFSG.KS.Raw.unpack 1755 11 (E v) = elaOf XA (d.words.getD v []) := by
  obtain ⟨hnV, hpar'⟩ := parOK_spec hpar
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    by_cases hv0 : v = 0
    · subst hv0
      rw [hE0, CFSG.KC.LQT.Cov.T.unpack_pidn (by norm_num) (by norm_num), hz, elaOf_nil]
    · have hpv : 0 < v := Nat.pos_of_ne_zero hv0
      obtain ⟨hparlt, hne, hwordeq⟩ := hpar' v hpv (by omega)
      have hmem : d.words.getD v [] ∈ d.words := buildE_word_mem hwords hv
      have hlast : lastK (d.words.getD v []) < 2 := by
        refine lastK_lt (fun l hl => hletters _ hmem l hl) ?_
        intro h0
        apply hne
        rw [getRG_words d hwords hv, h0]
      have hmod : Nat.mod (lastK (d.words.getD v [])) 2 = lastK (d.words.getD v []) :=
        Nat.mod_eq_of_lt hlast
      let i : Fin 2 := ⟨Nat.mod (lastK (d.words.getD v [])) 2, Nat.mod_lt _ (by norm_num)⟩
      have hi : (i : Nat) = lastK (d.words.getD v []) := by
        change Nat.mod (lastK (d.words.getD v [])) 2 = lastK (d.words.getD v [])
        exact hmod
      have hpv' : getK P (v - 1) 0 < d.nV := by omega
      rw [hrec v hpv hv, getRG_words d hwords hv]
      rw [← CFSG.KC.LQT.Cov.T.compA_unpack (n := 1755) (w := 11) (by norm_num) (hXlt i)]
      rw [ih (getK P (v - 1) 0) hparlt hpv', hX i]
      rw [← elaOf_append]
      have hwordeq' := hwordeq
      rw [getRG_words d hwords hv] at hwordeq'
      have hw : d.words.getD (getK P (v - 1) 0) [] ++ [(i : Nat)] = d.words.getD v [] := by
        rw [← getRG_words d hwords hpv', hi]
        exact hwordeq'
      rw [hw]

theorem buildE_canon {d : CT} {E : Nat → Nat} {P : List Nat} {X : List Nat}
    (hE0 : E 0 = pidn 1755 11)
    (hrec : ∀ v, 0 < v → v < d.nV →
      E v = pcomp 1755 11 (mask 11) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG d.words) v [])) 2) 0)) :
    ∀ v < d.nV, E v >>> (1755 * 11) = 0 := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    by_cases hv0 : v = 0
    · subst hv0
      rw [hE0]
      exact CFSG.KS.PF.pidn_shr (by norm_num) (by norm_num)
    · rw [hrec v (Nat.pos_of_ne_zero hv0) hv]
      exact CFSG.KS.PF.pcomp_shr _ _ (by norm_num) (by norm_num)

theorem toArray_getElem!_list (l : List (List Nat)) (i : Nat) :
    l.toArray[i]! = l.getD i [] := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => rfl
  | some x => rfl

private theorem elaTab_get (d : CT) {v : Nat} (hv : v < d.nV) :
    (ofCT d).elaTab[v]! = elaOf (ofCT d).xa (d.words.getD v []) := by
  unfold CovData.elaTab
  rw [CFSG.Sporadic.Schreier.Tits.getElem!_ofFn_of_lt]
  · congr 2
    change (ofCT d).words[v]! = d.words.getD v []
    rw [show (ofCT d).words = d.words.toArray from rfl, toArray_getElem!_list]
  · exact hv

private def GoodTStep (d : CT) (E : Nat → Nat) (P X : List Nat) (v i : Nat) : Prop :=
  strictB (getRG (rowsG d.tgt) (2 * v + i) d.nV) (fun t =>
    CFSG.KC.LQT.S.allBs [Nat.blt t d.nV,
      Nat.blt (getRG (rowsG d.back) (2 * v + i) d.nV) d.nV,
      Bool.rec
        (Nat.beq (getRG (rowsG (List.map E (List.range d.nV))) t 0)
          (pcomp 1755 11 (mask 11) (getRG (rowsG (List.map E (List.range d.nV))) v 0) (getK X i 0)))
        true
        (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq t 0))
          (CFSG.KC.Ord.andB (Nat.beq (getRG (rowsG P) (t - 1) 0) v)
            (Nat.beq (Nat.mod (lastK (getRG (rowsG d.words) t [])) 2) i))),
      Nat.beq (getRG (rowsG d.tgt) (2 * (getRG (rowsG d.back) (2 * v + i) 0) + i) 0) v]) = true

section GoodTStep

variable {d : CT} {E : Nat → Nat} {P X : List Nat}

private theorem goodT_step_prod_true
    (hwords : d.words.length = d.nV)
    (hrec : ∀ v, 0 < v → v < d.nV →
      E v = pcomp 1755 11 (mask 11) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG d.words) v [])) 2) 0))
    {v i : Nat} (hv : v < d.nV) (hstep : GoodTStep d E P X v i)
    (hcond : (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (d.tgt.getD (2 * v + i) d.nV) 0))
      (CFSG.KC.Ord.andB (Nat.beq (P.getD ((d.tgt.getD (2 * v + i) d.nV) - 1) 0) v)
        (Nat.beq (Nat.mod (lastK (d.words.getD
          (d.tgt.getD (2 * v + i) d.nV) [])) 2) i))) = true) :
    E (d.tgt.getD (2 * v + i) d.nV) =
      pcomp 1755 11 (mask 11) (E v) (getK X i 0) := by
  have hm := hstep
  unfold GoodTStep at hm
  rw [CFSG.KS.PF.strictB_eqP, CFSG.KC.LQT.BW.Pf.allBs_cons,
    CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_cons,
    CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true] at hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨ht, hm⟩ := hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨hb, hm⟩ := hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨hprodRaw, hback⟩ := hm
  simp only [getRG_rowsG, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hprodRaw hback
  have htlt : d.tgt.getD (2 * v + i) d.nV < d.nV := by
    simpa [getRG_rowsG] using ht
  rw [hcond] at hprodRaw
  simp at hprodRaw
  rw [andB_eq', Bool.and_eq_true, notB_eq', Bool.not_eq_true'] at hcond
  obtain ⟨ht0, hcond⟩ := hcond
  rw [andB_eq', Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hcond
  obtain ⟨hpar, hlast⟩ := hcond
  have ht0' : d.tgt.getD (2 * v + i) d.nV ≠ 0 := by
    intro h0
    rw [h0] at ht0
    simp at ht0
  have htpos : 0 < d.tgt.getD (2 * v + i) d.nV := Nat.pos_of_ne_zero ht0'
  have hparent : getK P ((d.tgt.getD (2 * v + i) d.nV) - 1) 0 = v := by
    rw [getK_getD, hpar]
  have hword : getRG (rowsG d.words) (d.tgt.getD (2 * v + i) d.nV) [] =
      d.words.getD (d.tgt.getD (2 * v + i) d.nV) [] :=
    getRG_words d hwords htlt
  rw [hrec (d.tgt.getD (2 * v + i) d.nV) htpos htlt, hparent, hword]
  congr 1
  have hlast' : Nat.mod (lastK (d.words.getD
      (d.tgt.getD (2 * v + i) d.nV) [])) 2 = i := by
    simpa [hword] using hlast
  rw [hlast']

private theorem goodT_step_prod
    (hwords : d.words.length = d.nV)
    (hrec : ∀ v, 0 < v → v < d.nV →
      E v = pcomp 1755 11 (mask 11) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG d.words) v [])) 2) 0))
    {v i : Nat} (hv : v < d.nV) (hstep : GoodTStep d E P X v i) :
    E (d.tgt.getD (2 * v + i) d.nV) =
      pcomp 1755 11 (mask 11) (E v) (getK X i 0) := by
  have hm := hstep
  unfold GoodTStep at hm
  rw [CFSG.KS.PF.strictB_eqP, CFSG.KC.LQT.BW.Pf.allBs_cons,
    CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_cons,
    CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true] at hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨ht, hm⟩ := hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨hb, hm⟩ := hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨hprodRaw, hback⟩ := hm
  simp only [getRG_rowsG, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hprodRaw hback
  have htlt : d.tgt.getD (2 * v + i) d.nV < d.nV := by
    simpa [getRG_rowsG] using ht
  have hERt : (List.map E (List.range d.nV)).getD (d.tgt.getD (2 * v + i) d.nV) 0 =
      E (d.tgt.getD (2 * v + i) d.nV) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [List.length_range]; exact htlt),
      Option.map_some, Option.getD_some, List.getElem_range]
  have hERv : (List.map E (List.range d.nV)).getD v 0 = E v := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [List.length_range]; exact hv),
      Option.map_some, Option.getD_some, List.getElem_range]
  by_cases hcond : (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (d.tgt.getD (2 * v + i) d.nV) 0))
      (CFSG.KC.Ord.andB (Nat.beq (P.getD ((d.tgt.getD (2 * v + i) d.nV) - 1) 0) v)
        (Nat.beq (Nat.mod (lastK (d.words.getD
          (d.tgt.getD (2 * v + i) d.nV) [])) 2) i))) = true
  · exact goodT_step_prod_true hwords hrec hv hstep hcond
  · have hfalse : (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (d.tgt.getD (2 * v + i) d.nV) 0))
        (CFSG.KC.Ord.andB (Nat.beq (P.getD ((d.tgt.getD (2 * v + i) d.nV) - 1) 0) v)
          (Nat.beq (Nat.mod (lastK (d.words.getD
            (d.tgt.getD (2 * v + i) d.nV) [])) 2) i))) = false := by
      rw [Bool.eq_false_iff]
      exact hcond
    rw [hfalse] at hprodRaw
    have := Nat.eq_of_beq_eq_true hprodRaw
    rw [hERt, hERv] at this
    exact this

private theorem goodT_step_check_aux
    {d : CT} {E : Nat → Nat} {P X : List Nat} {v i : Nat}
    (htA : (ofCT d).tgtA[2 * v + (i : Nat)]! = d.tgt.getD (2 * v + i) d.nV)
    (hbA : (ofCT d).backA[2 * v + (i : Nat)]! = d.back.getD (2 * v + i) d.nV)
    (hleft : (ofCT d).elaTab[d.tgt.getD (2 * v + i) d.nV]! =
      CFSG.KS.Raw.unpack 1755 11 (E (d.tgt.getD (2 * v + i) d.nV)))
    (hright : (ofCT d).elaTab[v]! = CFSG.KS.Raw.unpack 1755 11 (E v))
    (hprodU : CFSG.KS.Raw.unpack 1755 11 (E (d.tgt.getD (2 * v + i) d.nV)) =
      compA 1755 (CFSG.KS.Raw.unpack 1755 11 (E v)) ((ofCT d).xa (fo i)))
    (ht : Nat.blt (getRG (rowsG d.tgt) (2 * v + i) d.nV) d.nV = true)
    (hb : Nat.blt (getRG (rowsG d.back) (2 * v + i) d.nV) d.nV = true)
    (hbd : d.back.getD (2 * v + i) 0 = d.back.getD (2 * v + i) d.nV)
    (hback : Nat.beq (d.tgt.getD
      (2 * d.back.getD (2 * v + i) 0 + i) 0) v = true) :
    Nat.blt (ofCT d).tgtA[2 * v + (i : Nat)]! d.nV = true ∧
    Nat.blt (ofCT d).backA[2 * v + (i : Nat)]! d.nV = true ∧
    eqA 1755 (ofCT d).elaTab[(ofCT d).tgtA[2 * v + (i : Nat)]!]!
      (compA 1755 (ofCT d).elaTab[v]! ((ofCT d).xa (fo i))) = true ∧
    Nat.beq (ofCT d).tgtA[2 * (ofCT d).backA[2 * v + (i : Nat)]! + (i : Nat)]! v = true := by
  refine ⟨by rw [htA]; simpa [getRG_rowsG] using ht,
    by rw [hbA]; simpa [getRG_rowsG] using hb, ?_, ?_⟩
  · rw [htA, hleft, hright, hprodU, CFSG.KS.Raw.eqA_self]
  · rw [hbA, ← hbd, show (ofCT d).tgtA = d.tgt.toArray from rfl,
      CFSG.KC.LQT.Cov.Perm.arr_get]
    exact hback

private theorem goodT_step_check
    (hEunpack : ∀ v < d.nV, CFSG.KS.Raw.unpack 1755 11 (E v) = elaOf (ofCT d).xa (d.words.getD v []))
    (hX : ∀ i : Fin 2, CFSG.KS.Raw.unpack 1755 11 (getK X i 0) = (ofCT d).xa i)
    (hXlt : ∀ i : Fin 2, ∀ j < 1755,
      CFSG.KC.Enum.pg 11 (mask 11) (getK X i 0) j < 1755)
    {v i : Nat} (hv : v < d.nV) (hi : i < 2) (hstep : GoodTStep d E P X v i)
    (hprod : E (d.tgt.getD (2 * v + i) d.nV) =
      pcomp 1755 11 (mask 11) (E v) (getK X i 0)) :
    Nat.blt (ofCT d).tgtA[2 * v + (i : Nat)]! d.nV = true ∧
    Nat.blt (ofCT d).backA[2 * v + (i : Nat)]! d.nV = true ∧
    eqA 1755 (ofCT d).elaTab[(ofCT d).tgtA[2 * v + (i : Nat)]!]!
      (compA 1755 (ofCT d).elaTab[v]! ((ofCT d).xa (fo i))) = true ∧
    Nat.beq (ofCT d).tgtA[2 * (ofCT d).backA[2 * v + (i : Nat)]! + (i : Nat)]! v = true := by
  have hm := hstep
  unfold GoodTStep at hm
  rw [CFSG.KS.PF.strictB_eqP, CFSG.KC.LQT.BW.Pf.allBs_cons,
    CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_cons,
    CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true] at hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨ht, hm⟩ := hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨hb, hm⟩ := hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨hprodRaw, hback⟩ := hm
  simp only [getRG_rowsG, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hprodRaw hback
  have htlt : d.tgt.getD (2 * v + i) d.nV < d.nV := by
    simpa [getRG_rowsG] using ht
  have hblt : d.back.getD (2 * v + i) d.nV < d.nV := by
    simpa [getRG_rowsG] using hb
  obtain ⟨htidx, htd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt htlt
  obtain ⟨hbidx, hbd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt hblt
  have htA : (ofCT d).tgtA[2 * v + (i : Nat)]! = d.tgt.getD (2 * v + i) d.nV := by
    rw [show (ofCT d).tgtA = d.tgt.toArray from rfl, CFSG.KC.LQT.Cov.Perm.arr_get, ← htd]
  have hbA : (ofCT d).backA[2 * v + (i : Nat)]! = d.back.getD (2 * v + i) d.nV := by
    rw [show (ofCT d).backA = d.back.toArray from rfl, CFSG.KC.LQT.Cov.Perm.arr_get, ← hbd]
  have hleft : (ofCT d).elaTab[d.tgt.getD (2 * v + i) d.nV]! =
      CFSG.KS.Raw.unpack 1755 11 (E (d.tgt.getD (2 * v + i) d.nV)) := by
    rw [elaTab_get d htlt, ← hEunpack _ htlt]
  have hright : (ofCT d).elaTab[v]! = CFSG.KS.Raw.unpack 1755 11 (E v) := by
    rw [elaTab_get d hv, ← hEunpack v hv]
  have hfo : fo i = (⟨i, hi⟩ : Fin 2) := by
    simpa using (fo_val (⟨i, hi⟩ : Fin 2))
  have hprodU : CFSG.KS.Raw.unpack 1755 11 (E (d.tgt.getD (2 * v + i) d.nV)) =
      compA 1755 (CFSG.KS.Raw.unpack 1755 11 (E v)) ((ofCT d).xa (fo i)) := by
    rw [hfo, hprod]
    rw [← CFSG.KC.LQT.Cov.T.compA_unpack (n := 1755) (w := 11) (by norm_num)
      (hXlt ⟨i, hi⟩), hX ⟨i, hi⟩]
  exact goodT_step_check_aux (d := d) (E := E) (P := P) (X := X) htA hbA hleft hright hprodU ht hb hbd hback

private theorem goodT_distinct_step
    (hdist : CFSG.KC.LQT.T2.distinctS ((List.range d.nV).map E) = true)
    (hEunpack : ∀ v < d.nV, CFSG.KS.Raw.unpack 1755 11 (E v) = elaOf (ofCT d).xa (d.words.getD v []))
    (hEcanon : ∀ v < d.nV, E v >>> (1755 * 11) = 0)
    {u v : Nat} (hu : u < d.nV) (hv : v < d.nV) :
    (!decide (u < v) || !eqA 1755 (ofCT d).elaTab[u]! (ofCT d).elaTab[v]!) = true := by
  by_cases huv : u < v
  · have hdec : decide (u < v) = true := decide_eq_true huv
    rw [hdec]
    simp only [Bool.not_true, Bool.false_or]
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro heq
    have hnd : ((List.range d.nV).map E).Nodup :=
      CFSG.KC.LQT.T2.nodup_of_distinctS hdist
    have hpoint : ∀ j < 1755,
        (CFSG.KS.Raw.unpack 1755 11 (E u))[j]! =
          (CFSG.KS.Raw.unpack 1755 11 (E v))[j]! := by
      intro j hj
      have := (CFSG.KC.Co2Mem.eqA_iff).1 heq j hj
      simpa [elaTab_get d hu, elaTab_get d hv, hEunpack u hu, hEunpack v hv] using this
    have hEuv : E u = E v := by
      apply CFSG.KS.PF.eq_of_fields (by norm_num) (hEcanon u hu) (hEcanon v hv)
      intro j hj
      rw [← CFSG.KS.Raw.Orb.unpack_get hj, ← CFSG.KS.Raw.Orb.unpack_get hj]
      exact hpoint j hj
    have hlenu : u < ((List.range d.nV).map E).length := by
      rw [List.length_map, List.length_range]; exact hu
    have hlenv : v < ((List.range d.nV).map E).length := by
      rw [List.length_map, List.length_range]; exact hv
    have helem : ((List.range d.nV).map E)[u]'hlenu =
        ((List.range d.nV).map E)[v]'hlenv := by
      simp [List.getElem_map, List.getElem_range, hEuv]
    have := (List.Nodup.getElem_inj_iff hnd).1 helem
    omega
  · simp [huv]

end GoodTStep

private theorem goodT_base {d : CT} {E : Nat → Nat} {P X : List Nat}
    (hxw : d.xw.length = 2)
    (hll : CFSG.KC.LQT.T2.allT d.xw (CFSG.KS.Raw.lettersK 13) = true)
    (h : goodT d (rowsG d.words) (rowsG d.tgt) (rowsG d.back) (rowsG P) 1755 11 X
      (rowsG ((List.range d.nV).map E)) = true) :
    0 < d.nV ∧ d.words.getD 0 [] = [] ∧
      (ofCT d).xw0 = d.xw[0] ∧ (ofCT d).xw1 = d.xw[1] ∧
      CFSG.Monster.B.Co2.Native.lettersOK 13 d.xw[0] ∧
      CFSG.Monster.B.Co2.Native.lettersOK 13 d.xw[1] := by
  rw [goodT] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h0, hw0, -⟩ := h
  have h0' : 0 < d.nV := Nat.blt_eq.mp h0
  have hword0 : d.words.getD 0 [] = [] := by
    have hlen : (d.words.getD 0 [1]).length = 0 := by
      rw [← getK_getD]
      exact CFSG.KC.LQT.Cov.Parse.lenK_length .. ▸ Nat.beq_eq.mp hw0
    rw [List.getD_eq_getElem?_getD] at hlen ⊢
    cases h : d.words[0]? with
    | none => simp [h] at hlen
    | some w => simpa [h] using hlen
  have hxw0 : (ofCT d).xw0 = d.xw[0] := by
    change d.xw.getD 0 [] = d.xw[0]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hxw1 : (ofCT d).xw1 = d.xw[1] := by
    change d.xw.getD 1 [] = d.xw[1]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hll0 : CFSG.Monster.B.Co2.Native.lettersOK 13 d.xw[0] :=
    CFSG.KS.Prim.lettersK_sound
      ((CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hll (d.xw[0]) (List.getElem_mem (by omega)))
  have hll1 : CFSG.Monster.B.Co2.Native.lettersOK 13 d.xw[1] :=
    CFSG.KS.Prim.lettersK_sound
      ((CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hll (d.xw[1]) (List.getElem_mem (by omega)))
  exact ⟨h0', hword0, hxw0, hxw1, hll0, hll1⟩

theorem goodT_sound (d : CT) (E : Nat → Nat) (P : List Nat) (X : List Nat)
    (hwords : d.words.length = d.nV)
    (hxw : d.xw.length = 2)
    (hll : CFSG.KC.LQT.T2.allT d.xw (CFSG.KS.Raw.lettersK 13) = true)
    (hEunpack : ∀ v < d.nV, CFSG.KS.Raw.unpack 1755 11 (E v) = elaOf (ofCT d).xa (d.words.getD v []))
    (hEcanon : ∀ v < d.nV, E v >>> (1755 * 11) = 0)
    (hElt : ∀ v < d.nV, ∀ j < 1755, CFSG.KC.Enum.pg 11 (mask 11) (E v) j < 1755)
    (hX : ∀ i : Fin 2, CFSG.KS.Raw.unpack 1755 11 (getK X i 0) = (ofCT d).xa i)
    (hXlt : ∀ i : Fin 2, ∀ j < 1755,
      CFSG.KC.Enum.pg 11 (mask 11) (getK X i 0) j < 1755)
    (hrec : ∀ v, 0 < v → v < d.nV →
      E v = pcomp 1755 11 (mask 11) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG d.words) v [])) 2) 0))
    (hdist : CFSG.KC.LQT.T2.distinctS ((List.range d.nV).map E) = true)
    (h : goodT d (rowsG d.words) (rowsG d.tgt) (rowsG d.back) (rowsG P) 1755 11 X
      (rowsG ((List.range d.nV).map E)) = true) :
    goodCheck (ofCT d) (ofCT d).elaTab = true := by
  obtain ⟨h0', hword0, hxw0, hxw1, hll0, hll1⟩ :=
    goodT_base (d := d) (E := E) (P := P) (X := X) hxw hll h
  rw [goodT] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, -, hmain⟩ := h
  rw [CFSG.KC.LQT.Cov.Perm.allLtK_iff] at hmain
  rw [goodCheck]
  simp only [Bool.and_eq_true, decide_eq_true_eq, CFSG.Monster.B.Co2.allLt_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxw0]; exact hll0
  · rw [hxw1]; exact hll1
  · exact h0'
  · rw [show (ofCT d).words = d.words.toArray from rfl, toArray_getElem!_list]
    simpa using hword0
  · intro v hv i hi
    have hstep : GoodTStep d E P X v i := by
      unfold GoodTStep
      simpa [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
        Bool.and_true, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
        using (allLtK_iff _ _).1 (hmain v hv) i hi
    have hprod := goodT_step_prod (d := d) (E := E) (P := P) (X := X) hwords hrec hv hstep
    simpa [Nat.blt_eq, Nat.beq_eq, ofCT] using goodT_step_check (d := d) (E := E) (P := P) (X := X)
      hEunpack hX hXlt hv hi hstep hprod
  · intro u hu v hv
    exact goodT_distinct_step (d := d) (E := E) hdist hEunpack hEcanon hu hv

private theorem isInvA_unpack {n w p q : Nat}
    (h : CFSG.KC.Enum.permOK n w (mask w) (n * w) p q = true) :
    isInvA n (CFSG.KS.Raw.unpack n w p) (CFSG.KS.Raw.unpack n w q) = true := by
  have hpr := (CFSG.KC.LQT.Cov.T.perm_facts h).1
  rw [isInvA]
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [CFSG.KS.Raw.Orb.unpack_get hi, CFSG.KS.Raw.Orb.unpack_get (hpr i hi).1]
  simp [hpr i hi]

private structure BlkTStep (d : CT) (E : Nat → Nat)
    (bl : List Int × List Nat × List Nat × List (List (Nat × Bool))) (Ga Gi : Nat) (j : Nat) : Prop where
  ht : (getK bl.2.1 j d.nV).blt d.nV = true
  hb : (getK bl.2.2.1 j d.nV).blt d.nV = true
  hprod : Nat.beq (pcomp 1755 11 (mask 11)
      (pcomp 1755 11 (mask 11) Ga
        (getRG (rowsG ((List.range d.nV).map E)) (getK bl.2.1 j 0) 0)) Gi)
      (getRG (rowsG ((List.range d.nV).map E)) (getK bl.2.2.1 j 0) 0) = true

private theorem blkT_step_bounds {d : CT} {E : Nat → Nat}
    {bl : List Int × List Nat × List Nat × List (List (Nat × Bool))} {Ga Gi : Nat} {j : Nat}
    (s : BlkTStep d E bl Ga Gi j) :
    bl.2.1[j]! < d.nV ∧ bl.2.2.1[j]! < d.nV := by
  have ha' : bl.2.1.getD j d.nV < d.nV := by simpa [getK_getD] using s.ht
  have hb' : bl.2.2.1.getD j d.nV < d.nV := by simpa [getK_getD] using s.hb
  obtain ⟨hai, had⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt ha'
  obtain ⟨hbi, hbd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt hb'
  have hva : bl.2.1[j]! = bl.2.1.getD j d.nV := by
    rw [CFSG.KC.LQT.Cov.Perm.list_get, had]
  have hvb : bl.2.2.1[j]! = bl.2.2.1.getD j d.nV := by
    rw [CFSG.KC.LQT.Cov.Perm.list_get, hbd]
  exact ⟨by rw [hva]; exact ha', by rw [hvb]; exact hb'⟩

private theorem blkT_step_prod {d : CT} {E : Nat → Nat}
    {bl : List Int × List Nat × List Nat × List (List (Nat × Bool))} {Ga Gi : Nat} {j : Nat}
    (s : BlkTStep d E bl Ga Gi j) :
    bl.2.1.getD j d.nV < d.nV ∧ bl.2.2.1.getD j d.nV < d.nV ∧
      pcomp 1755 11 (mask 11)
        (pcomp 1755 11 (mask 11) Ga (E (bl.2.1.getD j d.nV))) Gi =
        E (bl.2.2.1.getD j d.nV) := by
  have ha' : bl.2.1.getD j d.nV < d.nV := by simpa [getK_getD] using s.ht
  have hb' : bl.2.2.1.getD j d.nV < d.nV := by simpa [getK_getD] using s.hb
  obtain ⟨hai, had⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt ha'
  obtain ⟨hbi, hbd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt hb'
  have had' : bl.2.1[j]?.getD 0 = bl.2.1[j]?.getD d.nV := by
    simpa [List.getD_eq_getElem?_getD] using had
  have hbd' : bl.2.2.1[j]?.getD 0 = bl.2.2.1[j]?.getD d.nV := by
    simpa [List.getD_eq_getElem?_getD] using hbd
  have hERa : getRG (rowsG ((List.range d.nV).map E)) (bl.2.1.getD j d.nV) 0 =
      E (bl.2.1.getD j d.nV) := by
    rw [getRG_rowsG, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [List.length_range]; exact ha'),
      Option.map_some, Option.getD_some, List.getElem_range]
  have hERb : getRG (rowsG ((List.range d.nV).map E)) (bl.2.2.1.getD j d.nV) 0 =
      E (bl.2.2.1.getD j d.nV) := by
    rw [getRG_rowsG, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [List.length_range]; exact hb'),
      Option.map_some, Option.getD_some, List.getElem_range]
  refine ⟨ha', hb', ?_⟩
  rw [← hERa, ← hERb]
  simpa [getK_getD, List.getD_eq_getElem?_getD, had', hbd'] using s.hprod

private theorem blkT_step_eq {d : CT} {E : Nat → Nat} {S SI : Nat → Nat}
    {bl : List Int × List Nat × List Nat × List (List (Nat × Bool))} {Ga Gi : Nat} {j : Nat}
    (hEunpack : ∀ v < d.nV, CFSG.KS.Raw.unpack 1755 11 (E v) =
      elaOf (ofCT d).xa (d.words.getD v []))
    (hElt : ∀ v < d.nV, ∀ j < 1755, CFSG.KC.Enum.pg 11 (mask 11) (E v) j < 1755)
    (hGa : CFSG.KS.Raw.unpack 1755 11 Ga = wordArr 1755 titsDerivedArrs bl.1)
    (hGi : CFSG.KS.Raw.unpack 1755 11 Gi =
      invCand 1755 (wordArr 1755 titsDerivedArrs bl.1))
    (hperm : CFSG.KC.Enum.permOK 1755 11 (mask 11) (1755 * 11) Ga Gi = true)
    (s : BlkTStep d E bl Ga Gi j) :
    eqA 1755 (compA 1755 (compA 1755 (wordArr 1755 titsDerivedArrs bl.1)
      (ofCT d).elaTab[bl.2.1[j]!]!) (invCand 1755 (wordArr 1755 titsDerivedArrs bl.1)))
      (ofCT d).elaTab[bl.2.2.1[j]!]! = true := by
  obtain ⟨ha', hb', hprod'⟩ := blkT_step_prod s
  obtain ⟨hai, had⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt ha'
  obtain ⟨hbi, hbd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt hb'
  have hva : bl.2.1[j]! = bl.2.1.getD j d.nV := by
    rw [CFSG.KC.LQT.Cov.Perm.list_get, had]
  have hvb : bl.2.2.1[j]! = bl.2.2.1.getD j d.nV := by
    rw [CFSG.KC.LQT.Cov.Perm.list_get, hbd]
  have hleft : (ofCT d).elaTab[bl.2.1[j]!]! =
      CFSG.KS.Raw.unpack 1755 11 (E (bl.2.1.getD j d.nV)) := by
    rw [hva, elaTab_get d ha', hEunpack _ ha']
  have hright : (ofCT d).elaTab[bl.2.2.1[j]!]! =
      CFSG.KS.Raw.unpack 1755 11 (E (bl.2.2.1.getD j d.nV)) := by
    rw [hvb, elaTab_get d hb', hEunpack _ hb']
  have hU : CFSG.KS.Raw.unpack 1755 11
      (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) Ga
        (E (bl.2.1.getD j d.nV))) Gi) =
      compA 1755 (compA 1755 (wordArr 1755 titsDerivedArrs bl.1)
        (CFSG.KS.Raw.unpack 1755 11 (E (bl.2.1.getD j d.nV))))
        (invCand 1755 (wordArr 1755 titsDerivedArrs bl.1)) := by
    have hGiRange : ∀ i < 1755, CFSG.KC.Enum.pg 11 (mask 11) Gi i < 1755 := by
      intro i hi
      obtain ⟨k, hk, hki⟩ := (CFSG.KC.LQT.Cov.T.perm_facts hperm).2 i hi
      rw [← hki, ((CFSG.KC.LQT.Cov.T.perm_facts hperm).1 k hk).2]
      exact hk
    rw [← CFSG.KC.LQT.Cov.T.compA_unpack (n := 1755) (w := 11)
      (p := pcomp 1755 11 (mask 11) Ga (E (bl.2.1.getD j d.nV)))
      (q := Gi) (by norm_num) hGiRange]
    rw [← CFSG.KC.LQT.Cov.T.compA_unpack (n := 1755) (w := 11) (by norm_num)
      (hElt (bl.2.1.getD j d.nV) ha')]
    rw [hGa, hGi]
  rw [hleft, hright, ← hU, hprod']
  exact CFSG.KS.Raw.eqA_self (CFSG.KS.Raw.unpack 1755 11 (E (bl.2.2.1.getD j d.nV)))

theorem blkT_sound (d : CT) (E : Nat → Nat) (P : List Nat)
    (S SI : Nat → Nat)
    (bl : List Int × List Nat × List Nat × List (List (Nat × Bool)))
    (hwords : d.words.length = d.nV)
    (hEunpack : ∀ v < d.nV, CFSG.KS.Raw.unpack 1755 11 (E v) =
      elaOf (ofCT d).xa (d.words.getD v []))
    (hElt : ∀ v < d.nV, ∀ j < 1755, CFSG.KC.Enum.pg 11 (mask 11) (E v) j < 1755)
    (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j))
    (hperm : ∀ j < 13, CFSG.KC.Enum.permOK 1755 11 (mask 11) (1755 * 11) (S j) (SI j) = true)
    (hsz : CFSG.KS.Raw.szOK 1755 11 = true)
    (h : blkT 1755 11 13 S SI d (rowsG ((List.range d.nV).map E)) bl = true) :
    blkCheck (ofCT d) (ofCT d).elaTab
      { gw := bl.1, va := bl.2.1, vb := bl.2.2.1, rhos := bl.2.2.2 } = true := by
  set blk : Blk := { gw := bl.1, va := bl.2.1, vb := bl.2.2.1, rhos := bl.2.2.2 }
  rw [blkT] at h
  simp only [CFSG.KS.PF.strictB_eqP] at h
  set Ga := CFSG.KS.Raw.wordK 1755 11 (mask 11) (CFSG.KC.Enum.pidn 1755 11) S SI bl.1
    with hGaDef
  set Gi := pinvS 1755 11 (mask 11) Ga with hGiDef
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons,
    CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hl, hperm', hlen, h32, hall⟩ := h
  rw [allLtK_iff] at hall
  have hGa : CFSG.KS.Raw.unpack 1755 11 Ga =
      wordArr 1755 titsDerivedArrs bl.1 := by
    rw [hGaDef]
    exact (wordArr_eq_unpack hS hperm hsz hl).symm
  have hGi : CFSG.KS.Raw.unpack 1755 11 Gi =
      invCand 1755 (wordArr 1755 titsDerivedArrs bl.1) := by
    rw [hGiDef, ← hGa]
    exact (CFSG.KC.LQT.Cov.T.invCand_unpack hperm').symm
  rw [blkCheck]
  simp only [Bool.and_eq_true, decide_eq_true_eq, CFSG.Monster.B.Co2.allLt_iff,
    and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.KS.Prim.lettersK_sound hl
  · simpa [hGa, hGi] using isInvA_unpack hperm'
  · simpa [blk, CFSG.KC.LQT.Cov.Parse.lenK_length] using Nat.beq_eq.mp hlen
  · simpa [blk, CFSG.KC.LQT.Cov.Parse.lenK_length] using Nat.ble_eq.mp h32
  · intro j hj
    have hj' : j < lenK bl.2.1 := by
      simpa [blk, CFSG.KC.LQT.Cov.Parse.lenK_length] using hj
    have hm := hall j hj'
    simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
      Bool.and_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hm
    obtain ⟨ha, hb, hprod⟩ := hm
    let s : BlkTStep d E bl Ga Gi j :=
      ⟨Nat.blt_eq.mpr ha, Nat.blt_eq.mpr hb, Nat.beq_eq.mpr hprod⟩
    obtain ⟨h1, h2⟩ := blkT_step_bounds (d := d) (E := E) s
    exact ⟨h1, h2, (by simpa using blkT_step_eq (d := d) (E := E) (S := S) (SI := SI) hEunpack hElt hGa hGi hperm' s)⟩
theorem buildE_range {d : CT} {E : Nat → Nat} {P : List Nat} {X : List Nat}
    (hE0 : E 0 = CFSG.KC.Enum.pidn 1755 11)
    (hrec : ∀ v, 0 < v → v < d.nV →
      E v = pcomp 1755 11 (mask 11) (E (getK P (v - 1) 0))
        (getK X (Nat.mod (lastK (getRG (rowsG d.words) v [])) 2) 0))
    (hXlt : ∀ i : Fin 2, ∀ j < 1755, CFSG.KC.Enum.pg 11 (mask 11) (getK X i 0) j < 1755)
    (hpar : ∀ v, 0 < v → v < d.nV → getK P (v - 1) 0 < v) :
    ∀ v < d.nV, ∀ i < 1755, CFSG.KC.Enum.pg 11 (mask 11) (E v) i < 1755 := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv i hi
    by_cases hv0 : v = 0
    · subst hv0
      rw [hE0, CFSG.KS.PF.pg_pidn (n := 1755) (w := 11) (by norm_num) (by norm_num) hi]
      exact hi
    · have hpv : 0 < v := Nat.pos_of_ne_zero hv0
      have hp : getK P (v - 1) 0 < v := hpar v hpv hv
      rw [hrec v hpv hv, CFSG.KS.PF.pg_pcomp (by norm_num) hi]
      have hqi : CFSG.KC.Enum.pg 11 (mask 11)
          (getK X (Nat.mod (lastK (getRG (rowsG d.words) v [])) 2) 0) i < 1755 :=
        hXlt ⟨_, Nat.mod_lt _ (by norm_num)⟩ i hi
      exact ih (getK P (v - 1) 0) hp (by omega) _ hqi

end CFSG.KC.LQT.Cov.T

end
