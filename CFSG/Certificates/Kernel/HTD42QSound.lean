module

public import Certificates.Data.Kernel.HTD42Q
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterRep
import CFSG.Certificates.Kernel.D4PlaneSound

public section

namespace CFSG.KC.HTD42Q

open CFSG.Quasithin CFSG.AGLEmbedding CFSG.AGLEmbedding.D4Two CFSG.KC.D4PlaneP
open CFSG.AGLEmbedding.ChevOuter (Pr frobArr frobPow getD_frobArr rep_wordP)

@[expose] def encQ (p : Pr) : Nat × Nat := (packA p.1, p.2)

theorem encQ_mk (A : Array GF8) (j : Nat) : encQ (A, j) = (packA A, j) := rfl

theorem qrec_and (x y : Bool) : Bool.rec (motive := fun _ => Bool) false y x = (x && y) := by
  cases x <;> rfl

theorem qrec_or (x r : Bool) : Bool.rec (motive := fun _ => Bool) r true x = (x || r) := by
  cases x <;> rfl

theorem qrec_imp (x y : Bool) : Bool.rec (motive := fun _ => Bool) true y x = (!x || y) := by
  cases x <;> rfl

theorem qrec_all {α : Type} (p : α → Bool) (L : List α) :
    List.rec (motive := fun _ => Bool) true
      (fun a _ r => Bool.rec (motive := fun _ => Bool) false r (p a)) L = L.all p := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.all_cons, ← ih]
    exact qrec_and _ _

theorem qrec_any {α : Type} (p : α → Bool) (L : List α) :
    List.rec (motive := fun _ => Bool) false
      (fun a _ r => Bool.rec (motive := fun _ => Bool) r true (p a)) L = L.any p := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.any_cons, ← ih]
    exact qrec_or _ _

theorem eqQ_eq (a b : Nat × Nat) : eqQ a b = (Nat.beq a.1 b.1 && Nat.beq a.2 b.2) :=
  qrec_and _ _

theorem eq_of_eqQ {a b : Nat × Nat} (h : eqQ a b = true) : a = b := by
  rw [eqQ_eq, Bool.and_eq_true] at h
  exact Prod.ext (Nat.eq_of_beq_eq_true h.1) (Nat.eq_of_beq_eq_true h.2)

theorem eqQ_self (a : Nat × Nat) : eqQ a a = true := by
  rw [eqQ_eq, Bool.and_eq_true]
  exact ⟨Nat.beq_refl _, Nat.beq_refl _⟩

theorem witY_eq (G : List (Nat × Nat)) (y : Nat × Nat) :
    witY G y = (!cubeQ y || G.any fun g => fixQ y g.1 && fixQ y g.2) := by
  unfold witY
  rw [qrec_imp, qrec_any (fun g : Nat × Nat =>
    Bool.rec (motive := fun _ => Bool) false (fixQ y g.2) (fixQ y g.1))]
  simp only [qrec_and]

theorem witAll_eq (x : Nat × Nat) (G : List (Nat × Nat)) (L : List Nat) :
    witAll x G L = L.all fun e => witY G (mulQ (e, 0) x) :=
  qrec_all (fun e => witY G (mulQ (e, 0) x)) L

theorem planesQ_eq (G : List (Nat × Nat)) : planesQ G = G.all fun g => planeQ g.1 g.2 := by
  unfold planesQ
  exact qrec_all (fun g : Nat × Nat => planeQ g.1 g.2) G

theorem gensP_eq (es : List Nat) : gensP es = gensI.map fun p => (atP es p.1, atP es p.2) := rfl

theorem frobF_bits (e : GF8) : (ChevOuter.frobF e).toNat.testBit 0 = e.toNat.testBit 0 ∧
    (ChevOuter.frobF e).toNat.testBit 1 = e.toNat.testBit 2 ∧
    (ChevOuter.frobF e).toNat.testBit 2 = (e.toNat.testBit 1 ^^ e.toNat.testBit 2) := by
  revert e
  decide +kernel

theorem testBit_packA_pos (A : Array GF8) (q L : Nat) (hq : q < 64) :
    (packA A).testBit (q + 64 * L) = (A.getD q 0).toNat.testBit L := by
  have e1 : (q + 64 * L) % 64 = q := by omega
  have e2 : (q + 64 * L) / 64 = L := by omega
  rw [testBit_packA, e1, e2]

theorem testBit_frK (X n : Nat) : (frK X).testBit n =
    (((X.testBit n && decide (n < 64)) ||
      (decide (n ≥ 64) && (X.testBit (128 + (n - 64)) && decide (n - 64 < 64)))) ||
      (decide (n ≥ 128) &&
        ((X.testBit (64 + (n - 128)) ^^ X.testBit (128 + (n - 128))) && decide (n - 128 < 64)))) := by
  simp only [frK, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_xor, testBit_m64]

theorem frK_packA (A : Array GF8) : frK (packA A) = packA (frobArr A) := by
  apply Nat.eq_of_testBit_eq
  intro n
  obtain ⟨q, L, hq, rfl⟩ : ∃ q L, q < 64 ∧ n = q + 64 * L :=
    ⟨n % 64, n / 64, Nat.mod_lt _ (by decide), by omega⟩
  rw [testBit_frK, testBit_packA_pos (frobArr A) _ _ hq, getD_frobArr]
  obtain ⟨b0, b1, b2⟩ := frobF_bits (A.getD q 0)
  obtain h | h | h | h : L = 0 ∨ L = 1 ∨ L = 2 ∨ 3 ≤ L := by omega
  · subst h
    have d1 : decide (q + 64 * 0 < 64) = true := decide_eq_true (by omega)
    have d2 : decide (q + 64 * 0 ≥ 64) = false := decide_eq_false (by omega)
    have d3 : decide (q + 64 * 0 ≥ 128) = false := decide_eq_false (by omega)
    simp only [d1, d2, d3, Bool.and_true, Bool.false_and, Bool.or_false]
    rw [testBit_packA_pos _ _ _ hq, b0]
  · subst h
    have d1 : decide (q + 64 * 1 < 64) = false := decide_eq_false (by omega)
    have d2 : decide (q + 64 * 1 ≥ 64) = true := decide_eq_true (by omega)
    have d3 : decide (q + 64 * 1 - 64 < 64) = true := decide_eq_true (by omega)
    have d4 : decide (q + 64 * 1 ≥ 128) = false := decide_eq_false (by omega)
    have i1 : 128 + (q + 64 * 1 - 64) = q + 64 * 2 := by omega
    simp only [d1, d2, d3, d4, i1, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
      Bool.or_false, Bool.false_or]
    rw [testBit_packA_pos _ _ _ hq, b1]
  · subst h
    have d1 : decide (q + 64 * 2 < 64) = false := decide_eq_false (by omega)
    have d2 : decide (q + 64 * 2 - 64 < 64) = false := decide_eq_false (by omega)
    have d3 : decide (q + 64 * 2 ≥ 128) = true := decide_eq_true (by omega)
    have d4 : decide (q + 64 * 2 - 128 < 64) = true := decide_eq_true (by omega)
    have i1 : 64 + (q + 64 * 2 - 128) = q + 64 * 1 := by omega
    have i2 : 128 + (q + 64 * 2 - 128) = q + 64 * 2 := by omega
    simp only [d1, d2, d3, d4, i1, i2, Bool.and_true, Bool.and_false, Bool.true_and,
      Bool.false_and, Bool.or_false, Bool.false_or]
    rw [testBit_packA_pos _ _ _ hq, testBit_packA_pos _ _ _ hq, b2]
  · have d1 : decide (q + 64 * L < 64) = false := decide_eq_false (by omega)
    have d2 : decide (q + 64 * L - 64 < 64) = false := decide_eq_false (by omega)
    have d3 : decide (q + 64 * L - 128 < 64) = false := decide_eq_false (by omega)
    simp only [d1, d2, d3, Bool.and_false, Bool.false_or]
    rw [testBit_toNat_hi _ _ h]

theorem frN_packA (n : Nat) (A : Array GF8) : frN n (packA A) = packA (frobPow n A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change frK (frN n (packA A)) = packA (frobArr (frobPow n A))
    rw [ih, frK_packA]

theorem encQ_mulP (p q : Pr) : encQ (ChevOuter.mulP p q) = mulQ (encQ p) (encQ q) := by
  refine Prod.ext ?_ rfl
  change packA (mulArr p.1 (frobPow p.2 q.1)) = mulP (packA p.1) (frN p.2 (packA q.1))
  rw [packA_mulArr, frN_packA]

theorem encQ_oneP : encQ ChevOuter.oneP = (oneP, 0) := by
  change (packA oneArr, 0) = (oneP, 0)
  rw [packA_oneArr]

theorem eq_of_eqQ_enc {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64)
    (h : eqQ (encQ p) (encQ q) = true) : p = q :=
  have e : encQ p = encQ q := eq_of_eqQ h
  have e1 : (encQ p).1 = (encQ q).1 := congrArg Prod.fst e
  have e2 : (encQ p).2 = (encQ q).2 := congrArg Prod.snd e
  Prod.ext (packA_inj hp hq e1) e2

theorem cube_of_cubeQ {y : Pr} (h : cubeQ (encQ y) = true) :
    ChevOuter.mulP y (ChevOuter.mulP y y) = ChevOuter.oneP := by
  unfold cubeQ at h
  rw [← encQ_mulP, ← encQ_mulP, ← encQ_oneP] at h
  exact eq_of_eqQ_enc (size_mulArr _ _) size_oneArr h

theorem cubeQ_of_cube {y : Pr} (h : ChevOuter.mulP y (ChevOuter.mulP y y) = ChevOuter.oneP) :
    cubeQ (encQ y) = true := by
  unfold cubeQ
  rw [← encQ_mulP, ← encQ_mulP, h, encQ_oneP]
  exact eqQ_self _

theorem fixQ_spec {y : Pr} {F : Array GF8} (h : fixQ (encQ y) (packA F) = true) :
    mulArr y.1 (frobPow y.2 F) = mulArr F y.1 := by
  have h' : Nat.beq (packA (mulArr y.1 (frobPow y.2 F))) (packA (mulArr F y.1)) = true := by
    rw [packA_mulArr, packA_mulArr, ← frN_packA]
    exact h
  exact packA_inj (size_mulArr _ _) (size_mulArr _ _) (Nat.eq_of_beq_eq_true h')

theorem planeQ_spec {u v : Array GF8} (hu : u.size = 64) (hv : v.size = 64)
    (h : planeQ (packA u) (packA v) = true) :
    mulArr u (mulArr u u) = oneArr ∧ mulArr v (mulArr v v) = oneArr ∧ mulArr u v = mulArr v u ∧
      u ≠ oneArr ∧ v ≠ oneArr ∧ v ≠ u ∧ v ≠ mulArr u u := by
  simp only [planeQ, cube1P, commP, Bool.and', Bool.not', Bool.and_eq_true,
    Bool.not_eq_true', beq_iff_eq, ← packA_mulArr, ← packA_oneArr] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨packA_inj (size_mulArr _ _) size_oneArr h1, packA_inj (size_mulArr _ _) size_oneArr h2,
    packA_inj (size_mulArr _ _) (size_mulArr _ _) h3,
    fun e => Nat.ne_of_beq_eq_false h4 (congrArg packA e),
    fun e => Nat.ne_of_beq_eq_false h5 (congrArg packA e),
    fun e => Nat.ne_of_beq_eq_false h6 (congrArg packA e),
    fun e => Nat.ne_of_beq_eq_false h7 (congrArg packA e)⟩

section Twin

variable {ls : List Nat} (hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0)

include hL

theorem encQ_symP (s : Nat) : encQ (ChevOuter.symP s) = symQ ls s := by
  unfold ChevOuter.symP
  rw [symQ]
  by_cases hs : s < 18
  · have hb : Nat.blt s 18 = true := Nat.blt_eq ▸ hs
    rw [if_pos hs, hb]
    change (packA (letterArr s), 0) = (letP ls s, 0)
    rw [packA_letterArr hL]
  · have hb : Nat.blt s 18 = false := Bool.eq_false_iff.2 fun e => hs (Nat.blt_eq ▸ e)
    rw [if_neg hs, hb]
    change (packA oneArr, 1) = (oneP, 1)
    rw [packA_oneArr]

theorem encQ_wordP (w : List Nat) : encQ (ChevOuter.wordP w) = wordQ ls w := by
  induction w with
  | nil => exact encQ_oneP
  | cons s w ih =>
    change encQ (ChevOuter.mulP (ChevOuter.symP s) (ChevOuter.wordP w)) =
      mulQ (symQ ls s) (wordQ ls w)
    rw [encQ_mulP, encQ_symP hL, ih]

theorem cube_wordP {w : List Nat} (h : cubeQ (wordQ ls w) = true) :
    ChevOuter.mulP (ChevOuter.wordP w) (ChevOuter.mulP (ChevOuter.wordP w) (ChevOuter.wordP w)) =
      ChevOuter.oneP := by
  rw [← encQ_wordP hL] at h
  exact cube_of_cubeQ h

theorem frob_wordP {w : List Nat} {j : Nat} (h : Nat.beq (wordQ ls w).2 j = true) :
    (ChevOuter.wordP w).2 = j := by
  rw [← encQ_wordP hL] at h
  exact Nat.eq_of_beq_eq_true h

variable {es : List Nat} (hE : bfsOK (wordP ls wordA) (wordP ls wordB) bfsPar es = true)

include hE

omit hL hE in
theorem atP_of_map (hS : sylowElems.map packA = es) (i : Nat) :
    atP es i = packA (sylowElemAt i) := by
  rw [← hS, packA_sylowElemAt]

theorem map_sylowElems_es : sylowElems.map packA = es :=
  (map_sylowElems hL).trans (bfsP_of_bfsOK _ _ _ _ hE)

theorem norm_sylow (w v : List Nat) (i : Nat)
    (h : eqQ (mulQ (wordQ ls w) (wordP ls v, 0)) (mulQ (atP es i, 0) (wordQ ls w)) = true) :
    ChevOuter.mulP (ChevOuter.wordP w) (wordArr v, 0) =
      ChevOuter.mulP (sylowElemAt i, 0) (ChevOuter.wordP w) := by
  rw [← encQ_wordP hL w, ← packA_wordArr hL v, atP_of_map (map_sylowElems_es hL hE) i,
    ← encQ_mk, ← encQ_mk, ← encQ_mulP, ← encQ_mulP] at h
  exact eq_of_eqQ_enc (size_mulArr _ _) (size_mulArr _ _) h

theorem planes_sylow (h : planesQ (gensP es) = true) : ∀ p ∈ gensI,
    mulArr (sylowElemAt p.1) (mulArr (sylowElemAt p.1) (sylowElemAt p.1)) = oneArr ∧
      mulArr (sylowElemAt p.2) (mulArr (sylowElemAt p.2) (sylowElemAt p.2)) = oneArr ∧
      mulArr (sylowElemAt p.1) (sylowElemAt p.2) = mulArr (sylowElemAt p.2) (sylowElemAt p.1) ∧
      sylowElemAt p.1 ≠ oneArr ∧ sylowElemAt p.2 ≠ oneArr ∧ sylowElemAt p.2 ≠ sylowElemAt p.1 ∧
      sylowElemAt p.2 ≠ mulArr (sylowElemAt p.1) (sylowElemAt p.1) := by
  rw [planesQ_eq, gensP_eq, List.all_map, List.all_eq_true] at h
  intro p hp
  have hp' := h p hp
  simp only [Function.comp_apply, atP_of_map (map_sylowElems_es hL hE)] at hp'
  exact planeQ_spec (size_sylowElemAt _) (size_sylowElemAt _) hp'

theorem witAll_sylow (hWa : witAll (wordQ ls xW) (gensP es) (es.take 40) = true)
    (hWb : witAll (wordQ ls xW) (gensP es) (es.drop 40) = true) :
    ∀ A ∈ sylowElems, ∀ y : Pr, y = ChevOuter.mulP (A, 0) (ChevOuter.wordP xW) →
      ChevOuter.mulP y (ChevOuter.mulP y y) = ChevOuter.oneP →
      ∃ p ∈ gensI, mulArr y.1 (frobPow y.2 (sylowElemAt p.1)) = mulArr (sylowElemAt p.1) y.1 ∧
        mulArr y.1 (frobPow y.2 (sylowElemAt p.2)) = mulArr (sylowElemAt p.2) y.1 := by
  intro A hA y hy h3
  have hS := map_sylowElems_es hL hE
  have hmem : packA A ∈ es := by
    rw [← hS]
    exact List.mem_map_of_mem hA
  have hwy : witY (gensP es) (mulQ (packA A, 0) (wordQ ls xW)) = true := by
    rw [← List.take_append_drop 40 es, List.mem_append] at hmem
    rw [witAll_eq, List.all_eq_true] at hWa hWb
    rcases hmem with he | he
    · exact hWa _ he
    · exact hWb _ he
  have henc : mulQ (packA A, 0) (wordQ ls xW) = encQ y := by
    rw [hy, encQ_mulP, encQ_wordP hL]
    rfl
  rw [henc, witY_eq, cubeQ_of_cube h3] at hwy
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true] at hwy
  obtain ⟨g, hg, h1, h2⟩ := hwy
  rw [gensP_eq, List.mem_map] at hg
  obtain ⟨p, hp, rfl⟩ := hg
  simp only [atP_of_map hS] at h1 h2
  exact ⟨p, hp, fixQ_spec h1, fixQ_spec h2⟩

end Twin

end CFSG.KC.HTD42Q

end
