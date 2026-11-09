module

public import CFSG.Certificates.Kernel.OpsLayFillSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerDefs
import CFSG.Certificates.Kernel.CosetLat.MatEnc
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.KC.OpsLayK.Snd
open CFSG.AGLEmbedding.R3 (Der)

@[expose] def derLetter (s t : Nat) (q : Nat × Nat) : List Op :=
  bif Nat.beq q.2 1 then [.mul t q.1 t] else [.pow q.2 q.1 s, .mul t s t]

@[expose] def derOps (s t : Nat) : Word → List Op
  | [] => []
  | (a, e) :: w => .pow e a t :: w.flatMap (derLetter s t)

@[expose] def derProg (s : Nat) (ds : List Der) : List Op :=
  ds.flatMap fun d => derOps s d.reg d.w

@[expose] def derChk (n s : Nat) : List Nat → List Der → Bool
  | _, [] => true
  | av, d :: ds => decide (d.reg < n) && !memB d.reg av && !d.w.isEmpty && wordOK n d.w &&
      wordIn av d.w && (decide (s < n) && !memB s (d.reg :: av)) && derChk n s (d.reg :: av) ds

@[expose] def opEqB : Op → Op → Bool
  | .mul i j t, .mul i' j' t' => Nat.beq i i' && Nat.beq j j' && Nat.beq t t'
  | .pow e i t, .pow e' i' t' => Nat.beq e e' && Nat.beq i i' && Nat.beq t t'
  | _, _ => false

@[expose] def opsEqB : List Op → List Op → Bool
  | [], [] => true
  | o :: l, o' :: l' => opEqB o o' && opsEqB l l'
  | _, _ => false

theorem eq_of_opEqB : ∀ {o o' : Op}, opEqB o o' = true → o = o'
  | .mul i j t, .mul i' j' t', h => by
    simp only [opEqB, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2]
  | .pow e i t, .pow e' i' t', h => by
    simp only [opEqB, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2]
  | .mul _ _ _, .pow _ _ _, h => Bool.noConfusion h
  | .pow _ _ _, .mul _ _ _, h => Bool.noConfusion h

theorem eq_of_opsEqB : ∀ {l l' : List Op}, opsEqB l l' = true → l = l'
  | [], [], _ => rfl
  | o :: l, o' :: l', h => by
    simp only [opsEqB, Bool.and_eq_true] at h
    rw [eq_of_opEqB h.1, eq_of_opsEqB h.2]
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h

section

variable {c : Lay}

theorem mul_assoc_canon (hc : c.ok = true) {x y z : Nat} (hx : CFSG.KS.Ord.Canon c.p c.d c.w x)
    (hy : CFSG.KS.Ord.Canon c.p c.d c.w y) (hz : CFSG.KS.Ord.Canon c.p c.d c.w z) :
    c.mul (c.mul x y) z = c.mul x (c.mul y z) := by
  obtain ⟨-, hS, hw, -⟩ := CFSG.KS.Ord.consts_facts hc
  obtain ⟨cxy, mxy⟩ := SecS.mul_sound c hc hx hy
  obtain ⟨cyz, myz⟩ := SecS.mul_sound c hc hy hz
  obtain ⟨c1, m1⟩ := SecS.mul_sound c hc cxy hz
  obtain ⟨c2, m2⟩ := SecS.mul_sound c hc hx cyz
  refine CFSG.KC.CosetLat.canon_eq_of_ordMat hw c1 c2 ?_
  rw [← hS, m1, m2, mxy, myz, mul_assoc]

theorem derPowK_one (x : Nat) : powK c x 1 = x := rfl

theorem derGetR_self {R : List Nat} {t x : Nat} (ht : t < R.length) : getR c (R.set t x) t = x := by
  simp [getR, List.getD_eq_getElem?_getD, ht]

theorem derGetR_ne {R : List Nat} {t r x : Nat} (h : t ≠ r) : getR c (R.set t x) r = getR c R r := by
  simp [getR, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem derCanon_set {R : List Nat} (hR : ∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c R r)) {t x : Nat}
    (ht : t < R.length) (hx : CFSG.KS.Ord.Canon c.p c.d c.w x) :
    ∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c (R.set t x) r) := by
  intro r
  by_cases h : t = r
  · subst h
    rw [derGetR_self ht]
    exact hx
  · rw [derGetR_ne h]
    exact hR r

theorem canon_evalWL (hc : c.ok = true) (hp : c.p = 3) {R : List Nat}
    (hR : ∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c R r)) {n : Nat} :
    ∀ w : Word, wordOK n w = true → CFSG.KS.Ord.Canon c.p c.d c.w (evalWL c R w)
  | [], _ => (CFSG.KS.Ord.one_sound hc).1
  | (r, e) :: w, h => by
    simp only [wordOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    exact (SecS.mul_sound c hc (powN_spec hc hp 17 e (hR r) (by omega)).1
      (canon_evalWL hc hp hR w (by simpa only [wordOK] using h.2))).1

theorem derFoldl_pow (hc : c.ok = true) (hp : c.p = 3) {R : List Nat}
    (hR : ∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c R r)) {n : Nat} :
    ∀ (w : Word) (acc : Nat), CFSG.KS.Ord.Canon c.p c.d c.w acc → wordOK n w = true →
      w.foldl (fun a q => c.mul a (powK c (getR c R q.1) q.2)) acc = c.mul acc (evalWL c R w)
  | [], acc, ha, _ => (mul_ONE_of_canon hc ha).symm
  | (r, e) :: w, acc, ha, hw => by
    simp only [wordOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    have hw' : wordOK n w = true := by simpa only [wordOK] using hw.2
    have hx : CFSG.KS.Ord.Canon c.p c.d c.w (powK c (getR c R r) e) :=
      (powN_spec hc hp 17 e (hR r) (by omega)).1
    rw [List.foldl_cons]
    change List.foldl (fun a q => c.mul a (powK c (getR c R q.1) q.2))
      (c.mul acc (powK c (getR c R r) e)) w = _
    rw [derFoldl_pow hc hp hR w _ (SecS.mul_sound c hc ha hx).1 hw',
      mul_assoc_canon hc ha hx (canon_evalWL hc hp hR w hw')]
    rfl

theorem derFoldl_congr {R R' : List Nat} :
    ∀ (w : Word), (∀ q ∈ w, getR c R q.1 = getR c R' q.1) → ∀ acc : Nat,
      w.foldl (fun a q => c.mul a (powK c (getR c R q.1) q.2)) acc =
        w.foldl (fun a q => c.mul a (powK c (getR c R' q.1) q.2)) acc
  | [], _, _ => rfl
  | q :: w, h, acc => by
    rw [List.foldl_cons, List.foldl_cons, h q List.mem_cons_self]
    exact derFoldl_congr w (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) _

theorem derRunL_cons (o : Op) (prog : List Op) (R : List Nat) :
    runL c (o :: prog) R = runL c prog (R.set (Op.tgt o) (stepV c R o)) := rfl

theorem derRunL_append (p q : List Op) (R : List Nat) : runL c (p ++ q) R = runL c q (runL c p R) := by
  unfold runL
  rw [List.foldl_append]

theorem getR_runL_of_ne : ∀ (prog : List Op) (R : List Nat) (r : Nat), (∀ o ∈ prog, Op.tgt o ≠ r) →
    getR c (runL c prog R) r = getR c R r
  | [], _, _, _ => rfl
  | o :: prog, R, r, h => by
    rw [derRunL_cons, getR_runL_of_ne prog _ r (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')),
      derGetR_ne (h o List.mem_cons_self)]

theorem runL_derLetter (hc : c.ok = true) (hp : c.p = 3) {s t : Nat} (hst : s ≠ t) (b e : Nat)
    (R : List Nat) (hR : ∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c R r)) (ht : t < R.length)
    (hs : s < R.length) (he : e < 65536) :
    getR c (runL c (derLetter s t (b, e)) R) t = c.mul (getR c R t) (powK c (getR c R b) e) ∧
      (∀ r, r ≠ t → r ≠ s → getR c (runL c (derLetter s t (b, e)) R) r = getR c R r) ∧
      (∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c (runL c (derLetter s t (b, e)) R) r)) ∧
      (runL c (derLetter s t (b, e)) R).length = R.length := by
  unfold derLetter
  cases h1 : Nat.beq e 1
  · simp only [Bool.cond_false]
    have hx := (powN_spec hc hp 17 e (hR b) (by omega)).1
    have hR1 := derCanon_set hR hs hx
    have ht1 : t < (R.set s (powK c (getR c R b) e)).length := by
      rw [List.length_set]
      exact ht
    have hrun : runL c [Op.pow e b s, Op.mul t s t] R =
        (R.set s (powK c (getR c R b) e)).set t
          (c.mul (getR c (R.set s (powK c (getR c R b) e)) t)
            (getR c (R.set s (powK c (getR c R b) e)) s)) := rfl
    rw [hrun, derGetR_ne hst, derGetR_self hs]
    refine ⟨derGetR_self ht1, fun r hrt hrs => ?_, derCanon_set hR1 ht1
      (SecS.mul_sound c hc (hR t) hx).1, by simp only [List.length_set]⟩
    rw [derGetR_ne (Ne.symm hrt), derGetR_ne (Ne.symm hrs)]
  · obtain rfl := Nat.eq_of_beq_eq_true h1
    simp only [Bool.cond_true]
    have hrun : runL c [Op.mul t b t] R = R.set t (c.mul (getR c R t) (getR c R b)) := rfl
    rw [hrun, derPowK_one]
    exact ⟨derGetR_self ht, fun r hrt _ => derGetR_ne (Ne.symm hrt),
      derCanon_set hR ht (SecS.mul_sound c hc (hR t) (hR b)).1, List.length_set⟩

theorem runL_derBlock (hc : c.ok = true) (hp : c.p = 3) {s t n : Nat} (hst : s ≠ t) :
    ∀ (w : Word) (R : List Nat), (∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c R r)) →
      t < R.length → s < R.length → (∀ q ∈ w, q.1 ≠ t ∧ q.1 ≠ s) → wordOK n w = true →
      getR c (runL c (w.flatMap (derLetter s t)) R) t =
        w.foldl (fun a q => c.mul a (powK c (getR c R q.1) q.2)) (getR c R t) ∧
      ∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c (runL c (w.flatMap (derLetter s t)) R) r)
  | [], R, hR, _, _, _, _ => ⟨rfl, hR⟩
  | (b, e) :: w, R, hR, ht, hs, hq, hok => by
    simp only [wordOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hok' : wordOK n w = true := by simpa only [wordOK] using hok.2
    obtain ⟨m1, m2, m3, m4⟩ := runL_derLetter hc hp hst b e R hR ht hs hok.1.2
    obtain ⟨h1, h2⟩ := runL_derBlock hc hp hst w _ m3 (m4 ▸ ht) (m4 ▸ hs)
      (fun q hq' => hq q (List.mem_cons_of_mem _ hq')) hok'
    rw [List.flatMap_cons, derRunL_append]
    refine ⟨?_, h2⟩
    rw [h1, m1, List.foldl_cons]
    exact derFoldl_congr w (fun q hq' => m2 q.1 (hq q (List.mem_cons_of_mem _ hq')).1
      (hq q (List.mem_cons_of_mem _ hq')).2) _

theorem runL_derOps (hc : c.ok = true) (hp : c.p = 3) {s t n a e : Nat} {w : Word}
    {R : List Nat} (hR : ∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c R r)) (ht : t < R.length)
    (hs : s < R.length) (hst : s ≠ t) (hq : ∀ q ∈ w, q.1 ≠ t ∧ q.1 ≠ s)
    (hok : wordOK n ((a, e) :: w) = true) :
    getR c (runL c (derOps s t ((a, e) :: w)) R) t = evalWL c R ((a, e) :: w) ∧
      ∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c (runL c (derOps s t ((a, e) :: w)) R) r) := by
  have hok' := hok
  simp only [wordOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hok'
  have hw : wordOK n w = true := by simpa only [wordOK] using hok'.2
  have hx : CFSG.KS.Ord.Canon c.p c.d c.w (powK c (getR c R a) e) :=
    (powN_spec hc hp 17 e (hR a) (by omega)).1
  have hR1 := derCanon_set hR ht hx
  have ht1 : t < (R.set t (powK c (getR c R a) e)).length := by
    rw [List.length_set]
    exact ht
  have hs1 : s < (R.set t (powK c (getR c R a) e)).length := by
    rw [List.length_set]
    exact hs
  obtain ⟨m1, m2⟩ := runL_derBlock hc hp hst w _ hR1 ht1 hs1 hq hw
  refine ⟨?_, m2⟩
  change getR c (runL c _ (R.set t (powK c (getR c R a) e))) t = _
  rw [m1, derGetR_self ht, derFoldl_congr w (fun q' hq' => derGetR_ne (Ne.symm (hq q' hq').1))
    _, derFoldl_pow hc hp hR w _ hx hw]
  rfl

theorem derLetter_tgt {s t : Nat} (q : Nat × Nat) :
    ∀ o ∈ derLetter s t q, Op.tgt o = t ∨ Op.tgt o = s := by
  intro o ho
  unfold derLetter at ho
  cases h : Nat.beq q.2 1 <;> rw [h] at ho <;>
    simp only [Bool.cond_true, Bool.cond_false, List.mem_cons, List.not_mem_nil, or_false] at ho
  · rcases ho with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [ho]
    exact Or.inl rfl

theorem derOps_tgt {s t : Nat} : ∀ (w : Word), ∀ o ∈ derOps s t w, Op.tgt o = t ∨ Op.tgt o = s
  | [], o, ho => absurd ho List.not_mem_nil
  | (a, e) :: w, o, ho => by
    rcases List.mem_cons.1 ho with h | h
    · rw [h]
      exact Or.inl rfl
    · obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 h
      exact derLetter_tgt q o hq

theorem derProg_tgt {s : Nat} : ∀ (ds : List Der), ∀ o ∈ derProg s ds,
    ∃ d ∈ ds, Op.tgt o = d.reg ∨ Op.tgt o = s := by
  intro ds o ho
  obtain ⟨d, hd, ho'⟩ := List.mem_flatMap.1 ho
  exact ⟨d, hd, derOps_tgt d.w o ho'⟩

theorem derChk_ne {n s : Nat} : ∀ (ds : List Der) (av : List Nat), derChk n s av ds = true →
    ∀ d ∈ ds, ∀ r ∈ av, d.reg ≠ r
  | [], _, _, d, hd => absurd hd List.not_mem_nil
  | e :: ds, av, h, d, hd => by
    simp only [derChk, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases List.mem_cons.1 hd with rfl | hd'
    · intro r hr hdr
      subst hdr
      have := h.1.1.1.1.1.2
      rw [memB_iff.2 hr] at this
      exact Bool.noConfusion this
    · intro r hr
      exact derChk_ne ds _ h.2 d hd' r (List.mem_cons_of_mem _ hr)

theorem der_eq_facts (hc : c.ok = true) (hp : c.p = 3) {n s : Nat} :
    ∀ (ds : List Der) (av : List Nat) (R : List Nat),
      (∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c R r)) → R.length = n →
      derChk n s av ds = true →
      ∀ e ∈ ds, factL c (runL c (derProg s ds) R) n (.eq [(e.reg, 1)] e.w) = true
  | [], _, _, _, _, _, e, he => absurd he List.not_mem_nil
  | ⟨d0, o0, w0⟩ :: ds, av, R, hR, hlen, h, e, he => by
    simp only [derChk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hdn, hdav⟩, hdne⟩, hok⟩, hin⟩, hsn, hsav⟩, hrest⟩ := h
    have hsav' : s ∉ d0 :: av := fun h => by
      rw [memB_iff.2 h] at hsav
      exact Bool.noConfusion hsav
    cases w0 with
    | nil => exact absurd hdne (by decide)
    | cons q w =>
    obtain ⟨a, e0⟩ := q
    have hin' := hin
    simp only [wordIn, List.all_eq_true, memB_iff] at hin'
    have hav : ∀ r ∈ av, d0 ≠ r := by
      intro r hr hdr
      subst hdr
      rw [memB_iff.2 hr] at hdav
      exact Bool.noConfusion hdav
    have hq : ∀ q ∈ w, q.1 ≠ d0 ∧ q.1 ≠ s := fun q hq =>
      ⟨(hav q.1 (hin' q (List.mem_cons_of_mem _ hq))).symm, fun h => hsav'
        (List.mem_cons_of_mem _ (h ▸ hin' q (List.mem_cons_of_mem _ hq)))⟩
    have hst : s ≠ d0 := fun h => hsav' (h ▸ List.mem_cons_self)
    obtain ⟨b1, b2⟩ := runL_derOps hc hp hR (hlen ▸ hdn) (hlen ▸ hsn) hst hq hok
    have hsplit : derProg s (⟨d0, o0, (a, e0) :: w⟩ :: ds) =
        derOps s d0 ((a, e0) :: w) ++ derProg s ds := by
      simp only [derProg, List.flatMap_cons]
    rw [hsplit, derRunL_append]
    have hlen1 : (runL c (derOps s d0 ((a, e0) :: w)) R).length = n := by
      rw [runL_length]
      exact hlen
    rcases List.mem_cons.1 he with rfl | he'
    · have hK : ∀ r ∈ d0 :: av,
          getR c (runL c (derProg s ds) (runL c (derOps s d0 ((a, e0) :: w)) R)) r
            = getR c (runL c (derOps s d0 ((a, e0) :: w)) R) r := by
        intro r hr
        refine getR_runL_of_ne _ _ r fun o ho => ?_
        obtain ⟨d', hd', hdo | hdo⟩ := derProg_tgt ds o ho
        · rw [hdo]
          exact derChk_ne ds (d0 :: av) hrest d' hd' r hr
        · rw [hdo]
          rintro rfl
          exact hsav' hr
      have hfin : factIn (d0 :: av) (.eq [(d0, 1)] ((a, e0) :: w)) = true := by
        simp only [factIn, wordIn, Bool.and_eq_true, List.all_eq_true, memB_iff]
        refine ⟨fun q hq => ?_, fun q hq => List.mem_cons_of_mem _ (hin' q hq)⟩
        rw [List.mem_singleton] at hq
        rw [hq]
        exact List.mem_cons_self
      rw [factL_congr hK n _ hfin]
      have hK' : ∀ r ∈ av, getR c R r = getR c (runL c (derOps s d0 ((a, e0) :: w)) R) r :=
        fun r hr => (getR_runL_of_ne _ _ r fun o ho => by
          rcases derOps_tgt _ o ho with hdo | hdo
          · rw [hdo]
            exact hav r hr
          · rw [hdo]
            rintro rfl
            exact hsav' (List.mem_cons_of_mem _ hr)).symm
      simp only [factL, Bool.and_eq_true]
      refine ⟨⟨?_, hok⟩, ?_⟩
      · simp only [wordOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨hdn, by norm_num⟩
      · change Nat.beq (c.mul (powK c (getR c (runL c (derOps s d0 ((a, e0) :: w)) R) d0) 1) c.ONE)
          _ = true
        rw [derPowK_one, mul_ONE_of_canon hc (b2 d0), b1, evalWL_congr hK' _ hin]
        exact Nat.beq_refl _
    · exact der_eq_facts hc hp ds (d0 :: av) _ b2 hlen1 hrest e he'

end

end CFSG.KC.OpsLayK

end
