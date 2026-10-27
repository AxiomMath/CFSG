module

public import CFSG.Certificates.Kernel.GMS78RuCzJEval
import CFSG.Certificates.Kernel.MonsterB.Co2PermSound
public import CFSG.Certificates.Kernel.GMS78RuGenCzJ

public section

namespace CFSG.KC.GMS.CzJ

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.GMS
open CFSG.ComponentClassification.GMS78.RuCz CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSporadicStandard.Fin76b.AutETable (mt ix tab ev)
open CFSG.Monster.B.Co2.Native (isInvA invCand compA idA)

variable {M : Array (Array Nat)} {inv : Array Nat} {c : ArrCert} {RW : Nat → Nat}
  {PAR LAB INV : Nat}

private theorem bang_eq_ix (t : Array Nat) (i : Nat) : t[i]! = ix t i := by
  rw [Array.getElem!_eq_getD]; rfl

private theorem ix_tab' {n a : Nat} {f : Nat → Nat} (ha : a < n) : ix (tab n f) a = f a := by
  simp [ix, tab, Array.getD, ha]

private theorem getD_map' {α β : Type} (f : α → β) (l : List α) (d : α) (n : Nat) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

private theorem czMt_lt (RW : Nat → Nat) (a b : Nat) : czMt RW a b < 2048 := fget11_lt _ _

private theorem mt_eq' (I : TabI M inv c RW PAR LAB INV) {a b : Nat} (ha : a < 2048)
    (hb : b < 2048) : mt M a b = czMt RW a b :=
  I.mt_eq a ha b hb

private theorem map_evW_lt (I : TabI M inv c RW PAR LAB INV) (t : List Nat)
    (ws : List (List Nat)) : ∀ x ∈ ws.map (evW M inv t), x < 2048 := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact evW_lt I t w

private theorem getD_map_evW (t : List Nat) (ws : List (List Nat)) (k : Nat) :
    (ws.map (evW M inv t)).getD k 0 = evW M inv t (ws.getD k []) :=
  getD_map' (evW M inv t) ws [] k

private theorem fget_czEvs (I : TabI M inv c RW PAR LAB INV) {t : List Nat}
    (ht : ∀ x ∈ t, x < 2048) (ws : List (List Nat)) (i : Nat) :
    fget (czEvs RW INV (czPack t) ws) i 11 = (ws.map (evW M inv t)).getD i 0 := by
  rw [czEvs_evW I ht, czPack_fget (map_evW_lt I t ws)]

private theorem range6_getD {f : Nat → Nat} {j : Nat} (hj : j < 6) :
    ((List.range 6).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

private theorem codesLt_spec {m : Nat} {rs : List (List Nat)} (h : czCodesLt m rs = true) :
    ∀ r ∈ rs, ∀ l ∈ r, l < m := by
  unfold czCodesLt at h
  intro r hr l hl
  exact Nat.blt_eq.mp (neAllL_iff.1 (neAllL_iff.1 h r hr) l hl)

private theorem gi_lt {LK : Nat → Nat} :
    ∀ x ∈ (List.range 6).map (fun k => fget (LK k) 0 11), x < 2048 := by
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact fget11_lt _ _

private theorem slRec_eq (RW : Nat → Nat) (INV G : Nat) (sols : List (List (List Nat))) :
    List.rec (motive := fun _ => List Nat) [] (fun s _ ih => List.cons (czEvs RW INV G s) ih)
      sols = sols.map (czEvs RW INV G) := by
  induction sols with
  | nil => rfl
  | cons s sols ih => exact congrArg (List.cons _) ih

private theorem solsG_getD (t : List Nat) (sols : List (List (List Nat))) (k : Nat) :
    (sols.map fun s => s.map (evW M inv t)).getD k [] = (sols.getD k []).map (evW M inv t) :=
  getD_map' (fun s => s.map (evW M inv t)) sols [] k

private theorem neGet_SL (I : TabI M inv c RW PAR LAB INV) {t : List Nat}
    (ht : ∀ x ∈ t, x < 2048) (sols : List (List (List Nat))) (k : Nat) :
    neGet 0 (sols.map (czEvs RW INV (czPack t))) k =
      czPack ((sols.map fun s => s.map (evW M inv t)).getD k []) := by
  rw [neGet_eq, solsG_getD, ← czEvs_evW I ht]
  exact getD_map' (czEvs RW INV (czPack t)) sols [] k

private theorem fget_SL (I : TabI M inv c RW PAR LAB INV) {t : List Nat}
    (ht : ∀ x ∈ t, x < 2048) (sols : List (List (List Nat))) (k i : Nat) :
    fget (neGet 0 (sols.map (czEvs RW INV (czPack t))) k) i 11 =
      ((sols.map fun s => s.map (evW M inv t)).getD k []).getD i 0 := by
  rw [neGet_SL I ht, solsG_getD, czPack_fget (map_evW_lt I t _)]

private theorem foldl_congr' {f g : Nat → Nat} : ∀ (w : List Nat) (acc : Nat),
    (∀ l ∈ w, f l = g l) →
      w.foldl (fun acc i => mt M acc (f i)) acc = w.foldl (fun acc i => mt M acc (g i)) acc
  | [], _, _ => rfl
  | l :: w, acc, h => by
    rw [List.foldl_cons, List.foldl_cons, h l List.mem_cons_self]
    exact foldl_congr' w _ fun l hl => h l (List.mem_cons_of_mem _ hl)

private theorem evW_congr {t t' w : List Nat}
    (h : ∀ l ∈ w, t.getD (l / 2) 0 = t'.getD (l / 2) 0) : evW M inv t w = evW M inv t' w := by
  show w.foldl (fun acc i => mt M acc (letF inv t i)) 0 =
    w.foldl (fun acc i => mt M acc (letF inv t' i)) 0
  refine foldl_congr' w 0 fun l hl => ?_
  unfold letF
  rw [h l hl]

private theorem relsHold_congr {t t' : List Nat} {rs : List (List Nat)}
    (hrs : ∀ r ∈ rs, ∀ l ∈ r, l < 12) (h : ∀ j < 6, t.getD j 0 = t'.getD j 0) :
    relsHold M inv rs t = relsHold M inv rs t' := by
  unfold relsHold
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  have e : ∀ r ∈ rs, evW M inv t r = evW M inv t' r := fun r hr =>
    evW_congr fun l hl => h _ (by have := hrs r hr l hl; omega)
  constructor
  · intro H r hr; rw [← e r hr]; exact H r hr
  · intro H r hr; rw [e r hr]; exact H r hr

private theorem homVal_congr (I : TabI M inv c RW PAR LAB INV) {t t' : List Nat}
    (h : ∀ j < 6, t.getD j 0 = t'.getD j 0) :
    ∀ (f a : Nat), a < 2048 → homVal M c t f a = homVal M c t' f a
  | 0, _, _ => rfl
  | f + 1, a, ha => by
    unfold homVal
    by_cases h0 : a = 0
    · rw [if_pos h0, if_pos h0]
    · have hp := I.par_lt a ha (Nat.pos_of_ne_zero h0)
      rw [if_neg h0, if_neg h0, I.lab_eq a ha, h _ (I.lab_lt a ha (Nat.pos_of_ne_zero h0)),
        I.par_eq a ha, homVal_congr I h f _ (by omega)]

private theorem ix_homTab_val {t : List Nat} {a : Nat} (ha : a < 2048) :
    ix (homTab 2048 M c t) a = homVal M c t 2048 a := by
  unfold homTab
  exact ix_tab' ha

private theorem c6_getD (t : List Nat) (c2J : List (List Nat)) :
    ∀ j < 6, ((List.range 6).map fun i => evW M inv t (c2J.getD i [])).getD j 0 =
      (c2J.map (evW M inv t)).getD j 0 := by
  intro j hj
  rw [range6_getD hj, getD_map_evW]

private theorem ix_gam (I : TabI M inv c RW PAR LAB INV) {t : List Nat}
    (ht : ∀ x ∈ t, x < 2048) (c2J : List (List Nat)) {a : Nat} (ha : a < 2048) :
    ix (homTab 2048 M c ((List.range 6).map fun i => evW M inv t (c2J.getD i []))) a =
      fget (czHom RW PAR LAB (czEvs RW INV (czPack t) c2J)) a 11 := by
  rw [ix_homTab_val ha, homVal_congr I (c6_getD t c2J) 2048 a ha, ← ix_homTab_val ha,
    czEvs_evW I ht, ix_homTab I (map_evW_lt I t c2J) ha]

private theorem part_norm (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    (hgi : ∀ x ∈ gi, x < 2048) {normX HT : List (List Nat)} {sols : List (List (List Nat))}
    {A : List Nat} (hA : A = HT.map (evW M inv gi))
    (h : allN 4 (fun s => allN 6 fun i =>
      Nat.beq (czMt RW (czMt RW (fget INV (czEv RW INV (czPack gi) (neGet [] normX s)) 11)
          (fget (neGet 0 (sols.map (czEvs RW INV (czPack gi))) s) i 11))
          (czEv RW INV (czPack gi) (neGet [] normX s)))
        (fget (czEvs RW INV (czPack gi) HT) i 11)) = true) :
    (List.range 4).all (fun s =>
      (List.range 6).all fun i =>
        mt M (mt M (ix inv (evW M inv gi (normX.getD s [])))
          (((sols.map fun s => s.map (evW M inv gi)).getD s []).getD i 0))
          (evW M inv gi (normX.getD s [])) == A.getD i 0) = true := by
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro s hs i hi
  have h' := Nat.eq_of_beq_eq_true (allN_iff'.1 (allN_iff'.1 h s hs) i hi)
  rw [hA, ← fget_czEvs I hgi, ← fget_SL I hgi, ← neGet_eq, evW_eq I hgi,
    I.inv_eq _ (czEv_lt _ _ _ _), mt_eq' I (fget11_lt _ _) (fget11_lt _ _),
    mt_eq' I (czMt_lt _ _ _) (czEv_lt _ _ _ _)]
  exact h'

private theorem part_gamma_rels (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    (hgi : ∀ x ∈ gi, x < 2048) {relsJ c2J : List (List Nat)} (hc : czCodesLt 12 relsJ = true)
    (h : czRels RW INV (czEvs RW INV (czPack gi) c2J) relsJ = true) :
    relsHold M inv relsJ ((List.range 6).map fun i => evW M inv gi (c2J.getD i [])) = true := by
  rw [czEvs_evW I hgi, ← relsHold_eq I (map_evW_lt I gi c2J)] at h
  rw [relsHold_congr (codesLt_spec hc) (c6_getD gi c2J)]
  exact h

private theorem part_gamma_conj (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    (hgi : ∀ x ∈ gi, x < 2048) {c2J : List (List Nat)} {sols : List (List (List Nat))}
    {cls : List Nat}
    (h : allN 4 (fun s => andB (Nat.blt (neGet 0 cls s) 4) (allN 6 fun i =>
        Nat.beq (fget (czHom RW PAR LAB (neGet 0 (sols.map (czEvs RW INV (czPack gi))) (s + 4)))
            (fget (czHom RW PAR LAB (czEvs RW INV (czPack gi) c2J)) (fget (czPack gi) i 11) 11)
            11)
          (fget (czHom RW PAR LAB (czEvs RW INV (czPack gi) c2J))
            (fget (neGet 0 (sols.map (czEvs RW INV (czPack gi))) (neGet 0 cls s)) i 11) 11)))
      = true) :
    (List.range 4).all (fun s =>
      decide (cls.getD s 0 < 4) && (List.range 6).all fun i =>
        ix (homTab 2048 M c ((sols.map fun s => s.map (evW M inv gi)).getD (s + 4) []))
            (ix (homTab 2048 M c ((List.range 6).map fun i => evW M inv gi (c2J.getD i [])))
              (gi.getD i 0)) ==
          ix (homTab 2048 M c ((List.range 6).map fun i => evW M inv gi (c2J.getD i [])))
            (((sols.map fun s => s.map (evW M inv gi)).getD (cls.getD s 0) []).getD i 0))
      = true := by
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  intro s hs
  obtain ⟨h1, h2⟩ := andB_iff.1 (allN_iff'.1 h s hs)
  refine ⟨by rw [← neGet_eq]; exact Nat.blt_eq.mp h1, fun i hi => ?_⟩
  have h' := Nat.eq_of_beq_eq_true (allN_iff'.1 h2 i hi)
  have hs' : ∀ x ∈ (sols.map fun s => s.map (evW M inv gi)).getD (s + 4) [], x < 2048 := by
    rw [solsG_getD]; exact map_evW_lt I gi _
  rw [← czPack_fget hgi, ← neGet_eq 0 cls s, ← fget_SL I hgi, ix_gam I hgi c2J (fget11_lt _ _),
    ix_gam I hgi c2J (fget11_lt _ _), ix_homTab I hs' (fget11_lt _ _), ← neGet_SL I hgi]
  exact h'

private theorem part_inj {K : Array (Array Nat)} {KS : List Nat}
    (hK : ∀ j < 4, ∀ a < 2048, ix (K.getD j #[]) a = fget (neGet 0 KS j) a 11)
    (hinj : ∀ j < 4, czInj (neGet 0 KS j) = true) :
    (List.range 4).all (fun j => isInvA 2048 (K.getD j #[]) (invCand 2048 (K.getD j #[])))
      = true := by
  simp only [List.all_eq_true, List.mem_range]
  intro j hj
  apply CFSG.KC.Co2Mem.isInvA_invCand
  · intro i hi
    rw [bang_eq_ix, hK j hj i hi]
    exact fget11_lt _ _
  · intro i i' hi hi' e
    rw [bang_eq_ix, bang_eq_ix, hK j hj i hi, hK j hj i' hi'] at e
    exact czInj_spec (hinj j hj) i hi i' hi' e

private theorem invCand_eq {t : Array Nat} {X : Nat} (hX : czInj X = true)
    (ht : ∀ i < 2048, ix t i = fget X i 11) {a : Nat} (ha : a < 2048) :
    ix (invCand 2048 t) a = fget (czInvT X) a 11 := by
  let f : Fin 2048 → Fin 2048 := fun i => ⟨fget X i 11, fget11_lt _ _⟩
  have finj : Function.Injective f := fun i i' e =>
    Fin.ext (czInj_spec hX i i.2 i' i'.2 (congrArg Fin.val e))
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective finj ⟨a, ha⟩
  have e : a = fget X i 11 := (congrArg Fin.val hi).symm
  subst e
  have hb : ∀ k < 2048, t[k]! < 2048 := fun k hk => by
    rw [bang_eq_ix, ht k hk]; exact fget11_lt _ _
  have hi' : ∀ k k', k < 2048 → k' < 2048 → t[k]! = t[k']! → k = k' := fun k k' hk hk' e => by
    rw [bang_eq_ix, bang_eq_ix, ht k hk, ht k' hk'] at e
    exact czInj_spec hX k hk k' hk' e
  rw [czInvT_fget hX i i.2, ← ht i i.2, ← bang_eq_ix, ← bang_eq_ix]
  exact CFSG.KC.Co2Mem.invCand_spec hb hi' i i.2

private theorem czLetterAt_lt (RW : Nat → Nat) (INV G : Nat) (KS KI : List Nat) (l a : Nat) :
    czLetterAt RW INV G KS KI l a < 2048 := by
  unfold czLetterAt
  cases Nat.blt l 12 <;> cases Nat.beq (l % 2) 0 <;> exact fget11_lt _ _

private theorem letter_eq (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    (hgi : ∀ x ∈ gi, x < 2048) {K : Array (Array Nat)} {KS KI : List Nat}
    (hK : ∀ j < 4, ∀ a < 2048, ix (K.getD j #[]) a = fget (neGet 0 KS j) a 11)
    (hinj : ∀ j < 4, czInj (neGet 0 KS j) = true)
    (hKI : ∀ j < 4, neGet 0 KI j = czInvT (neGet 0 KS j)) {l a : Nat} (hl : l < 20)
    (ha : a < 2048) :
    (letterTab 2048 M inv gi K l)[a]! = czLetterAt RW INV (czPack gi) KS KI l a := by
  rw [bang_eq_ix]
  by_cases h12 : l < 12
  · have e1 : letterTab 2048 M inv gi K l =
        tab 2048 (fun a => mt M (mt M (ix inv (letF inv gi l)) a) (letF inv gi l)) := by
      unfold letterTab; rw [if_pos h12]; rfl
    have e2 : czLetterAt RW INV (czPack gi) KS KI l a = czMt RW (czMt RW
        (fget INV (czLet INV (czPack gi) l) 11) a) (czLet INV (czPack gi) l) := by
      unfold czLetterAt; rw [Nat.blt_eq.mpr h12]
    rw [e1, e2, ix_tab' ha, ← letF_eq I hgi, I.inv_eq _ (letF_lt I hgi l),
      mt_eq' I (fget11_lt _ _) ha, mt_eq' I (czMt_lt _ _ _) (letF_lt I hgi l)]
  · have hj : l / 2 - 6 < 4 := by omega
    have hb : Nat.blt l 12 = false := by
      cases e : Nat.blt l 12
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h12
    by_cases h2 : l % 2 = 0
    · have e1 : letterTab 2048 M inv gi K l = K.getD (l / 2 - 6) #[] := by
        unfold letterTab; rw [if_neg h12, if_pos h2]
      have e2 : czLetterAt RW INV (czPack gi) KS KI l a =
          fget (neGet 0 KS (l / 2 - 6)) a 11 := by
        have hb2 : Nat.beq (Nat.mod l 2) 0 = true := Nat.beq_eq.mpr h2
        unfold czLetterAt; rw [hb, hb2]; try rfl
      rw [e1, e2, hK _ hj a ha]
    · have e1 : letterTab 2048 M inv gi K l = invCand 2048 (K.getD (l / 2 - 6) #[]) := by
        unfold letterTab; rw [if_neg h12, if_neg h2]
      have hb2 : Nat.beq (Nat.mod l 2) 0 = false := by
        cases e : Nat.beq (Nat.mod l 2) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) h2
      have e2 : czLetterAt RW INV (czPack gi) KS KI l a =
          fget (neGet 0 KI (l / 2 - 6)) a 11 := by
        unfold czLetterAt; rw [hb, hb2]; try rfl
      rw [e1, e2, hKI _ hj]
      exact invCand_eq (hinj _ hj) (hK _ hj) ha

private noncomputable def kFold (RW : Nat → Nat) (INV G : Nat) (KS KI : List Nat) (r : List Nat)
    (T : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun T => T)
    (fun l _ ih T => strictN (czTab fun i => czLetterAt RW INV G KS KI l (fget T i 11)) ih) r T

private theorem kFold_cons (RW : Nat → Nat) (INV G : Nat) (KS KI : List Nat) (l : Nat)
    (r : List Nat) (T : Nat) :
    kFold RW INV G KS KI (l :: r) T =
      kFold RW INV G KS KI r (czTab fun i => czLetterAt RW INV G KS KI l (fget T i 11)) :=
  strictN_eq' (czTab fun i => czLetterAt RW INV G KS KI l (fget T i 11)) (kFold RW INV G KS KI r)

private theorem compA_get (t u : Array Nat) {p : Nat} (hp : p < 2048) :
    (compA 2048 t u)[p]! = t[u[p]!]! := by
  unfold compA
  rw [getElem!_pos _ p (by rw [Array.size_ofFn]; exact hp), Array.getElem_ofFn]

private theorem fold_eq {gi : List Nat} {K : Array (Array Nat)} {KS KI : List Nat}
    (hlet : ∀ l < 20, ∀ a < 2048,
      (letterTab 2048 M inv gi K l)[a]! = czLetterAt RW INV (czPack gi) KS KI l a) :
    ∀ (r : List Nat) (T : Array Nat) (T' : Nat), (∀ l ∈ r, l < 20) →
      (∀ i < 2048, T[i]! = fget T' i 11) →
      ∀ i < 2048, (r.foldl (fun T l => compA 2048 (letterTab 2048 M inv gi K l) T) T)[i]! =
        fget (kFold RW INV (czPack gi) KS KI r T') i 11
  | [], _, _, _, h => h
  | l :: r, T, T', hr, h => by
    rw [List.foldl_cons, kFold_cons]
    refine fold_eq hlet r _ _ (fun l' hl' => hr l' (List.mem_cons_of_mem _ hl')) ?_
    intro i hi
    rw [compA_get _ _ hi, h i hi, hlet l (hr l List.mem_cons_self) _ (fget11_lt _ _),
      czTab_fget (fun j _ => czLetterAt_lt _ _ _ _ _ _ _) hi]

private theorem idA_get {p : Nat} (hp : p < 2048) : (idA 2048)[p]! = p := by
  unfold idA
  rw [getElem!_pos _ p (by rw [Array.size_ofFn]; exact hp), Array.getElem_ofFn]

private theorem part_sign (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    (hgi : ∀ x ∈ gi, x < 2048) {K : Array (Array Nat)} {KS KI : List Nat}
    {HR : List (List Nat)} (hc : czCodesLt 20 HR = true)
    (hK : ∀ j < 4, ∀ a < 2048, ix (K.getD j #[]) a = fget (neGet 0 KS j) a 11)
    (hinj : ∀ j < 4, czInj (neGet 0 KS j) = true)
    (hKI : ∀ j < 4, neGet 0 KI j = czInvT (neGet 0 KS j))
    (h : neAllL (fun r => neAllL (fun g => Nat.beq (fget (kFold RW INV (czPack gi) KS KI r
      (czTab fun i => i)) g 11) g) gi) HR = true) :
    HR.all (fun r =>
      gi.all fun g =>
        ix (r.foldl (fun T l => compA 2048 (letterTab 2048 M inv gi K l) T) (idA 2048)) g == g)
      = true := by
  have hlet : ∀ l < 20, ∀ a < 2048,
      (letterTab 2048 M inv gi K l)[a]! = czLetterAt RW INV (czPack gi) KS KI l a :=
    fun l hl a ha => letter_eq I hgi hK hinj hKI hl ha
  have hcs := codesLt_spec hc
  simp only [List.all_eq_true, beq_iff_eq]
  intro r hr g hg
  have h' := Nat.eq_of_beq_eq_true (neAllL_iff.1 (neAllL_iff.1 h r hr) g hg)
  rw [← bang_eq_ix, fold_eq hlet r _ (czTab fun i => i) (hcs r hr)
    (fun i hi => by rw [idA_get hi, czTab_fget (fun j hj => hj) hi]) g (hgi g hg)]
  exact h'

private theorem part_centre (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    (hgi : ∀ x ∈ gi, x < 2048)
    (h : czListEq (czFilter fun a => neAllL (fun g => Nat.beq (czMt RW a g) (czMt RW g a)) gi)
      [0, czEv RW INV (czPack gi) [0, 0]] = true) :
    ((List.range 2048).filter (fun a => gi.all fun g => mt M a g == mt M g a) ==
      [0, evW M inv gi [0, 0]]) = true := by
  rw [czListEq_iff, czFilter_eq, ← evW_eq I hgi] at h
  rw [beq_iff_eq, ← h]
  apply List.filter_congr
  intro a ha
  have ha' : a < 2048 := List.mem_range.1 ha
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, neAllL_iff]
  refine forall_congr' fun g => imp_congr_right fun hg => ?_
  rw [mt_eq' I ha' (hgi g hg), mt_eq' I (hgi g hg) ha', beq_iff_eq, Nat.beq_eq]

theorem czJ_relsHold (I : TabI M inv c RW PAR LAB INV) {LK : Nat → Nat} {gi : List Nat}
    (hgi : gi = (List.range 6).map fun k => fget (LK k) 0 11)
    {relsJ Wq Wv Ww normX c2J HT HR : List (List Nat)} {sols : List (List (List Nat))}
    {cls : List Nat}
    (hId : kIdent RW PAR LAB INV ((List.range 6).map fun k => fget (LK k) 0 11) relsJ Wq Wv Ww
      normX c2J HT HR sols cls = true) :
    relsHold M inv relsJ gi = true := by
  have hl : ∀ x ∈ gi, x < 2048 := hgi ▸ gi_lt
  rw [← hgi] at hId
  simp only [kIdent, andB_iff] at hId
  rw [relsHold_eq I hl]
  exact hId.2.2.2.2.1

private theorem getD4_0 {α : Type} (a b c d e : α) : (#[a, b, c, d] : Array α).getD 0 e = a := rfl
private theorem getD4_1 {α : Type} (a b c d e : α) : (#[a, b, c, d] : Array α).getD 1 e = b := rfl
private theorem getD4_2 {α : Type} (a b c d e : α) : (#[a, b, c, d] : Array α).getD 2 e = c := rfl
private theorem getD4_3 {α : Type} (a b c d e : α) : (#[a, b, c, d] : Array α).getD 3 e = d := rfl
private theorem neGet4_0 (a b c d e : Nat) : neGet e [a, b, c, d] 0 = a := rfl
private theorem neGet4_1 (a b c d e : Nat) : neGet e [a, b, c, d] 1 = b := rfl
private theorem neGet4_2 (a b c d e : Nat) : neGet e [a, b, c, d] 2 = c := rfl
private theorem neGet4_3 (a b c d e : Nat) : neGet e [a, b, c, d] 3 = d := rfl

private theorem kI_spec (k1 k2 k3 k4 : Nat) : ∀ j < 4,
    neGet 0 (List.rec (motive := fun _ => List Nat) [] (fun K _ ih => List.cons (czInvT K) ih)
      [k1, k2, k3, k4]) j = czInvT (neGet 0 [k1, k2, k3, k4] j) := by
  have e : List.rec (motive := fun _ => List Nat) [] (fun K _ ih => List.cons (czInvT K) ih)
      [k1, k2, k3, k4] = [czInvT k1, czInvT k2, czInvT k3, czInvT k4] := rfl
  intro j hj
  rw [e]
  match j, hj with
  | 0, _ => rw [neGet4_0, neGet4_0]
  | 1, _ => rw [neGet4_1, neGet4_1]
  | 2, _ => rw [neGet4_2, neGet4_2]
  | 3, _ => rw [neGet4_3, neGet4_3]

private theorem K_spec (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    (hgi : ∀ x ∈ gi, x < 2048) (Wq Wv Ww HT : List (List Nat)) :
    ∀ j < 4, ∀ a < 2048,
      ix ((#[homTab 2048 M c (Wq.map (evW M inv gi)), homTab 2048 M c (Wv.map (evW M inv gi)),
        homTab 2048 M c (Ww.map (evW M inv gi)), homTab 2048 M c (HT.map (evW M inv gi))] :
          Array (Array Nat)).getD j #[]) a =
      fget (neGet 0 [czHom RW PAR LAB (czEvs RW INV (czPack gi) Wq),
        czHom RW PAR LAB (czEvs RW INV (czPack gi) Wv),
        czHom RW PAR LAB (czEvs RW INV (czPack gi) Ww),
        czHom RW PAR LAB (czEvs RW INV (czPack gi) HT)] j) a 11 := by
  intro j hj a ha
  have key : ∀ ws : List (List Nat), ix (homTab 2048 M c (ws.map (evW M inv gi))) a =
      fget (czHom RW PAR LAB (czEvs RW INV (czPack gi) ws)) a 11 := fun ws => by
    rw [czEvs_evW I hgi, ix_homTab I (map_evW_lt I gi ws) ha]
  match j, hj with
  | 0, _ => rw [getD4_0, neGet4_0]; exact key Wq
  | 1, _ => rw [getD4_1, neGet4_1]; exact key Wv
  | 2, _ => rw [getD4_2, neGet4_2]; exact key Ww
  | 3, _ => rw [getD4_3, neGet4_3]; exact key HT

theorem czJ_ident (I : TabI M inv c RW PAR LAB INV) {LK : Nat → Nat} {gi : List Nat}
    (hgi : gi = (List.range 6).map fun k => fget (LK k) 0 11)
    {relsJ Wq Wv Ww normX hCodes c2J HT HR : List (List Nat)} {sols : List (List (List Nat))}
    {cls : List Nat}
    (hHT : HT = (List.range 6).map fun i => invCodes ((hCodes.getD i []).drop 3))
    (hHR : HR = hCodes.drop 7)
    (hId : kIdent RW PAR LAB INV ((List.range 6).map fun k => fget (LK k) 0 11) relsJ Wq Wv Ww
      normX c2J HT HR sols cls = true) :
    Gen.identSearchG relsJ Wq Wv Ww sols normX hCodes c2J cls 2048 M inv c gi = true := by
  have hl : ∀ x ∈ gi, x < 2048 := hgi ▸ gi_lt
  rw [← hgi] at hId
  subst hHR
  have hA : (List.range 6).map (fun i => evW M inv gi (invCodes ((hCodes.getD i []).drop 3))) =
      HT.map (evW M inv gi) := by
    rw [hHT, List.map_map]; rfl
  simp only [kIdent, andB_iff, slRec_eq] at hId
  obtain ⟨hc12, hc20, -, -, -, h1, h2, h3, h4, h5, h6⟩ := hId
  have hK := K_spec (c := c) I hl Wq Wv Ww HT
  have hinj : ∀ j < 4, czInj (neGet 0 [czHom RW PAR LAB (czEvs RW INV (czPack gi) Wq),
      czHom RW PAR LAB (czEvs RW INV (czPack gi) Wv),
      czHom RW PAR LAB (czEvs RW INV (czPack gi) Ww),
      czHom RW PAR LAB (czEvs RW INV (czPack gi) HT)] j) = true := by
    intro j hj
    rw [neGet_eq]
    refine neAllL_iff.1 h4 _ ?_
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    exact List.getElem_mem _
  unfold Gen.identSearchG
  rw [hA]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨part_norm I hl rfl h1, part_gamma_rels I hl hc12 h2⟩, part_gamma_conj I hl h3⟩,
    part_inj hK hinj⟩, part_sign I hl hc20 hK hinj (kI_spec _ _ _ _) h5⟩, part_centre I hl h6⟩

end CFSG.KC.GMS.CzJ

end
