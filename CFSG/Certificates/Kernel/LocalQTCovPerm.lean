module

public import Certificates.Data.Kernel.LocalQT.Cov
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck
public import CFSG.Certificates.Kernel.LocalQTPermSound
import CFSG.Certificates.Kernel.LocalQTTab2KSound
import CFSG.Certificates.Kernel.LocalQTBaseWProved
import CFSG.Monster.B.Co2.IsInvA

public section

namespace CFSG.KC.LQT.Cov.Perm

open Equiv CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.M22Cover CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native (compA eqA idA invCand isInvA allLt)
open CFSG.Sporadic.Mathieu (m22gA m22gB)

theorem sgetK_eq {α : Type} : ∀ (l : List α) (i : Nat) (d : α),
    CFSG.KC.LQT.Syl.getK l i d = l.getD i d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, d => by
    change CFSG.KC.LQT.Syl.getK l i d = _
    rw [sgetK_eq l i d]
    rfl

theorem slenK_eq {α : Type} : ∀ l : List α, CFSG.KC.LQT.Syl.lenK l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (slenK_eq l)

theorem allT_iff {α : Type} (l : List α) (f : α → Bool) :
    CFSG.KC.LQT.T2.allT l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [CFSG.KC.LQT.T2.allT]
  | cons x l ih =>
    change CFSG.KC.Ord.andB (f x) (CFSG.KC.LQT.T2.allT l f) = true ↔ _
    rw [CFSG.KC.LQT.BW.Pf.andB_eq, Bool.and_eq_true, ih]
    simp

theorem allLtK_iff (m : Nat) (f : Nat → Bool) : allLtK m f = true ↔ ∀ i < m, f i = true := by
  rw [allLtK, P.allL_iff]
  simp [List.mem_range]

private theorem code_gen22 (l : Nat) {cA cB : Nat} (hA : P.code m22gA = cA)
    (hB : P.code m22gB = cB) :
    (Bool.rec (motive := fun _ => Nat) cB cA (Nat.beq l 0) : Nat) = P.code (gen22 l) := by
  unfold gen22
  by_cases hl : l = 0
  · subst hl
    exact hA.symm
  · have : Nat.beq l 0 = false := by
      cases h : Nat.beq l 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hl
    rw [this, if_neg hl]
    exact hB.symm

private theorem wP_go {cA cB : Nat} (hA : P.code m22gA = cA) (hB : P.code m22gB = cB) :
    ∀ (w : List Nat) (σ : Perm (Fin 22)),
      (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
        (fun l _ ih acc => ih (P.mul 22 acc (Bool.rec (motive := fun _ => Nat) cB cA
          (Nat.beq l 0)))) w (P.code σ) : Nat) = P.code (σ * wordP w)
  | [], σ => by simp [wordP]
  | l :: w, σ => by
    change (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
        (fun l _ ih acc => ih (P.mul 22 acc (Bool.rec (motive := fun _ => Nat) cB cA
          (Nat.beq l 0)))) w
        (P.mul 22 (P.code σ) (Bool.rec (motive := fun _ => Nat) cB cA (Nat.beq l 0))) : Nat) = _
    rw [code_gen22 l hA hB, P.code_mul (by omega), wP_go hA hB w]
    simp [wordP, mul_assoc]

theorem wP_code {cA cB : Nat} (hA : P.code m22gA = cA) (hB : P.code m22gB = cB) (w : List Nat) :
    wP 22 cA cB w = P.code (wordP w) := by
  have h := wP_go hA hB w 1
  rw [one_mul, ← P.code_one] at h
  exact h

variable {D : CD} {d : CovData}

theorem genX_code {cA cB : Nat} (hA : P.code m22gA = cA) (hB : P.code m22gB = cB)
    (hxw : D.xw.length = 3) (hx0 : d.xw0 = D.xw.getD 0 []) (hx1 : d.xw1 = D.xw.getD 1 [])
    (hx2 : d.xw2 = D.xw.getD 2 []) (i : Nat) :
    CFSG.KC.LQT.Syl.getK (D.xw.map (wP 22 cA cB)) (i % 3) (P.one 22) = P.code (d.x (fo i)) := by
  have hi : i % 3 < 3 := Nat.mod_lt _ (by omega)
  rw [sgetK_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some, wP_code hA hB]
  unfold CovData.x CovData.xwOf fo
  simp only
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
  · simp only [h, ↓reduceIte, hx0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by omega : 0 < D.xw.length), Option.getD_some]
  · simp only [h, Nat.one_ne_zero, ↓reduceIte, hx1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : 1 < D.xw.length), Option.getD_some]
  · simp only [h, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, hx2,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 2 < D.xw.length),
      Option.getD_some]

private theorem elK_go {X : List Nat} (hX : ∀ l : Nat,
      CFSG.KC.LQT.Syl.getK X (l % 3) (P.one 22) = P.code (d.x (fo l))) :
    ∀ (w : List Nat) (σ : Perm (Fin 22)),
      (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
        (fun l _ ih acc => ih (P.mul 22 acc (CFSG.KC.LQT.Syl.getK X (Nat.mod l 3) (P.one 22))))
        w (P.code σ) : Nat) = P.code (σ * (w.map fun l => d.x (fo l)).prod)
  | [], σ => by simp
  | l :: w, σ => by
    change (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
        (fun l _ ih acc => ih (P.mul 22 acc (CFSG.KC.LQT.Syl.getK X (Nat.mod l 3) (P.one 22))))
        w (P.mul 22 (P.code σ) (CFSG.KC.LQT.Syl.getK X (Nat.mod l 3) (P.one 22))) : Nat) = _
    rw [show Nat.mod l 3 = l % 3 from rfl, hX l, P.code_mul (by omega), elK_go hX w]
    simp [mul_assoc]

private theorem elK_code {X : List Nat} (hX : ∀ l : Nat,
      CFSG.KC.LQT.Syl.getK X (l % 3) (P.one 22) = P.code (d.x (fo l))) (w : List Nat) :
    elK 22 X w = P.code ((w.map fun l => d.x (fo l)).prod) := by
  have h := elK_go hX w 1
  rw [one_mul, ← P.code_one] at h
  exact h

private theorem el_eq (hwd : d.words = D.words.toArray) (v : Nat) :
    d.tab.el d.x v = ((D.words.getD v []).map fun l => d.x (fo l)).prod := by
  simp only [CayTab.el, CovData.tab, hwd, List.map_map]
  congr 2
  rw [List.getElem!_toArray, List.getD_eq_getElem?_getD]
  first
    | exact getElem!_def _ _
    | simp [getElem!_def]
    | (cases h : D.words[v]? <;> simp_all [getElem!_neg, getElem!_pos])

theorem arr_get (l : List Nat) (i : Nat) : (l.toArray)[i]! = l.getD i 0 := by
  rw [CFSG.KC.LQT.BW.Pf.arr_getN, List.toList_toArray]

theorem getD_dflt {l : List Nat} {i m : Nat} (h : l.getD i m < m) :
    i < l.length ∧ l.getD i 0 = l.getD i m := by
  by_cases hi : i < l.length
  · refine ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
    simp at h

theorem goodK_sound {cA cB : Nat} (hA : P.code m22gA = cA) (hB : P.code m22gB = cB)
    (hxw : D.xw.length = 3) (hx0 : d.xw0 = D.xw.getD 0 []) (hx1 : d.xw1 = D.xw.getD 1 [])
    (hx2 : d.xw2 = D.xw.getD 2 []) (hnV : d.nV = D.nV) (hwd : d.words = D.words.toArray)
    (htg : d.tgtA = D.tgt.toArray) (hbk : d.backA = D.back.toArray)
    (h : goodK 22 D (D.xw.map (wP 22 cA cB))
      (D.words.map (elK 22 (D.xw.map (wP 22 cA cB)))) = true) :
    goodCheck d d.elaTab = true := by
  set X := D.xw.map (wP 22 cA cB) with hXdef
  set E := D.words.map (elK 22 X) with hEdef
  have hX : ∀ l : Nat, CFSG.KC.LQT.Syl.getK X (l % 3) (P.one 22) = P.code (d.x (fo l)) :=
    genX_code hA hB hxw hx0 hx1 hx2
  rw [goodK] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨h0, hw0, hmain, hlen, hdist⟩ := h
  rw [Nat.blt_eq] at h0
  rw [Nat.beq_eq, slenK_eq, hEdef, List.length_map] at hlen
  have hE : ∀ v < D.nV, CFSG.KC.LQT.Syl.getK E v 0 = P.code (d.tab.el d.x v) := by
    intro v hv
    rw [sgetK_eq, hEdef, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some, elK_code hX,
      el_eq hwd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
  have hnd : E.Nodup := CFSG.KC.LQT.T2.nodup_of_distinctS hdist
  have hx : ∀ i, CFSG.Monster.B.Co2.Rep 22 (d.xa i) (d.x i) := fun i => d.xa_rep i
  have hrep : ∀ {v : ℕ}, v < D.nV → CFSG.Monster.B.Co2.Rep 22 (d.elaTab[v]!) (d.tab.el d.x v) :=
    fun hv => d.rep_el hx (by rw [hnV]; exact hv)
  rw [allLtK_iff] at hmain
  rw [goodCheck]
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff, hnV]
  refine ⟨⟨⟨h0, ?_⟩, fun v hv i hi => ?_⟩, fun u hu v hv => ?_⟩
  · rw [Nat.beq_eq, slenK_eq, sgetK_eq] at hw0
    have hne : D.words ≠ [] := by
      intro e
      rw [e] at hw0
      simp at hw0
    rw [hwd, beq_iff_eq, List.getElem!_toArray]
    obtain ⟨w, ws, e⟩ := List.exists_cons_of_ne_nil hne
    rw [e] at hw0 ⊢
    simpa using hw0
  · have hm := (allLtK_iff _ _).1 (hmain v hv) i hi
    simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true,
      Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, sgetK_eq, Nat.add_eq, Nat.mul_eq] at hm
    obtain ⟨ht, hb, he, hbt⟩ := hm
    obtain ⟨ht', htd⟩ := getD_dflt ht
    obtain ⟨hb', hbd⟩ := getD_dflt hb
    have htg' : d.tgtA[3 * v + i]! = D.tgt.getD (3 * v + i) D.nV := by rw [htg, arr_get, htd]
    have hbk' : d.backA[3 * v + i]! = D.back.getD (3 * v + i) D.nV := by rw [hbk, arr_get, hbd]
    have hlt : D.tgt.getD (3 * v + i) D.nV < D.nV := ht
    refine ⟨⟨⟨by rw [htg']; exact ht, by rw [hbk']; exact hb⟩, ?_⟩, ?_⟩
    · rw [htg']
      have hfo : fo i = fo i := rfl
      rw [eqA_iff (hrep hlt) (rep_compA (hrep hv) (hx (fo i)))]
      have hi3 : i % 3 = i := Nat.mod_eq_of_lt hi
      have e1 : E.getD (D.tgt.getD (3 * v + i) 0) 0 =
          P.code (d.tab.el d.x (D.tgt.getD (3 * v + i) D.nV)) := by
        rw [htd, ← sgetK_eq]
        exact hE _ hlt
      have e2 : E.getD v 0 = P.code (d.tab.el d.x v) := by
        rw [← sgetK_eq]
        exact hE v hv
      have e3 : X.getD i (P.one 22) = P.code (d.x (fo i)) := by
        rw [← sgetK_eq, ← hX i, hi3]
      rw [e1, e2, e3, P.code_mul (by omega)] at he
      exact P.code_inj (by omega) he
    · rw [beq_iff_eq, htg, hbk, arr_get, arr_get]
      exact hbt
  · by_cases huv : u < v
    · simp only [huv, decide_true, Bool.not_true, Bool.false_or, Bool.not_eq_true']
      cases he : eqA 22 d.elaTab[u]! d.elaTab[v]!
      · rfl
      · exfalso
        have e := eq_of_eqA (hrep hu) (hrep hv) he
        have : CFSG.KC.LQT.Syl.getK E u 0 = CFSG.KC.LQT.Syl.getK E v 0 := by
          rw [hE u hu, hE v hv, e]
        rw [sgetK_eq, sgetK_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [hEdef, List.length_map]; omega),
          List.getElem?_eq_getElem (by rw [hEdef, List.length_map]; omega)] at this
        have := (List.Nodup.getElem_inj_iff hnd).1 this
        omega
    · simp [huv]

theorem list_get (l : List Nat) (j : Nat) : l[j]! = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD]
  first
    | exact getElem!_def _ _
    | simp [getElem!_def]
    | (cases h : l[j]? <;> simp_all [getElem!_neg, getElem!_pos])

private theorem invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand {n : ℕ} {t : Array ℕ} {g : Perm (Fin n)}
    (ht : CFSG.Monster.B.Co2.Rep n t g) : CFSG.Monster.B.Co2.Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem isInvA_of_rep {n : ℕ} {t r : Array ℕ} {g : Perm (Fin n)}
    (ht : CFSG.Monster.B.Co2.Rep n t g) (hr : CFSG.Monster.B.Co2.Rep n r g⁻¹) :
    isInvA n t r = true := by
  rw [isInvA_iff]
  intro i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨ht.lt hi, ?_⟩
  rw [ht.apply hi, hr.apply (g ⟨i, hi⟩).2]
  simp

theorem codes_E {cA cB : Nat} (hA : P.code m22gA = cA) (hB : P.code m22gB = cB)
    (hxw : D.xw.length = 3) (hx0 : d.xw0 = D.xw.getD 0 []) (hx1 : d.xw1 = D.xw.getD 1 [])
    (hx2 : d.xw2 = D.xw.getD 2 []) (hwd : d.words = D.words.toArray)
    (hlen : D.words.length = D.nV) :
    ∀ v < D.nV, (D.words.map (elK 22 (D.xw.map (wP 22 cA cB)))).getD v 0 =
      P.code (d.tab.el d.x v) := by
  intro v hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega),
    Option.map_some, Option.getD_some, elK_code (genX_code hA hB hxw hx0 hx1 hx2), el_eq hwd,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem blkK_sound {cA cB : Nat} (hA : P.code m22gA = cA) (hB : P.code m22gB = cB)
    (hxw : D.xw.length = 3) (hx0 : d.xw0 = D.xw.getD 0 []) (hx1 : d.xw1 = D.xw.getD 1 [])
    (hx2 : d.xw2 = D.xw.getD 2 []) (hnV : d.nV = D.nV) (hwd : d.words = D.words.toArray)
    (hlen : D.words.length = D.nV)
    (b : List Nat × List Nat × List Nat × List (List (Nat × Bool)))
    (h : blkK 22 cA cB D (D.words.map (elK 22 (D.xw.map (wP 22 cA cB)))) b = true) :
    blkCheck d d.elaTab ⟨b.1, b.2.1, b.2.2.1, b.2.2.2⟩ = true := by
  have hE := codes_E hA hB hxw hx0 hx1 hx2 hwd hlen
  have hx : ∀ i, CFSG.Monster.B.Co2.Rep 22 (d.xa i) (d.x i) := fun i => d.xa_rep i
  have hrep : ∀ {v : ℕ}, v < D.nV → CFSG.Monster.B.Co2.Rep 22 (d.elaTab[v]!) (d.tab.el d.x v) :=
    fun hv => d.rep_el hx (by rw [hnV]; exact hv)
  rw [blkK, P.letB_eq, P.letB_eq] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true,
    Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, slenK_eq] at h
  obtain ⟨hl, h32, hall⟩ := h
  rw [allLtK_iff] at hall
  have hGa : CFSG.Monster.B.Co2.Rep 22 (wordArrP b.1) (wordP b.1) := rep_wordArrP b.1
  have hGi : CFSG.Monster.B.Co2.Rep 22 (invCand 22 (wordArrP b.1)) (wordP b.1)⁻¹ :=
    rep_invCand hGa
  rw [blkCheck]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨isInvA_of_rep hGa hGi, hl⟩, h32⟩, fun j hj => ?_⟩
  have hm := hall j hj
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true,
    Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, sgetK_eq] at hm
  obtain ⟨ha, hb, he⟩ := hm
  obtain ⟨-, had⟩ := getD_dflt ha
  obtain ⟨-, hbd⟩ := getD_dflt hb
  have hva : b.2.1[j]! = b.2.1.getD j D.nV := by rw [list_get, had]
  have hvb : b.2.2.1[j]! = b.2.2.1.getD j D.nV := by rw [list_get, hbd]
  refine ⟨⟨by rw [hnV, hva]; exact ha, by rw [hnV, hvb]; exact hb⟩, ?_⟩
  rw [hva, hvb, eqA_iff (rep_compA (rep_compA hGi (hrep ha)) hGa) (hrep hb)]
  rw [had, hbd, hE _ ha, hE _ hb, wP_code hA hB, P.code_inv (by omega),
    P.code_mul (by omega), P.code_mul (by omega)] at he
  exact P.code_inj (by omega) he

end CFSG.KC.LQT.Cov.Perm

end
