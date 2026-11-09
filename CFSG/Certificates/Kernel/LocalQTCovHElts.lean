module

public import CFSG.Certificates.Kernel.LocalQTCovHBase
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.LocalQTCovTElts
import CFSG.Certificates.Kernel.LocalQTCovPerm
import CFSG.Certificates.Kernel.LocalQTCovEqns
import CFSG.Certificates.Kernel.MonsterB.Co2MatSound
import CFSG.Certificates.Kernel.LocalQTTab2KSound
import CFSG.Certificates.Kernel.LocalQTBaseWProved

public section

namespace CFSG.KC.LQT.Cov.H

open CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.HSCover CFSG.Sporadic.Schreier
open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KC.LQT.Syl CFSG.Monster.B.Co2.Native
open CFSG.QuasithinUnique.Ch1.M22Cover (fo)

private theorem eltsH_gen_unpack {A B : Nat}
    (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A)
    (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B) (l : Nat) :
    Raw.unpack 3850 12 (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0)) = genArr l := by
  unfold genArr lc
  cases h : Nat.beq l 0
  · have hl : l ≠ 0 := fun e => by subst e; simp at h
    rw [if_neg hl]
    exact hB.symm
  · have hl : l = 0 := Nat.eq_of_beq_eq_true h
    rw [if_pos hl]
    exact hA.symm

private theorem eltsH_xwOf (D : CH) (i : Fin 3) : (ofCH D).xwOf i = D.xw.getD i [] := by
  rcases i with ⟨i, hi⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

section Pts

variable {A B Ai Bi : Nat} (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A)
  (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B)
  (hpA : permOK 3850 12 (mask 12) (3850 * 12) A Ai = true)
  (hpB : permOK 3850 12 (mask 12) (3850 * 12) B Bi = true)
include hA hB hpA hpB

omit hA hB in
private theorem eltsH_inv_key (l : Nat) :
    ∀ i < 3850, pg 12 (mask 12) (Bool.rec (motive := fun _ => Nat) Bi Ai (Nat.beq l 0))
      (pg 12 (mask 12) (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0)) i) = i := by
  cases Nat.beq l 0
  · exact fun i hi => ((CFSG.KC.LQT.Cov.T.perm_facts hpB).1 i hi).2
  · exact fun i hi => ((CFSG.KC.LQT.Cov.T.perm_facts hpA).1 i hi).2

omit hpA hpB in
private theorem eltsH_fwd_pg (l : Nat) (p : Fin 3850) :
    pg 12 (mask 12) (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0)) ((gen l)⁻¹ p) = p := by
  have h := rep_genArr l ((gen l)⁻¹ p)
  rw [← eltsH_gen_unpack hA hB l, CFSG.KS.Raw.Orb.unpack_get ((gen l)⁻¹ p).2] at h
  rw [h, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

private theorem eltsH_inv_pg (l : Nat) (p : Fin 3850) :
    pg 12 (mask 12) (Bool.rec (motive := fun _ => Nat) Bi Ai (Nat.beq l 0)) p =
      ((gen l)⁻¹ p : ℕ) := by
  rw [← eltsH_fwd_pg hA hB l p, eltsH_inv_key hpA hpB l _ ((gen l)⁻¹ p).2]

private theorem eltsH_ptI :
    ∀ (wd : List Nat) (p : Fin 3850), covPtI 12 (mask 12) Ai Bi wd p = ((wordP wd)⁻¹ p : ℕ) := by
  intro wd
  induction wd with
  | nil => intro p; simp [wordP, covPtI]
  | cons l wd ih =>
    intro p
    change strictN (pg 12 (mask 12) (Bool.rec (motive := fun _ => Nat) Bi Ai (Nat.beq l 0)) p)
      (covPtI 12 (mask 12) Ai Bi wd) = _
    rw [CFSG.KS.PF.strictN_eqP, eltsH_inv_pg hA hB hpA hpB l p, ih]
    simp [wordP, mul_inv_rev, Equiv.Perm.mul_apply]

private theorem eltsH_ptX (D : CH) :
    ∀ (u : List Nat), (∀ l ∈ u, l < 3) → ∀ p : Fin 3850,
      covPtX 12 (mask 12) Ai Bi D.xw u p =
        ((((u.map fun l => (ofCH D).x (fo l)).prod)⁻¹ p : Fin 3850) : ℕ) := by
  intro u
  induction u with
  | nil => intro _ p; simp [covPtX]
  | cons l u ih =>
    intro hu p
    change strictN (covPtI 12 (mask 12) Ai Bi (getK D.xw l []) p)
      (covPtX 12 (mask 12) Ai Bi D.xw u) = _
    have hl : l < 3 := hu l (by simp)
    have hfo : fo l = ⟨l, hl⟩ := by
      ext
      simp only [fo]
      exact Nat.mod_eq_of_lt hl
    have hx : (ofCH D).x (fo l) = wordP (getK D.xw l []) := by
      rw [hfo, CFSG.KC.LQT.Cov.Parse.getK_getD]
      change wordP ((ofCH D).xwOf ⟨l, hl⟩) = _
      rw [eltsH_xwOf]
    rw [CFSG.KS.PF.strictN_eqP, eltsH_ptI hA hB hpA hpB,
      ih (fun l' hl' => hu l' (by simp [hl'])), List.map_cons, List.prod_cons, hx]
    simp [mul_inv_rev, Equiv.Perm.mul_apply]

end Pts

private theorem eltsH_getRG_words (D : CH) (v : Nat) :
    getRG (rowsG D.words) v [] = D.words.getD v [] :=
  CFSG.KC.LQT.Cov.T.getRG_rowsG D.words v []

private theorem eltsH_word_mem {D : CH} (hwords : D.words.length = D.nV)
    {v : Nat} (hv : v < D.nV) : D.words.getD v [] ∈ D.words := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hwords]; exact hv),
    Option.getD_some]
  exact List.getElem_mem _

private theorem eltsH_el (D : CH) (v : Nat) :
    (ofCH D).tab.el (ofCH D).x v = ((D.words.getD v []).map fun l => (ofCH D).x (fo l)).prod := by
  unfold CFSG.QuasithinUnique.Ch1.M22Cover.CayTab.el
  change ((((ofCH D).words[v]!).map fo).map (ofCH D).x).prod = _
  rw [show (ofCH D).words = D.words.toArray from rfl, CFSG.KC.LQT.Cov.T.toArray_getElem!_list,
    List.map_map]
  rfl

private theorem eltsH_el_mem (D : CH) (v : Nat) :
    (ofCH D).tab.el (ofCH D).x v ∈ hsChain.originalSubgroup := by
  rw [eltsH_el]
  exact Subgroup.list_prod_mem _ fun y hy => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
    exact wordP_mem _

private theorem eltsH_eq_of_base {g h : Equiv.Perm (Fin 3850)}
    (hg : g ∈ hsChain.originalSubgroup) (hh : h ∈ hsChain.originalSubgroup)
    (e : ∀ p : Fin 3850, (p : ℕ) ∈ covBase → g⁻¹ p = h⁻¹ p) : g = h := by
  have h1 := hs_baseFaithful (h * g⁻¹) (Subgroup.mul_mem _ hh (Subgroup.inv_mem _ hg))
    fun p hp => by
      rw [Equiv.Perm.mul_apply, e p hp]
      simp
  exact (mul_inv_eq_one.mp h1).symm

private theorem eltsH_FR_get {nV : Nat} {f : Nat → List Nat} {v : Nat} (hv : v < nV) :
    getRG (rowsG (List.map f (List.range nV))) v [] = f v := by
  rw [CFSG.KC.LQT.Cov.T.getRG_rowsG, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [List.length_range]; exact hv),
    Option.map_some, Option.getD_some, List.getElem_range]

private theorem eltsH_map_base {f g : Nat → Nat}
    (h : eqL (List.map f covBase) (List.map g covBase) = true) :
    ∀ p : Fin 3850, (p : ℕ) ∈ covBase → f p = g p := by
  rw [CFSG.KC.LQT.Cov.Eqns.eqL_iff, List.map_inj_left] at h
  exact fun p hp => h p hp

private theorem eltsH_isInv {t : Array Nat} {g : Equiv.Perm (Fin 3850)}
    (ht : CFSG.Monster.B.Co2.Rep 3850 t g) : isInvA 3850 t (invCand 3850 t) = true :=
  CFSG.KC.LQT.Cov.Perm.isInvA_of_rep ht (CFSG.KC.LQT.Cov.Perm.rep_invCand ht)

private theorem eltsH_good_base {D : CH} {TG TB : List (List Nat)} {w m Ai Bi : Nat}
    {FR : List (List (List Nat))} (h : goodH D TG TB w m Ai Bi FR = true) :
    0 < D.nV ∧ D.words.getD 0 [] = [] := by
  rw [goodH] at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h0, hw0, -⟩ := h
  refine ⟨Nat.blt_eq.mp h0, ?_⟩
  have hlen : (D.words.getD 0 [1]).length = 0 := by
    rw [← CFSG.KC.LQT.Cov.Parse.getK_getD]
    exact CFSG.KC.LQT.Cov.Parse.lenK_length .. ▸ Nat.beq_eq.mp hw0
  rw [List.getD_eq_getElem?_getD] at hlen ⊢
  cases h : D.words[0]? with
  | none => simp [h] at hlen
  | some w => simpa [h] using hlen

private theorem eltsH_F_get {Ai Bi : Nat} {D : CH} {v : Nat} (hv : v < D.nV) :
    getRG (rowsG (List.map (fun v => covImg 12 (mask 12) Ai Bi D.xw (getRG (rowsG D.words) v []))
      (List.range D.nV))) v [] =
      List.map (fun b => covPtX 12 (mask 12) Ai Bi D.xw (getRG (rowsG D.words) v []) b) covBase :=
  eltsH_FR_get hv

section Main

variable {A B Ai Bi : Nat} (hA : hsStrongArrs[0]! = Raw.unpack 3850 12 A)
  (hB : hsStrongArrs[1]! = Raw.unpack 3850 12 B)
  (hpA : permOK 3850 12 (mask 12) (3850 * 12) A Ai = true)
  (hpB : permOK 3850 12 (mask 12) (3850 * 12) B Bi = true)
  {D : CH} (hwords : D.words.length = D.nV) (hletters : ∀ w ∈ D.words, ∀ l ∈ w, l < 3)
include hA hB hpA hpB hwords hletters

private theorem eltsH_ptV {v : Nat} (hv : v < D.nV) (p : Fin 3850) :
    covPtX 12 (mask 12) Ai Bi D.xw (getRG (rowsG D.words) v []) p =
      ((((ofCH D).tab.el (ofCH D).x v)⁻¹ p : Fin 3850) : ℕ) := by
  rw [eltsH_getRG_words, eltsH_ptX hA hB hpA hpB D _ (hletters _ (eltsH_word_mem hwords hv)),
    eltsH_el]

private theorem eltsH_F_eq {u v : Nat} (hu : u < D.nV) (hv : v < D.nV)
    (he : (ofCH D).tab.el (ofCH D).x u = (ofCH D).tab.el (ofCH D).x v) :
    covImg 12 (mask 12) Ai Bi D.xw (getRG (rowsG D.words) u []) =
      covImg 12 (mask 12) Ai Bi D.xw (getRG (rowsG D.words) v []) := by
  unfold covImg
  apply List.map_congr_left
  intro b hb
  have hb' : b < 3850 := by
    simp only [covBase, List.mem_cons, List.not_mem_nil, or_false] at hb
    omega
  have e1 := eltsH_ptV hA hB hpA hpB hwords hletters hu ⟨b, hb'⟩
  have e2 := eltsH_ptV hA hB hpA hpB hwords hletters hv ⟨b, hb'⟩
  rw [he] at e1
  exact e1.trans e2.symm

end Main

theorem covHA_sound {cs : List Char} {D : CH} (hp : parseH cs = some D)
    (hxw : D.xw.length = 3) (hwords : D.words.length = D.nV)
    (hletters : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) {P : List ℕ} {nV0 A B : ℕ}
    (hA : hsStrongArrs[0]! = CFSG.KS.Raw.unpack 3850 12 A)
    (hB : hsStrongArrs[1]! = CFSG.KS.Raw.unpack 3850 12 B)
    (h : covHA 3850 12 A B cs P nV0 = true) :
    goodCheck (ofCH D) (ofCH D).elaTab = true ∧
      (ofCH D).pairs.all (pairCheck (ofCH D) (ofCH D).elaTab) = true ∧
      (ofCH D).anchors.all (anchorCheck (ofCH D) (ofCH D).elaTab) = true ∧
      D.nV = nV0 ∧ 0 < D.nV := by
  rw [covHA, hp] at h
  simp only [CFSG.KS.PF.strictB_eqP] at h
  generalize pinvS 3850 12 (mask 12) A = Ai at h
  generalize pinvS 3850 12 (mask 12) B = Bi at h
  simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
    Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, -, hnv0, hpA, hpB, -, hgood, hdist, hpairs, hanchors⟩ := h
  obtain ⟨hnV, hz⟩ := eltsH_good_base hgood
  have hx : ∀ i, CFSG.Monster.B.Co2.Rep 3850 ((ofCH D).xa i) ((ofCH D).x i) :=
    fun i => (ofCH D).xa_rep i
  have hrep : ∀ {v : ℕ}, v < D.nV →
      CFSG.Monster.B.Co2.Rep 3850 ((ofCH D).elaTab[v]!) ((ofCH D).tab.el (ofCH D).x v) :=
    fun hv => (ofCH D).rep_el hx hv
  have hptV := @eltsH_ptV A B Ai Bi hA hB hpA hpB D hwords hletters
  have hptI := @eltsH_ptI A B Ai Bi hA hB hpA hpB
  have hFg := @eltsH_F_get Ai Bi D
  refine ⟨?_, ?_, ?_, Nat.beq_eq.mp hnv0, hnV⟩
  ·
    rw [goodH] at hgood
    simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil,
      Bool.and_true, Bool.and_eq_true] at hgood
    obtain ⟨-, -, hmain⟩ := hgood
    rw [CFSG.KC.LQT.Cov.Perm.allLtK_iff] at hmain
    rw [goodCheck]
    simp only [Bool.and_eq_true, decide_eq_true_eq, CFSG.Monster.B.Co2.allLt_iff, and_assoc]
    refine ⟨hnV, ?_, ?_, ?_⟩
    · rw [show (ofCH D).words = D.words.toArray from rfl,
        CFSG.KC.LQT.Cov.T.toArray_getElem!_list, hz]
      rfl
    · intro v hv i hi
      have hm := (CFSG.KC.LQT.Cov.Perm.allLtK_iff _ _).1 (hmain v hv) i hi
      rw [CFSG.KS.PF.strictB_eqP] at hm
      simp only [Bool.and_eq_true] at hm
      obtain ⟨ht, hb, he, hback⟩ := hm
      simp only [CFSG.KC.LQT.Cov.T.getRG_rowsG, Nat.add_eq, Nat.mul_eq] at ht hb hback
      rw [CFSG.KC.LQT.Cov.T.getRG_rowsG D.tgt] at he
      simp only [Nat.add_eq, Nat.mul_eq] at he
      have htlt : D.tgt.getD (3 * v + i) D.nV < D.nV := Nat.blt_eq.mp ht
      have hblt : D.back.getD (3 * v + i) D.nV < D.nV := Nat.blt_eq.mp hb
      obtain ⟨-, htd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt htlt
      obtain ⟨-, hbd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt hblt
      have htA : (ofCH D).tgtA[3 * v + i]! = D.tgt.getD (3 * v + i) D.nV := by
        rw [show (ofCH D).tgtA = D.tgt.toArray from rfl, CFSG.KC.LQT.Cov.Perm.arr_get, ← htd]
      have hbA : (ofCH D).backA[3 * v + i]! = D.back.getD (3 * v + i) D.nV := by
        rw [show (ofCH D).backA = D.back.toArray from rfl, CFSG.KC.LQT.Cov.Perm.arr_get, ← hbd]
      have hfo : fo i = (⟨i, hi⟩ : Fin 3) := by
        simpa using (fo_val (⟨i, hi⟩ : Fin 3))
      have hxi : (ofCH D).x ⟨i, hi⟩ = wordP (getK D.xw i []) := by
        rw [CFSG.KC.LQT.Cov.Parse.getK_getD]
        change wordP ((ofCH D).xwOf ⟨i, hi⟩) = _
        rw [eltsH_xwOf]
      set t := D.tgt.getD (3 * v + i) D.nV with ht_def
      rw [hFg htlt, hFg hv, List.map_map] at he
      have hpt := eltsH_map_base he
      have hel : (ofCH D).tab.el (ofCH D).x t =
          (ofCH D).tab.el (ofCH D).x v * (ofCH D).x ⟨i, hi⟩ := by
        apply eltsH_eq_of_base (eltsH_el_mem D t)
          (Subgroup.mul_mem _ (eltsH_el_mem D v) (wordP_mem _))
        intro p hp
        have := hpt p hp
        rw [Function.comp_apply, hptV htlt, hptV hv, hptI] at this
        rw [← hxi] at this
        rw [mul_inv_rev, Equiv.Perm.mul_apply]
        exact Fin.ext this
      refine ⟨by rw [htA]; exact htlt, by rw [hbA]; exact hblt, ?_, ?_⟩
      · rw [htA, hfo]
        exact (CFSG.Monster.B.Co2.eqA_iff (hrep htlt) (CFSG.Monster.B.Co2.rep_compA (hrep hv)
          (hx _))).2 hel
      · rw [hbA, ← hbd, show (ofCH D).tgtA = D.tgt.toArray from rfl,
          CFSG.KC.LQT.Cov.Perm.arr_get, beq_iff_eq]
        exact Nat.eq_of_beq_eq_true hback
    · intro u hu v hv
      by_cases huv : u < v
      · have hdec : decide (u < v) = true := decide_eq_true huv
        rw [hdec]
        simp only [Bool.not_true, Bool.false_or]
        rw [Bool.not_eq_true', Bool.eq_false_iff]
        intro heq
        have hel := (CFSG.Monster.B.Co2.eqA_iff (hrep hu) (hrep hv)).1 heq
        have hF := eltsH_F_eq hA hB hpA hpB hwords hletters hu hv hel
        have hnd := CFSG.KC.LQT.T2.nodup_of_distinctS hdist
        have hlenu : u < (List.map covCode (List.map (fun v => covImg 12 (mask 12) Ai Bi D.xw
            (getRG (rowsG D.words) v [])) (List.range D.nV))).length := by
          simp only [List.length_map, List.length_range]; exact hu
        have hlenv : v < (List.map covCode (List.map (fun v => covImg 12 (mask 12) Ai Bi D.xw
            (getRG (rowsG D.words) v [])) (List.range D.nV))).length := by
          simp only [List.length_map, List.length_range]; exact hv
        have helem : (List.map covCode (List.map (fun v => covImg 12 (mask 12) Ai Bi D.xw
            (getRG (rowsG D.words) v [])) (List.range D.nV)))[u]'hlenu =
            (List.map covCode (List.map (fun v => covImg 12 (mask 12) Ai Bi D.xw
            (getRG (rowsG D.words) v [])) (List.range D.nV)))[v]'hlenv := by
          simp only [List.getElem_map, List.getElem_range, hF]
        have := (List.Nodup.getElem_inj_iff hnd).1 helem
        omega
      · simp [huv]
  · rw [show (ofCH D).pairs =
        D.pairs.map (fun p => ({ gw := p.1, a := p.2.1, b := p.2.2 } : Rec)) from rfl,
      List.all_map]
    apply List.all_eq_true.2
    intro r hr
    have h := (CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hpairs r hr
    rw [pairH] at h
    simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true,
      Bool.and_eq_true] at h
    obtain ⟨ha, hb, he⟩ := h
    have ha' : r.2.1 < D.nV := Nat.blt_eq.mp ha
    have hb' : r.2.2 < D.nV := Nat.blt_eq.mp hb
    rw [hFg ha', List.map_map] at he
    have hpt := eltsH_map_base he
    have hGa := rep_wordArrP r.1
    have hinv := eltsH_isInv hGa
    have hGi := CFSG.Monster.B.Co2.rep_inv_of_isInvA hGa hinv
    have e2 : (ofCH D).tab.el (ofCH D).x r.2.1 * wordP r.1 =
        wordP r.1 * (ofCH D).tab.el (ofCH D).x r.2.2 := by
      apply eltsH_eq_of_base (Subgroup.mul_mem _ (eltsH_el_mem D _) (wordP_mem _))
        (Subgroup.mul_mem _ (wordP_mem _) (eltsH_el_mem D _))
      intro p hp
      have := hpt p hp
      rw [Function.comp_apply, hptV ha', hptI, hptI r.1 p, hptV hb'] at this
      rw [mul_inv_rev, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      exact Fin.ext this
    have hrel : (wordP r.1)⁻¹ * (ofCH D).tab.el (ofCH D).x r.2.1 * wordP r.1 =
        (ofCH D).tab.el (ofCH D).x r.2.2 := by
      rw [mul_assoc, e2, ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [Function.comp_apply, pairCheck, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hinv, ha'⟩, hb'⟩, ?_⟩
    exact (CFSG.Monster.B.Co2.eqA_iff (CFSG.Monster.B.Co2.rep_compA
      (CFSG.Monster.B.Co2.rep_compA hGi (hrep ha')) hGa) (hrep hb')).2 hrel
  · rw [show (ofCH D).anchors =
        D.anchors.map (fun p => ({ gw := p.1, a := 0, b := p.2 } : Rec)) from rfl,
      List.all_map]
    apply List.all_eq_true.2
    intro r hr
    have h := (CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hanchors r hr
    rw [anchorH] at h
    simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true,
      Bool.and_eq_true] at h
    obtain ⟨hb, he⟩ := h
    have hb' : r.2 < D.nV := Nat.blt_eq.mp hb
    have hpt := eltsH_map_base he
    have hGa := rep_wordArrP r.1
    have hinv := eltsH_isInv hGa
    have hGi := CFSG.Monster.B.Co2.rep_inv_of_isInvA hGa hinv
    have e2 : cElt * wordP r.1 = wordP r.1 * (ofCH D).tab.el (ofCH D).x r.2 := by
      apply eltsH_eq_of_base (Subgroup.mul_mem _ (wordP_mem _) (wordP_mem _))
        (Subgroup.mul_mem _ (wordP_mem _) (eltsH_el_mem D _))
      intro p hp
      have := hpt p hp
      rw [hptI _ p, hptI, hptI r.1 p, hptV hb'] at this
      rw [mul_inv_rev, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      exact Fin.ext this
    have hrel : (wordP r.1)⁻¹ * cElt * wordP r.1 = (ofCH D).tab.el (ofCH D).x r.2 := by
      rw [mul_assoc, e2, ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [Function.comp_apply, anchorCheck, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hinv, hb'⟩, ?_⟩
    exact (CFSG.Monster.B.Co2.eqA_iff (CFSG.Monster.B.Co2.rep_compA
      (CFSG.Monster.B.Co2.rep_compA hGi (rep_wordArrP cWord)) hGa) (hrep hb')).2 hrel

end CFSG.KC.LQT.Cov.H

end
