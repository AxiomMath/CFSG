module

public import CFSG.Certificates.Kernel.LocalQTPipeCosetReps
public import CFSG.Certificates.Kernel.LocalQTPipeCosetOrb
public import CFSG.Certificates.Kernel.LocalQTPipeCosetShape

public section

namespace CFSG.KC.LQT.PPC

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.PPB
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem getT_eq : ∀ (L : List (List Nat)) (j : Nat), getT L j = L.getD j []
  | [], _ => rfl
  | x :: t, j => by
    change Bool.rec (motive := fun _ => List Nat) (getT t (Nat.sub j 1)) x (Nat.beq j 0) = _
    cases j with
    | zero => rfl
    | succ j =>
      have e : Nat.beq (j + 1) 0 = false := rfl
      rw [e]
      dsimp only
      rw [getT_eq t, List.getD_cons_succ]
      rfl

theorem gensK_eq (RC : List Nat) (MF : Nat → Nat) (xl : List Nat) :
    gensK RC MF xl = RC ++ xl.map MF := by
  have e : (List.rec (motive := fun _ => List Nat) [] (fun x _ ih => List.cons (MF x) ih) xl :
      List Nat) = xl.map MF := by
    induction xl with
    | nil => rfl
    | cons x t ih =>
      change MF x :: _ = _
      rw [ih]; rfl
  unfold gensK
  rw [appK_eq, e]

theorem f2_append {R : Nat → Array Nat → Prop} :
    ∀ {l₁ l₂ : List Nat} {m₁ m₂ : List (Array Nat)}, List.Forall₂ R l₁ m₁ → List.Forall₂ R l₂ m₂ →
      List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂)
  | _, _, _, _, .nil, h => by simpa using h
  | _, _, _, _, .cons hr hl, h => List.Forall₂.cons hr (f2_append hl h)

theorem f2_facts {N W : Nat} {GS : List Nat} {ts : List (Array Nat)}
    (h : List.Forall₂ (TabP N W) GS ts) :
    (∀ g ∈ GS, ∃ t ∈ ts, ∀ x < N, imgW W g x = arrImg t x) ∧
    (∀ t ∈ ts, ∃ g ∈ GS, ∀ x < N, imgW W g x = arrImg t x) ∧
    (∀ t ∈ ts, ∀ i < N, arrImg t i < N) ∧
    (∀ t ∈ ts, ∀ i < N, ∀ j < N, arrImg t i = arrImg t j → i = j) := by
  refine ⟨fun g hg => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨t, ht, hp⟩ := f2_mem_left h hg
    exact ⟨t, ht, fun x hx => (hp.1.2 x hx).2⟩
  · obtain ⟨g, hg, hp⟩ := f2_mem_right h ht
    exact ⟨g, hg, fun x hx => (hp.1.2 x hx).2⟩
  · obtain ⟨g, hg, hp⟩ := f2_mem_right h ht
    exact fun i hi => (hp.1.2 i hi).1
  · obtain ⟨g, hg, hp⟩ := f2_mem_right h ht
    exact hp.2

theorem perm_spec {N : Nat} {l : List Nat} (h : PP.permK N l = true) :
    tabL N l = true ∧ ∀ i < N, ∀ j < N, l.getD i 0 = l.getD j 0 → i = j := by
  unfold PP.permK at h
  rw [andB_iff, beq_iff] at h
  obtain ⟨ht, hm⟩ := h
  refine ⟨ht, ?_⟩
  obtain ⟨hlen, hlt⟩ := tabL_spec ht
  have hcov : ∀ j < N, j ∈ l := by
    intro j hj
    rw [← maskL_testBit, hm]
    change (Nat.shiftLeft 1 N - 1).testBit j = true
    rw [shiftLeft_one, Nat.testBit_two_pow_sub_one]
    simpa using hj
  let f : Fin N → Fin N := fun i => ⟨l.getD i 0, hlt _ (by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)⟩
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 (hcov j j.2)
    refine ⟨⟨k, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [f]
    rw [List.getD_eq_getElem _ _ hk, e]
  have hinj := Finite.injective_iff_surjective.2 hsurj
  intro i hi j hj e
  have := @hinj ⟨i, hi⟩ ⟨j, hj⟩ (Fin.ext (by simpa [f] using e))
  simpa using this

theorem flatten_getD (a : Array (Array Nat)) (i : Nat) :
    (Array.flatten a).getD i 0 = (chunksK a).getD i 0 := by
  rw [chunksK_eq, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem tabP_of_perm {N W : Nat} (hW : N ≤ 2 ^ W) {a : Array (Array Nat)} {c : Nat}
    (hp : PP.permK N (chunksK a) = true) (hc : Nat.beq (codeK W (chunksK a)) c = true) :
    TabP N W c (Array.flatten a) := by
  obtain ⟨ht, hi⟩ := perm_spec hp
  have := rep_chunksK hW ht
  rw [← beq_iff.1 hc]
  refine ⟨this, fun i hi' j hj e => ?_⟩
  apply hi i hi' j hj
  have e' : (Array.flatten a).getD i 0 = (Array.flatten a).getD j 0 := e
  rwa [flatten_getD, flatten_getD] at e'

theorem rep_of_tab {N W : Nat} (hW : N ≤ 2 ^ W) {a : Array (Array Nat)} {c : Nat}
    (ht : tabL N (chunksK a) = true) (hc : Nat.beq (codeK W (chunksK a)) c = true) :
    Rep N W c (Array.flatten a) := by
  rw [← beq_iff.1 hc]
  exact rep_chunksK hW ht

theorem xs_getD_toList (xs : Array (List Nat)) (h : Nat) : xs.toList.getD h [] = xs.getD h [] := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

theorem xs_getD_mem (xs : Array (List Nat)) {h : Nat} (hh : h < xs.size) :
    xs.getD h [] ∈ xs.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hh]
  exact Array.mem_def.1 (Array.getElem_mem hh)

theorem coset_core {N W : Nat} (hN : 0 < N) {Aa' Ab' par gen repR : Array Nat}
    {qp : List (Nat × Nat)} {tab : Nat → Array Nat} (xs : Array (List Nat))
    (TF MF : Nat → Nat) (ML REPS OML BM : List Nat) (BWL PWL : List (List Nat))
    (PRK GNK RPK RIK QPK QGK DPK h₁ h₂ KM KR LR KB KP : Nat)
    (t0 : TabP N W (TF 0) Aa') (t1 : TabP N W (TF 1) Ab')
    (rP : Rep N W PRK par) (rG : Rep N W GNK gen) (rR : Rep N W RPK repR)
    (hpar : ∀ y < N, 0 < y → par.getD y 0 < y)
    (hT : ∀ p ∈ qp, TabP N W (TF p.1) (tab p.1))
    (hid : idK N W (MF 0) = true) (hM : needP W PRK ML = true)
    (hKM : lenA ML = KM) (hm : ∀ c < KM, omChk N W TF MF PRK GNK (getK ML c) = true)
    (hRM : ∀ x ∈ REPS, x = 0 ∨ x ∈ ML)
    (hXM : ∀ l ∈ xs.toList, ∀ x ∈ l, x = 0 ∨ x ∈ ML)
    (hrs : repsSumK N REPS OML = true) (hKR : KR * LR = N)
    (hr : ∀ c < KR, repsChunk N W (qpK TF qp) RPK RIK QPK QGK DPK REPS OML (c * LR) LR = true)
    (hKB : xs.size = KB) (hBL : lenA BM = KB)
    (hb : ∀ h < KB, blockK N W (qpK TF qp) MF RPK REPS BM BWL xs.toList h = true)
    (hKP : KB * lenA REPS = KP)
    (hp : ∀ i < KP, pairK N W (qpK TF qp) MF RPK REPS BM PWL xs.toList i = true)
    (hsh : shapeK N BM h₁ h₂ = true) :
    blocksClosed (qp.map fun p => tab p.1) N Aa' Ab' par gen xs
        (blocksOf (qp.map fun p => tab p.1) N Aa' Ab' par gen xs) ∧
      repsOK (qp.map fun p => tab p.1) N repR (repList N repR)
        (repOrbs (qp.map fun p => tab p.1) N (repList N repR)) ∧
      closureOK (qp.map fun p => tab p.1) N Aa' Ab' par gen xs
        (blocksOf (qp.map fun p => tab p.1) N Aa' Ab' par gen xs) (repList N repR) ∧
      shapeOK N (blocksOf (qp.map fun p => tab p.1) N Aa' Ab' par gen xs) := by
  have hMF := om_nodes hN t0 t1 rP rG hpar hid hM (by intro c hc; rw [hKM] at hc; exact hm c hc)
  have hROmT : List.Forall₂ (TabP N W) (qpK TF qp) (qp.map fun p => tab p.1) := by
    rw [qpK_eq]; exact f2_map qp (fun p => TF p.1) (fun p => tab p.1) hT
  obtain ⟨_, _, htabR, hinjR⟩ := f2_facts hROmT
  have hall : ∀ i < N, repsAt N W (qpK TF qp) RPK RIK QPK QGK DPK REPS OML i = true := by
    intro i hi
    have hLR : 0 < LR := by
      rcases Nat.eq_zero_or_pos LR with h | h
      · rw [h] at hKR; omega
      · exact h
    have hc : i / LR < KR := by
      rw [Nat.div_lt_iff_lt_mul hLR]; omega
    have := allR_spec' (hr _ hc) (i % LR) (Nat.mod_lt _ hLR)
    have e : i / LR * LR + i % LR = i := by
      have := Nat.div_add_mod i LR; rw [Nat.mul_comm] at this; exact this
    rwa [e] at this
  obtain ⟨R1, R2⟩ := reps_sound hN hT rR hrs hall
  have hTS : ∀ h < xs.size, List.Forall₂ (TabP N W)
      (gensK (qpK TF qp) MF (getT xs.toList h))
      ((qp.map fun p => tab p.1) ++
        (xs.getD h []).map fun x => omegaOf N Aa' Ab' par gen x x) := by
    intro h hh
    rw [gensK_eq, getT_eq, xs_getD_toList]
    refine f2_append hROmT (f2_map _ MF _ fun x hx => (hMF x ?_).2)
    exact hXM _ (xs_getD_mem xs hh) x hx
  have hMFs : ∀ x, (x = 0 ∨ x ∈ ML) → TabP N W (MF x) (omegaOf N Aa' Ab' par gen x x) :=
    fun x hx => (hMF x hx).2
  have hRO : ∀ (ts : List (Array Nat)), (∀ t ∈ (qp.map fun p => tab p.1), t ∈ ts) →
      ∀ i < N, Reach ts (repR.getD i 0) i := fun ts hts i hi => reach_mono hts (R2 i hi)
  have hmask : ∀ h < xs.size, MaskOf N ((qp.map fun p => tab p.1) ++
      (xs.getD h []).map fun x => omegaOf N Aa' Ab' par gen x x) (getK BM h) := by
    intro h hh
    have hbh := hb h (by omega)
    have e : blockK N W (qpK TF qp) MF RPK REPS BM BWL xs.toList h =
        orbChk N W (gensK (qpK TF qp) MF (getT xs.toList h)) RPK REPS (getK BM h)
          (getT BWL h) := rfl
    rw [e] at hbh
    obtain ⟨f1, f2, f3, f4⟩ := f2_facts (hTS h hh)
    exact orbChk_sound hN rR (hRO _ (fun t ht => List.mem_append_left _ ht)) R1 f1 f2 f3 f4 hbh
  have hblocks : ∀ h < xs.size, (blocksOf (qp.map fun p => tab p.1) N Aa' Ab' par gen xs).getD h #[] =
      bfsVis N ((qp.map fun p => tab p.1) ++
        (xs.getD h []).map fun x => omegaOf N Aa' Ab' par gen x x) 0 :=
    fun h hh => blocksOf_getD' _ N Aa' Ab' par gen xs hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨blocksOf_size' _ N Aa' Ab' par gen xs, fun h hh => ?_⟩
    rw [hblocks h hh]
    exact bfsVis_closed N _ (f2_facts (hTS h hh)).2.2.1 hN
  · obtain ⟨L1, L2⟩ := repList_spec N repR
    refine ⟨fun i hi => (rR.2 i hi).1, fun i hi => L2 i hi, ?_, fun i hi => ?_⟩
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
      obtain ⟨i, hi, rfl⟩ := L1 x hx
      exact bfsVis_closed N _ htabR (rR.2 i hi).1
    · refine ⟨(repR.getD i 0, bfsVis N (qp.map fun p => tab p.1) (repR.getD i 0)),
        List.mem_map.2 ⟨_, L2 i hi, rfl⟩, rfl, ?_⟩
      exact (bfsVis_getD_iff N _ htabR (rR.2 i hi).1 hi).2 (R2 i hi)
  · intro h hh x hx
    obtain ⟨i, hi, rfl⟩ := (repList_spec N repR).1 x hx
    have hxR : repR.getD i 0 ∈ REPS := R1 i hi
    obtain ⟨c, hc, hcx⟩ := List.mem_iff_getElem.1 hxR
    have hL : 0 < REPS.length := by omega
    have hi0 : REPS.length * h + c < KP := by
      rw [← hKP, lenA_eq]
      have e : (h + 1) * REPS.length ≤ KB * REPS.length := Nat.mul_le_mul_right _ (by omega)
      have e2 : (h + 1) * REPS.length = REPS.length * h + REPS.length := by
        rw [Nat.succ_mul, Nat.mul_comm]
      omega
    have hpi := hp _ hi0
    have hdm := (Nat.div_mod_unique hL (a := REPS.length * h + c) (d := h) (c := c)).2
      ⟨by rw [Nat.add_comm], hc⟩
    have hpair : andB (Nat.blt (headK (getT PWL (REPS.length * h + c))) (lenA BM))
        (orbChk N W (appK (gensK (qpK TF qp) MF (getT xs.toList h)) [MF (getK REPS c)]) RPK REPS
          (getK BM (headK (getT PWL (REPS.length * h + c))))
          (tailK (getT PWL (REPS.length * h + c)))) = true := by
      have e : pairK N W (qpK TF qp) MF RPK REPS BM PWL xs.toList (REPS.length * h + c) =
          (fun h c C => andB (Nat.blt (headK C) (lenA BM))
            (orbChk N W (appK (gensK (qpK TF qp) MF (getT xs.toList h)) [MF (getK REPS c)]) RPK
              REPS (getK BM (headK C)) (tailK C)))
          ((REPS.length * h + c) / lenA REPS) ((REPS.length * h + c) % lenA REPS)
          (getT PWL (REPS.length * h + c)) := rfl
      rw [e, lenA_eq REPS, hdm.1, hdm.2] at hpi
      exact hpi
    rw [andB_iff, blt_iff, lenA_eq] at hpair
    obtain ⟨hk, horb⟩ := hpair
    have hBL' : BM.length = KB := by rw [← lenA_eq]; exact hBL
    have hk' : headK (getT PWL (REPS.length * h + c)) < xs.size := by omega
    have hxg : getK REPS c = repR.getD i 0 := by
      rw [getK_eq, List.getD_eq_getElem _ _ hc, hcx]
    rw [hxg] at horb
    have hTS' : List.Forall₂ (TabP N W)
        (appK (gensK (qpK TF qp) MF (getT xs.toList h)) [MF (repR.getD i 0)])
        (((qp.map fun p => tab p.1) ++
          (xs.getD h []).map fun x => omegaOf N Aa' Ab' par gen x x) ++
          [omegaOf N Aa' Ab' par gen (repR.getD i 0) (repR.getD i 0)]) := by
      rw [appK_eq]
      exact f2_append (hTS h hh) (List.Forall₂.cons (hMFs _ (hRM _ hxR)) List.Forall₂.nil)
    obtain ⟨f1, f2, f3, f4⟩ := f2_facts hTS'
    have hmk := orbChk_sound hN rR
      (hRO _ (fun t ht => List.mem_append_left _ (List.mem_append_left _ ht))) R1 f1 f2 f3 f4
      horb
    have hmk2 := hmask _ hk'
    have heq : bfsVis N (((qp.map fun p => tab p.1) ++
          (xs.getD h []).map fun x => omegaOf N Aa' Ab' par gen x x) ++
          [omegaOf N Aa' Ab' par gen (repR.getD i 0) (repR.getD i 0)]) 0 =
        bfsVis N ((qp.map fun p => tab p.1) ++
          (xs.getD (headK (getT PWL (REPS.length * h + c))) []).map fun x =>
            omegaOf N Aa' Ab' par gen x x) 0 := by
      apply bfsVis_eq_of_reach_iff N _ _ f3 (f2_facts (hTS _ hk')).2.2.1 hN
      intro j hj
      have a1 := hmk j
      have a2 := hmk2 j
      constructor
      · intro hr'
        exact (a2.1 ((a1.2) ⟨hj, hr'⟩)).2
      · intro hr'
        exact (a1.1 ((a2.2) ⟨hj, hr'⟩)).2
    have hgo : gensOm (qp.map fun p => tab p.1) N Aa' Ab' par gen (xs.getD h []) =
        (qp.map fun p => tab p.1) ++ (xs.getD h []).map fun x => omegaOf N Aa' Ab' par gen x x :=
      rfl
    rw [hgo]
    refine ⟨headK (getT PWL (REPS.length * h + c)), hk', ?_, ?_⟩
    · rw [hblocks _ hk', heq]
    · rw [hblocks _ hk', ← heq]
      exact bfsVis_closed N _ f3 hN
  · refine shapeOK_of_shapeK _ (by rw [blocksOf_size' _ N Aa' Ab' par gen xs, hKB, ← lenA_eq]; exact hBL.symm) ?_ ?_ hsh
    · intro h hh i hi
      have hh' : h < xs.size := by rwa [blocksOf_size'] at hh
      rw [hblocks h hh']
      rw [bfsVis_getD_iff N _ (f2_facts (hTS h hh')).2.2.1 hN hi]
      exact (and_iff_right hi).symm.trans ((hmask h hh') i).symm
    · intro h hh i hi
      have hh' : h < xs.size := by rwa [blocksOf_size'] at hh
      by_contra hne
      have := ((hmask h hh') i).1 (by simpa using hne)
      omega

theorem coset_sound {N W : Nat} (hW : N ≤ 2 ^ W) (hN : 0 < N)
    (Aa Ab ps gs rs : Array (Array Nat)) (prog qp : List (Nat × Nat)) (xs : Array (List Nat))
    (TF MF : Nat → Nat) (SL ML REPS OML BM : List Nat) (BWL PWL : List (List Nat))
    (PRK GNK RPK RIK QPK QGK DPK h₁ h₂ KS KM KR LR KB KP : Nat)
    (hA : PP.permK N (chunksK Aa) = true) (hB : PP.permK N (chunksK Ab) = true)
    (h0 : Nat.beq (codeK W (chunksK Aa)) (TF 0) = true)
    (h1 : Nat.beq (codeK W (chunksK Ab)) (TF 1) = true)
    (htree : treeK N (chunksK ps) (chunksK gs) = true)
    (hpt : tabL N (chunksK ps) = true) (hgt : tabL N (chunksK gs) = true)
    (hrt : tabL N (chunksK rs) = true)
    (hPK : Nat.beq (codeK W (chunksK ps)) PRK = true)
    (hGK : Nat.beq (codeK W (chunksK gs)) GNK = true)
    (hRK : Nat.beq (codeK W (chunksK rs)) RPK = true)
    (hso : slpOKK prog 2 = true) (hsn : slpNeedK prog SL = true)
    (hq : allA qp (fun p => anyL SL (Nat.beq p.1)) = true)
    (hKS : lenA SL = KS) (hs : ∀ c < KS, slpChk N W TF prog (getK SL c) = true)
    (hid : idK N W (MF 0) = true) (hM : needP W PRK ML = true)
    (hKM : lenA ML = KM) (hm : ∀ c < KM, omChk N W TF MF PRK GNK (getK ML c) = true)
    (hRM : allL REPS (fun x => orB (Nat.beq x 0) (anyL ML (Nat.beq x))) = true)
    (hXM : allA xs.toList (fun l => allL l fun x => orB (Nat.beq x 0) (anyL ML (Nat.beq x))) =
      true)
    (hrs : repsSumK N REPS OML = true) (hKR : KR * LR = N)
    (hr : ∀ c < KR, repsChunk N W (qpK TF qp) RPK RIK QPK QGK DPK REPS OML (c * LR) LR = true)
    (hKB : xs.size = KB) (hBL : lenA BM = KB)
    (hb : ∀ h < KB, blockK N W (qpK TF qp) MF RPK REPS BM BWL xs.toList h = true)
    (hKP : KB * lenA REPS = KP)
    (hp : ∀ i < KP, pairK N W (qpK TF qp) MF RPK REPS BM PWL xs.toList i = true)
    (hsh : shapeK N BM h₁ h₂ = true) :
    blocksClosed (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
        (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs
        (blocksOf (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
          (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs) ∧
      repsOK (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
        (Array.flatten rs) (repList N (Array.flatten rs))
        (repOrbs (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
          (repList N (Array.flatten rs))) ∧
      closureOK (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
        (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs
        (blocksOf (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
          (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs)
        (repList N (Array.flatten rs)) ∧
      shapeOK N
        (blocksOf (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
          (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs) := by
  have t0 : TabP N W (TF 0) (Array.flatten Aa) := tabP_of_perm hW hA h0
  have t1 : TabP N W (TF 1) (Array.flatten Ab) := tabP_of_perm hW hB h1
  have tv := tree_sound N ps gs htree
  have hpar : ∀ y < N, 0 < y → (Array.flatten ps).getD y 0 < y :=
    fun y hy hy0 => (tv.2.2 y hy hy0).1
  have rP : Rep N W PRK (Array.flatten ps) := rep_of_tab hW hpt hPK
  have rG : Rep N W GNK (Array.flatten gs) := rep_of_tab hW hgt hGK
  have rR : Rep N W RPK (Array.flatten rs) := rep_of_tab hW hrt hRK
  have hsl := slp_nodes t0 t1 hso hsn (by intro c hc; rw [hKS] at hc; exact hs c hc)
  have hT : ∀ p ∈ qp, TabP N W (TF p.1)
      ((slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) := by
    intro p hp
    rw [allA_eq, List.all_eq_true] at hq
    exact (hsl p.1 (Or.inr ((any_beq_iff SL p.1).1 (hq p hp)))).2
  have hRM' : ∀ x ∈ REPS, x = 0 ∨ x ∈ ML := by
    intro x hx
    rw [allL_iff] at hRM
    have := hRM x hx
    rw [orB_iff, beq_iff, any_beq_iff] at this
    exact this
  have hXM' : ∀ l ∈ xs.toList, ∀ x ∈ l, x = 0 ∨ x ∈ ML := by
    intro l hl x hx
    rw [allA_eq, List.all_eq_true] at hXM
    have := hXM l hl
    rw [allL_iff] at this
    have := this x hx
    rw [orB_iff, beq_iff, any_beq_iff] at this
    exact this
  exact coset_core (tab := fun j => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[j]!)
    hN xs TF MF ML REPS OML BM BWL PWL PRK GNK RPK RIK QPK QGK DPK h₁ h₂ KM KR LR KB KP t0 t1 rP rG
    rR hpar hT hid hM hKM hm hRM' hXM' hrs hKR hr hKB hBL hb hKP hp hsh

end CFSG.KC.LQT.PPC
