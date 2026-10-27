module

public import CFSG.Certificates.Kernel.K3EnumProved
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Child3Reps
public import CFSG.Certificates.Kernel.Spor.HBfsTree

public section

namespace CFSG.KC.K3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.Th.Native CFSG.KS.MulH
open CFSG.KS.BfsReplay SP EP CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSmallLie.Child3.SelK3 CFSG.Sporadic.SmallOddCore

namespace KP

variable {K : K3C}

theorem ap_compT {n : Nat} (P Q : Table) {i : Nat} (hi : i < n) :
    ap (compT n P Q) i = ap P (ap Q i) := by
  unfold compT ap
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem ap_idT {n : Nat} (hn : n < 2 ^ 32) {i : Nat} (hi : i < n) : ap (idT n) i = i := by
  unfold idT ap
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega)]

theorem invoOK_eq {n : Nat} (hn : n < 2 ^ 32) (P : Table) :
    CFSG.Sporadic.Th.Native.invoOK n P = tblEq n (compT n P P) (idT n) := by
  unfold CFSG.Sporadic.Th.Native.invoOK tblEq
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [ap_compT _ _ hi, ap_idT hn hi]

theorem order3OK_eq {n : Nat} (hn : n < 2 ^ 32) (P : Table) :
    order3OK n P = tblEq n (compT n P (compT n P P)) (idT n) := by
  unfold order3OK tblEq
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [ap_compT _ _ hi, ap_compT _ _ hi, ap_idT hn hi]

theorem tblEq_tb {P Q : Nat} (hP : Cn K P) (hQ : Cn K Q) :
    tblEq K.n (tb K P) (tb K Q) = Nat.beq P Q := tblEq_unpack hP hQ

theorem commTT_tb {P Q : Nat} (hP : Cn K P) (hQ : Cn K Q) :
    commTT K.n (tb K P) (tb K Q) = Nat.beq (K.pc P Q) (K.pc Q P) := by
  unfold commTT
  rw [tb_pc hP hQ, tb_pc hQ hP, tblEq_tb (cn_pc hP hQ) (cn_pc hQ hP)]

theorem n32 (hs : szOK K.n K.w = true) : K.n < 2 ^ 32 := by
  have := (CFSG.KC.BfsPin.szOK_facts' hs).1
  omega

theorem idT_eq (hs : szOK K.n K.w = true) : idT K.n = tb K K.one := (tb_one hs).symm

theorem tblEq_one (hs : szOK K.n K.w = true) {P : Nat} (hP : Cn K P) :
    tblEq K.n (tb K P) (idT K.n) = Nat.beq P K.one := by
  rw [idT_eq hs, tblEq_tb hP (cn_one hs)]

theorem invoOK_tb (hs : szOK K.n K.w = true) {P : Nat} (hP : Cn K P) :
    CFSG.Sporadic.Th.Native.invoOK K.n (tb K P) = Nat.beq (K.pc P P) K.one := by
  rw [invoOK_eq (n32 hs), tb_pc hP hP, tblEq_one hs (cn_pc hP hP)]

theorem isOrd3_tb (hs : szOK K.n K.w = true) {P : Nat} (hP : Cn K P) :
    isOrd3 K.n (tb K P) = (!Nat.beq P K.one && Nat.beq (K.pc P (K.pc P P)) K.one) := by
  unfold isOrd3
  rw [order3OK_eq (n32 hs), tb_pc hP hP, tb_pc hP (cn_pc hP hP),
    tblEq_one hs (cn_pc hP (cn_pc hP hP)), tblEq_one hs hP]

theorem natArr_tb {P : Nat} (hP : Cn K P) : natArr (tb K P) = unpack K.n K.w P := by
  apply Array.ext (by simp [natArr, tabT])
  intro i h1 h2
  simp only [natArr, tabT, Array.getElem_map]
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
  have := unpack_lt (i := i) hP
  rwa [getElem!_pos _ i h2] at this

theorem permOK_tb (hs : szOK K.n K.w = true) {P Q : Nat}
    (h : permOK K.n K.w (mask K.w) (K.n * K.w) P Q = true) :
    CFSG.Sporadic.SmallOddCore.permOK K.n (tb K P) = true := by
  have hpp := CFSG.KC.Misc.ArrEnum.pp_of_permOK hs h
  unfold CFSG.Sporadic.SmallOddCore.permOK
  rw [natArr_tb hpp.1, CFSG.KC.BfsPin.invCand_PP hpp]
  exact CFSG.KS.Raw.Orb.isInvA_unpack (CFSG.KS.PinvS.permOK_pinvS hpp.1 hpp.2)

theorem memT_ofFn {n cnt q : Nat} {U : Nat → Table} {x : Table} (hq : q < cnt)
    (hx : tblEq n x (U q) = true) : memT n (Array.ofFn (n := cnt) fun i => U i.val) x = true := by
  unfold memT
  rw [Array.any_eq_true]
  exact ⟨q, by simpa using hq, by simpa using hx⟩

theorem all_zip_map {α β : Type} (f : α → β) (P : α × β → Bool) :
    ∀ l : List α, (∀ x ∈ l, P (x, f x) = true) → (l.zip (l.map f)).all P = true
  | [], _ => rfl
  | x :: l, h => by
    rw [List.map_cons, List.zip_cons_cons, List.all_cons, h x List.mem_cons_self,
      all_zip_map f P l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem conjTree_any (n : Nat) (gens gensI : Array Table) (x : Table) (cap : Nat) :
    conjTreeOK n gens gensI x (conjClosureH n gens gensI x cap).1
      (conjClosureH n gens gensI x cap).2.1 (conjClosureH n gens gensI x cap).2.2 = true := by
  have e : conjClosureH n gens gensI x cap = CFSG.KS.HBfs.hbfs (hkey n)
      (fun l y => conjT n gens[l]! gensI[l]! y) gens.size x cap := rfl
  obtain ⟨a1, a2, -, -, a5⟩ := CFSG.KS.HBfs.hbfs_tree (hkey n)
    (fun l y => conjT n gens[l]! gensI[l]! y) gens.size x cap
  rw [e]
  unfold conjTreeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨a1, by rw [a2]; exact tblEqH_self n _⟩, allInH_of fun i h1 h2 => ?_⟩
  obtain ⟨b1, b2, b3⟩ := a5 i (by omega) h2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨b1, b2⟩, ?_⟩
  rw [b3]
  exact tblEqH_self n _

end KP

open KP in
theorem k3_sound_proved {D : Data} {K : K3C}
    (hn : D.n = K.n) (hR : D.regs = K.R) (hprog : D.prog = (List.range K.N).map (instrOf K))
    (hg : D.gens.size = K.g) (hgt : ∀ i < K.g, D.gens[i]! = tblOf K (K.GP i))
    (hsyl : D.syl = (List.range K.sy).map K.SY) (hord : D.order = K.ord) (hreps : D.reps = K.RE)
    (hwits : D.wits = (List.range K.nw).map (witOf K))
    (hh : K.headK = true) (hs : ∀ t < K.N, K.stepK t = true) (hf : ∀ r < K.R, K.finK r = true)
    (he : ∀ k < K.ord, K.eK k = true) (hc : ∀ p < K.NC, K.cK p = true)
    (hm : ∀ k < K.ord, K.memK k = true) (hw : ∀ j < K.nw, K.witK j = true) :
    check D = true := by
  have hF := hf_of hh
  obtain ⟨hs2, hsz, hreg⟩ := slp_final (slp_run hn hR hprog hg hgt hF.sz hF.gR hF.gc hs) hf
  have hlt := instrLt_all hR hprog hs
  change (decide (D.gens.size ≤ D.regs) && D.prog.all (instrLtB D.regs) &&
    (runSLP D.n D.prog (regs0 D)).2 &&
    checkCore D.n D.order (runSLP D.n D.prog (regs0 D)).1 D.syl D.reps D.wits) = true
  generalize runSLP D.n D.prog (regs0 D) = st at hs2 hsz hreg ⊢
  rw [hlt, hs2, hn, hord, hreps, hwits, hsyl, hg, hR]
  simp only [decide_eq_true hF.gR, Bool.true_and, Bool.and_true]
  unfold checkCore
  simp only [Bool.and_eq_true]
  have hsz32 := n32 hF.sz
  have hAc : ∀ j < K.sy, Cn K (K.A j) := fun j hj => (hreg _ (hF.syl j hj).1).2
  have hAIc : ∀ j < K.sy, Cn K (K.AI j) := fun j hj => (hF.syl j hj).2.1
  have hperm := fun j (hj : j < K.sy) => (hF.syl j hj).2.2
  have hA : (List.map (fun r => st.1[r]!) (List.map K.SY (List.range K.sy))).toArray =
      Array.ofFn (n := K.sy) fun a => tb K (K.A a.val) := by
    apply Array.ext (by simp)
    intro i h1 h2
    have hi : i < K.sy := by simpa using h2
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, Array.getElem_ofFn]
    exact (hreg _ (hF.syl i hi).1).1
  rw [hA]
  have hAI : Array.map (invT K.n) (Array.ofFn (n := K.sy) fun a => tb K (K.A a.val)) =
      Array.ofFn (n := K.sy) fun a => tb K (K.AI a.val) := by
    apply Array.ext (by simp)
    intro i h1 h2
    have hi : i < K.sy := by simpa using h2
    simp only [Array.getElem_map, Array.getElem_ofFn]
    exact invT_tb (hAc i hi) (hperm i hi)
  rw [hAI]
  generalize hGA : (Array.ofFn (n := K.sy) fun a => tb K (K.A a.val)) = GA
  generalize hGAI : (Array.ofFn (n := K.sy) fun a => tb K (K.AI a.val)) = GAI
  have hGAs : GA.size = K.sy := by rw [← hGA, Array.size_ofFn]
  have hGAt : ∀ j < K.sy, GA[j]! = tb K (K.A j) := fun j hj => by
    rw [← hGA]
    exact ofFnH_get (fun j => tb K (K.A j)) hj
  have hGAIt : ∀ j < K.sy, GAI[j]! = tb K (K.AI j) := fun j hj => by
    rw [← hGAI]
    exact ofFnH_get (fun j => tb K (K.AI j)) hj
  have hGAIs : GAI.size = K.sy := by rw [← hGAI, Array.size_ofFn]
  have RM := mul_replay hF he hGAs hGAt hAc
  have e1 : mulClosureH K.n GA (K.ord + 1) = CFSG.KS.HBfs.hbfs (hkey K.n)
      (fun l y => compT K.n y GA[l]!) GA.size (idT K.n) (K.ord + 1) := rfl
  have hE : mulClosureH K.n GA (K.ord + 1) = (Array.ofFn (n := K.ord) fun i => tb K (K.E i.val),
      Array.ofFn (n := K.ord) fun i => parE K i.val, Array.ofFn (n := K.ord) fun i => labE K i.val) :=
    e1.trans (CFSG.KS.HBfs.hbfs_replay RM (Nat.le_succ _))
  have F := fun k (hk : k < K.ord) => ek_facts (he k hk)
  rw [hE]
  dsimp only
  have hRR : List.map (fun i => (Array.ofFn (n := K.ord) fun i => tb K (K.E i.val))[i]!) K.RE =
      K.RE.map fun i => tb K (K.E i) :=
    List.map_congr_left fun i hi => ofFnH_get (fun i => tb K (K.E i)) (hF.rel i hi)
  rw [hRR]
  have hcap : ∀ c < K.CS.length, lget K.CS c ≤ K.ord + 1 := fun c hc' =>
    Nat.le_succ_of_le (class_le hF he hc hc')
  have hRE : ∀ c (hc' : c < K.RE.length), lget K.RE c = K.RE[c] :=
    fun c hc' => by
      rw [CFSG.KC.Child3.lget_eq, List.getD_eq_getElem]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    simp [hsz, (hF.syl a (List.mem_range.1 ha)).1]
  · rw [Array.all_eq_true]
    intro i hi
    rw [hGAs] at hi
    rw [← getElem!_pos GA i (by omega), hGAt i hi]
    exact permOK_tb hF.sz (hperm i hi)
  · rw [Array.all_eq_true]
    intro i hi
    rw [hGAs] at hi
    rw [← getElem!_pos GA i (by omega), hGAt i hi, invT_tb (hAc i hi) (hperm i hi)]
    exact invOK_tb (hAc i hi) (hAIc i hi) (hperm i hi)
  · have hT := mulTree_of RM
    exact hT
  · unfold closedOK
    rw [Array.all_eq_true]
    intro k hk
    simp only [Array.size_ofFn] at hk
    rw [Array.getElem_ofFn, Array.all_eq_true]
    intro j hj
    rw [Array.size_append, hGAs, hGAIs] at hj
    rcases Nat.lt_or_ge j K.sy with hjs | hjs
    · rw [Array.getElem_append_left (by omega), ← getElem!_pos GA j (by omega), hGAt j hjs,
        tb_pc (F k hk).1 (hAc j hjs)]
      obtain ⟨b1, b2, -⟩ := (F k hk).2.2.2.2.1 j hjs
      refine memT_ofFn (U := fun i => tb K (K.E i)) b1 ?_
      rw [b2]
      exact tblEqH_self _ _
    · rw [Array.getElem_append_right (by omega), ← getElem!_pos GAI (j - GA.size) (by omega),
        hGAs, hGAIt (j - K.sy) (by omega), tb_pc (F k hk).1 (hAIc _ (by omega))]
      obtain ⟨b1, b2⟩ := (F k hk).2.2.2.2.2.1 (j - K.sy) (by omega)
      refine memT_ofFn (U := fun i => tb K (K.E i)) b1 ?_
      rw [b2]
      exact tblEqH_self _ _
  · exact hkeysDistinct_ofFn fun a ha b hb e => RM.kinj a ha b hb (UInt64.toNat_inj.1 e)
  · simp
  · rw [List.all_eq_true]
    intro x hx
    simpa using hF.rel x hx
  · simp [hF.re, hF.nw]
  · exact all_zip_map _ _ _ fun x _ => conjTree_any K.n GA GAI x (K.ord + 1)
  · rw [Array.all_eq_true]
    intro k hk
    simp only [Array.size_ofFn] at hk
    rw [Array.getElem_ofFn]
    cases hiso : isOrd3 K.n (tb K (K.E k))
    · rfl
    · rw [isOrd3_tb hF.sz (F k hk).1, Bool.and_eq_true] at hiso
      have h1 : K.E k ≠ K.one := fun e => by
        rw [e, Nat.beq_refl] at hiso
        exact absurd hiso.1 (by decide)
      obtain ⟨hp, hcases⟩ := mem_facts (hm k hk) h1 (Nat.eq_of_beq_eq_true hiso.2)
      obtain ⟨c1, c2, c3, -⟩ := ck_facts (hc _ hp)
      have hpos : 0 < lget K.CS (K.CI (K.MW k / 2)) := by omega
      have RC := cls_replay hF hc hGAs hGAt hGAIt hAc c1 hpos
      have e2 : conjClosureH K.n GA GAI (tb K (K.E (lget K.RE (K.CI (K.MW k / 2))))) (K.ord + 1) =
          CFSG.KS.HBfs.hbfs (hkey K.n) (fun l y => conjT K.n GA[l]! GAI[l]! y) GA.size
            (tb K (K.E (lget K.RE (K.CI (K.MW k / 2))))) (K.ord + 1) := rfl
      have hC := e2.trans (CFSG.KS.HBfs.hbfs_replay RC (hcap _ c1))
      have hcl : K.CI (K.MW k / 2) < K.RE.length := by rw [hF.re]; exact c1
      simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_map]
      refine ⟨_, ⟨_, ⟨_, List.getElem_mem hcl, rfl⟩, rfl⟩, ?_⟩
      rw [← hRE _ hcl, hC]
      have hq : K.MW k / 2 - lget K.OFF (K.CI (K.MW k / 2)) < lget K.CS (K.CI (K.MW k / 2)) := c3
      have hpe : lget K.OFF (K.CI (K.MW k / 2)) + (K.MW k / 2 - lget K.OFF (K.CI (K.MW k / 2))) =
          K.MW k / 2 := by omega
      rcases hcases with e | e
      · rw [memT_ofFn (U := fun i => tb K (K.CE (lget K.OFF (K.CI (K.MW k / 2)) + i)))
          (x := tb K (K.E k)) hq (by
          simp only [hpe, e]
          exact tblEqH_self _ _)]
        rfl
      · rw [tb_pc (F k hk).1 (F k hk).1, memT_ofFn (U := fun i =>
            tb K (K.CE (lget K.OFF (K.CI (K.MW k / 2)) + i)))
          (x := tb K (K.pc (K.E k) (K.E k))) hq (by
          simp only [hpe, e]
          exact tblEqH_self _ _)]
        simp
  · rw [List.all_eq_true]
    intro pr hpr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hpr
    simp only [List.length_zip, List.length_map, List.length_range] at hj
    have hj1 : j < K.RE.length := by omega
    have hj2 : j < K.nw := by omega
    have hjc : j < K.CS.length := by rw [← hF.re]; exact hj1
    rw [List.getElem_zip]
    simp only [List.getElem_map, List.getElem_range]
    have W := wit_facts (hw j hj2)
    rw [hRE j hj1] at W
    have hx : Cn K (K.E K.RE[j]) := (F _ (hF.rel _ (List.getElem_mem hj1))).1
    unfold witOf
    by_cases e : K.WT j = 0
    · obtain ⟨a1, a2, a3, a4⟩ := W.1 e
      rw [ite_eq_left e]
      have hu := hreg _ a1
      simp only [witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      rw [hu.1, commTT_tb hu.2 hx, tb_pc hu.2 hu.2, tblEq_one hF.sz (cn_pc hu.2 hu.2),
        ← (pw_facts hF.sz hu.2 4).2, tblEq_one hF.sz (pw_facts hF.sz hu.2 4).1, a2, a4]
      refine ⟨⟨⟨by omega, Nat.beq_refl _⟩, ?_⟩, Nat.beq_refl _⟩
      cases e' : Nat.beq (K.pc (K.reg (K.WU j)) (K.reg (K.WU j))) K.one
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e') a3
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := W.2 e
      rw [ite_eq_right e]
      have hu := hreg _ a1
      have hv := hreg _ a2
      have hne : ∀ {a b : Nat}, a ≠ b → Nat.beq a b = false := fun h => by
        cases e' : Nat.beq _ _
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e') h
      simp only [witOK, involOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      rw [hu.1, hv.1, invoOK_tb hF.sz hu.2, invoOK_tb hF.sz hv.2, tblEq_one hF.sz hu.2,
        tblEq_one hF.sz hv.2, tblEq_tb hu.2 hv.2, commTT_tb hu.2 hv.2, commTT_tb hu.2 hx,
        commTT_tb hv.2 hx, a3, a5, a8, a9, a10, hne a4, hne a6, hne a7]
      simp only [Nat.beq_refl, and_self, and_true]
      omega

end CFSG.KC.K3

end
