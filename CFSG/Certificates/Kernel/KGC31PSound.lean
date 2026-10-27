module

public import Certificates.Data.Kernel.KGC31P
public import CFSG.Certificates.Kernel.HeGlueKGlue
public import CFSG.Certificates.Kernel.Child3Reps
public import CFSG.Certificates.Kernel.SporSch.TblSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.Quasithin.Vol2.KGFactC31FrameCheck
public import CFSG.Certificates.Kernel.SporSch.CodesImg

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.HeGlueK
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31.Native
open CFSG.KC.Child3 (tabP ap_tabP tabP_size)

variable {n w : Nat}

theorem all_congr' {α : Type} : ∀ {l : List α} {f g : α → Bool}, (∀ a ∈ l, f a = g a) →
    l.all f = l.all g
  | [], _, _, _ => rfl
  | a :: l, f, g, H => by
    rw [List.all_cons, List.all_cons, H a List.mem_cons_self,
      all_congr' fun b hb => H b (List.mem_cons_of_mem _ hb)]

theorem any_congr' {α : Type} : ∀ {l : List α} {f g : α → Bool}, (∀ a ∈ l, f a = g a) →
    l.any f = l.any g
  | [], _, _, _ => rfl
  | a :: l, f, g, H => by
    rw [List.any_cons, List.any_cons, H a List.mem_cons_self,
      any_congr' fun b hb => H b (List.mem_cons_of_mem _ hb)]

theorem all_map_congr {α β : Type} {l : List α} {g : α → β} {f : β → Bool} {h : α → Bool}
    (H : ∀ a ∈ l, f (g a) = h a) : (l.map g).all f = l.all h := by
  rw [List.all_map]
  exact all_congr' fun a ha => H a ha

theorem any_map_congr {α β : Type} {l : List α} {g : α → β} {f : β → Bool} {h : α → Bool}
    (H : ∀ a ∈ l, f (g a) = h a) : (l.map g).any f = l.any h := by
  rw [List.any_map]
  exact any_congr' fun a ha => H a ha

theorem tabP_eq {a : Nat} (ha : PP n w a) : tabP n w a = toTable (sg n w a) :=
  (CFSG.ComponentClassification.J2Cover.toTable_eq_arrTable (rep_sg ha)).symm

theorem _root_.CFSG.KC.BfsPin.PP.pc {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    PP n w (pc n w a b) := ha.mul hb

theorem _root_.CFSG.KC.BfsPin.PP.pinv {a : Nat} (ha : PP n w a) : PP n w (pinv n w a) := ha.inv

theorem PP_ppw {a : Nat} (ha : PP n w a) : ∀ e, PP n w (ppw n w a e)
  | 0 => PP.id ha.sz
  | e + 1 => ha.pc (PP_ppw ha e)

theorem PP_pcj {x xi t : Nat} (hx : PP n w x) (hxi : PP n w xi) (ht : PP n w t) :
    PP n w (pcj n w x xi t) := (hx.pc ht).pc hxi

theorem compT_tabP' {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    compT n (tabP n w a) (tabP n w b) = tabP n w (pc n w a b) := by
  have hn := ha.lt32
  rw [tabP_eq ha, tabP_eq hb, tabP_eq (ha.pc hb),
    CFSG.KS.Tbl.compT_eq_toTable hn (rep_toTable hn _) (rep_toTable hn _)]
  exact congrArg toTable (sg_pcomp ha hb).symm

theorem idT_tabP (hsz : szOK n w = true) : idT n = tabP n w (pidn n w) := by
  have hn : n < 2 ^ 32 := by have := (szOK_facts' hsz).1; omega
  rw [tabP_eq (PP.id hsz), sg_id hsz]
  exact CFSG.KS.Tbl.toTable_ext hn (by simp [idT]) (Rep.idT hn)

theorem invT_tabP {a : Nat} (ha : PP n w a) : invT n (tabP n w a) = tabP n w (pinv n w a) := by
  have hn := ha.lt32
  rw [tabP_eq ha, tabP_eq ha.pinv, pinv, sg_pinv ha]
  exact CFSG.KS.Tbl.toTable_ext hn (CFSG.KS.Tbl.invT_size _ _)
    (CFSG.KS.Tbl.invT_rep hn (rep_toTable hn _))

theorem invOK_tabP {a : Nat} (ha : PP n w a) : invOK n (tabP n w a) (invT n (tabP n w a)) = true := by
  rw [tabP_eq ha]
  exact CFSG.KS.Tbl.invOK_invT ha.lt32 (rep_toTable ha.lt32 _)

theorem tblEq_tabP {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    tblEq n (tabP n w a) (tabP n w b) = Nat.beq a b := by
  have hn := ha.lt32
  rw [beq_PP ha hb, tabP_eq ha, tabP_eq hb, Bool.eq_iff_iff, decide_eq_true_iff]
  exact CFSG.KS.Tbl.tblEq_iff_eq (rep_toTable hn _) (rep_toTable hn _)

theorem commT_tabP {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    commT n (tabP n w a) (tabP n w b) = Nat.beq (pc n w a b) (pc n w b a) := by
  rw [commT, compT_tabP' ha hb, compT_tabP' hb ha, tblEq_tabP (ha.pc hb) (hb.pc ha)]

theorem powT_tabP {a : Nat} (ha : PP n w a) : ∀ e, powT n e (tabP n w a) = tabP n w (ppw n w a e)
  | 0 => idT_tabP ha.sz
  | e + 1 => by
    rw [powT, powT_tabP ha e, compT_tabP' ha (PP_ppw ha e)]
    rfl

theorem conjTab_tabP {x xi t : Nat} (hx : PP n w x) (hxi : PP n w xi) (ht : PP n w t) :
    conjTab n (tabP n w x) (tabP n w xi) (tabP n w t) = tabP n w (pcj n w x xi t) := by
  unfold conjTab pcj
  rw [compT_tabP' hx ht, compT_tabP' (hx.pc ht) hxi]

theorem map_eq_compT {P T : Table} (hT : T.size = n) :
    T.map (fun t => P[t.toNat]!) = compT n P T := by
  apply Array.ext (by simp [compT, hT])
  intro i h1 h2
  simp only [Array.getElem_map, compT, Array.getElem_ofFn]
  rw [getElem!_pos T i (by simpa using h1)]

theorem wordT_tabP (hsz : szOK n w = true) {gens : ℤ → Table} {G : ℤ → Nat}
    (hG : ∀ l, gens l = tabP n w (G l)) (hP : ∀ l, PP n w (G l)) :
    ∀ wd, wordT n gens wd = tabP n w (pword n w G wd)
  | [] => idT_tabP hsz
  | l :: wd => by
    have ih := wordT_tabP hsz hG hP wd
    have e : wordT n gens (l :: wd) = (wordT n gens wd).map (fun t => (gens l)[t.toNat]!) := rfl
    rw [e, map_eq_compT (wordT_size n gens wd), ih, hG l, compT_tabP' (hP l) (PP_pword hsz hP wd)]
    rfl
where
  PP_pword (hsz : szOK n w = true) {G : ℤ → Nat} (hP : ∀ l, PP n w (G l)) :
      ∀ wd, PP n w (pword n w G wd)
    | [] => PP.id hsz
    | l :: wd => (hP l).pc (PP_pword hsz hP wd)

theorem PP_pword (hsz : szOK n w = true) {G : ℤ → Nat} (hP : ∀ l, PP n w (G l)) (wd : List ℤ) :
    PP n w (pword n w G wd) := wordT_tabP.PP_pword hsz hP wd

theorem PP_pmask (hsz : szOK n w = true) :
    ∀ (bs : List Nat), (∀ b ∈ bs, PP n w b) → ∀ m, PP n w (pmask n w bs m)
  | [], _, _ => PP.id hsz
  | b :: bs, h, m => by
    unfold pmask
    refine PP.pc ?_ (PP_pmask hsz bs (fun c hc => h c (List.mem_cons_of_mem _ hc)) _)
    split
    · exact h b List.mem_cons_self
    · exact PP.id hsz

theorem maskProd_tabP (hsz : szOK n w = true) :
    ∀ (bs : List Nat), (∀ b ∈ bs, PP n w b) →
      ∀ m, maskProd n (bs.map (tabP n w)) m = tabP n w (pmask n w bs m)
  | [], _, _ => idT_tabP hsz
  | b :: bs, h, m => by
    have hbs : ∀ c ∈ bs, PP n w c := fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hb : PP n w b := h b List.mem_cons_self
    rw [List.map_cons, maskProd, maskProd_tabP hsz bs hbs (m / 2), pmask]
    by_cases hm : m % 2 = 1
    · rw [if_pos hm, if_pos hm]
      exact compT_tabP' hb (PP_pmask hsz bs hbs _)
    · rw [if_neg hm, if_neg hm, idT_tabP hsz]
      exact compT_tabP' (PP.id hsz) (PP_pmask hsz bs hbs _)

theorem PP_pspan (hsz : szOK n w = true) {bs : List Nat} (h : ∀ b ∈ bs, PP n w b) :
    ∀ s ∈ pspan n w bs, PP n w s := by
  intro s hs
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hs
  exact PP_pmask hsz bs h m

theorem spanTabs_tabP (hsz : szOK n w = true) {bs : List Nat} (h : ∀ b ∈ bs, PP n w b) :
    spanTabs n (bs.map (tabP n w)) = (pspan n w bs).map (tabP n w) := by
  rw [spanTabs, pspan, List.length_map, List.map_map]
  exact List.map_congr_left fun m _ => maskProd_tabP hsz bs h m

theorem PP_porbTabs {m x xi t : Nat} (hx : PP n w x) (hxi : PP n w xi) (ht : PP n w t) :
    ∀ s ∈ porbTabs n w m x xi t, PP n w s := by
  intro s hs
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hs
  exact PP_pcj (PP_ppw hx j) (PP_ppw hxi j) ht

theorem orbTabs_tabP {m x xi t : Nat} (hx : PP n w x) (hxi : PP n w xi) (ht : PP n w t) :
    orbTabs n m (tabP n w x) (tabP n w xi) (tabP n w t) =
      (porbTabs n w m x xi t).map (tabP n w) := by
  rw [orbTabs, porbTabs, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp]
  rw [powT_tabP hx, powT_tabP hxi, conjTab_tabP (PP_ppw hx j) (PP_ppw hxi j) ht]

theorem eq_tabP_of_rep {T : Table} {g : Equiv.Perm (Fin n)} {X : Nat} (hn : n < 2 ^ 32)
    (hs : T.size = n) (hT : Rep n T g)
    (hg : CFSG.Monster.B.Mathieu.imageList g = (unpack n w X).toList) : T = tabP n w X := by
  rw [CFSG.KS.Tbl.toTable_ext hn hs hT]
  exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img hg

theorem imageList_of_rep {X : Nat} {g : Equiv.Perm (Fin n)}
    (hX : canonK n w (mask w) (n * w) X = true) (h : Rep n (tabP n w X) g) :
    CFSG.Monster.B.Mathieu.imageList g = (unpack n w X).toList := by
  obtain ⟨hn, -, -, hXr⟩ := PF.canon_facts hX
  unfold CFSG.Monster.B.Mathieu.imageList unpack
  rw [Array.toList_ofFn]
  congr 1
  funext i
  have e := h i.val i.isLt
  rw [ap_tabP i.isLt (by have := hXr i.val i.isLt; omega), idx_of_lt _ i.isLt] at e
  rw [e]
  rfl

theorem imageList_of_prep {X : Nat} {g : Equiv.Perm (Fin n)} (h : CFSG.KS.Raw.Orb.PRep n w X g) :
    CFSG.Monster.B.Mathieu.imageList g = (unpack n w X).toList := by
  unfold CFSG.Monster.B.Mathieu.imageList unpack
  rw [Array.toList_ofFn]
  congr 1
  funext i
  exact (h i).symm

theorem filterProducts_size {f : Table → Bool} :
    ∀ (Ts : List (List Table)) (g : Table) (acc : List Table), g.size = n →
      (∀ T ∈ acc, T.size = n) → ∀ T ∈ filterProducts n f Ts g acc, T.size = n
  | [], g, acc, hg, hacc, T, hT => by
    unfold filterProducts at hT
    split at hT
    · rcases List.mem_cons.1 hT with rfl | h
      · exact hg
      · exact hacc T h
    · exact hacc T hT
  | L :: Ts, g, acc, hg, hacc, T, hT => by
    unfold filterProducts at hT
    suffices ∀ (l : List Table) (a : List Table), (∀ T ∈ a, T.size = n) →
        ∀ T ∈ l.foldl (fun acc t => filterProducts n f Ts (compT n g t) acc) a, T.size = n from
      this L acc hacc T hT
    intro l
    induction l with
    | nil => intro a ha T hT; exact ha T hT
    | cons t l ih =>
      intro a ha T hT
      rw [List.foldl_cons] at hT
      exact ih _ (filterProducts_size Ts (compT n g t) a (by simp [compT]) ha) T hT

theorem allTables_size (Q : CFSG.Certificates.RawSchreierDatum n) :
    ∀ T ∈ allTables Q, T.size = n :=
  filterProducts_size _ _ _ (by simp [idT]) (fun _ h => absurd h List.not_mem_nil)

theorem inSpan_tabP (hsz : szOK n w = true) {bs : List Nat} (h : ∀ b ∈ bs, PP n w b) {t : Nat}
    (ht : PP n w t) : inSpan n (bs.map (tabP n w)) (tabP n w t) = pinSpan n w bs t := by
  rw [inSpan, spanTabs_tabP hsz h, pinSpan]
  exact any_map_congr fun s hs => tblEq_tabP ht (PP_pspan hsz h s hs)

theorem orbIs_tabP (hsz : szOK n w = true) {orb bs : List Nat} (ho : ∀ o ∈ orb, PP n w o)
    (hb : ∀ b ∈ bs, PP n w b) :
    orbIs n (orb.map (tabP n w)) (bs.map (tabP n w)) = porbIs n w orb bs := by
  rw [orbIs, porbIs, spanTabs_tabP hsz hb, spanTabs_tabP hsz ho]
  congr 1
  · exact all_map_congr fun o hoo =>
      any_map_congr fun s hs => tblEq_tabP (ho o hoo) (PP_pspan hsz hb s hs)
  · exact all_map_congr fun b hbb =>
      any_map_congr fun s hs => tblEq_tabP (hb b hbb) (PP_pspan hsz ho s hs)

theorem badAct_tabP {m x xi t : Nat} (hx : PP n w x) (hxi : PP n w xi) (ht : PP n w t) :
    badAct n m (tabP n w x) (tabP n w xi) (tabP n w t) = pbadAct n w m x xi t := by
  rw [badAct, pbadAct, conjTab_tabP hx hxi ht, tblEq_tabP (PP_pcj hx hxi ht) ht]
  congr 1
  refine all_congr' fun j _ => ?_
  have hc := PP_pcj (PP_ppw hx j) (PP_ppw hxi j) ht
  rw [powT_tabP hx, powT_tabP hxi, conjTab_tabP (PP_ppw hx j) (PP_ppw hxi j) ht,
    compT_tabP' ht hc, compT_tabP' hc ht, tblEq_tabP (ht.pc hc) (hc.pc ht)]

theorem orbOne_tabP (hsz : szOK n w = true) {m x t : Nat} {cands : List (List Nat)}
    (hx : PP n w x) (ht : PP n w t) (hc : ∀ c ∈ cands, ∀ b ∈ c, PP n w b) :
    (!(badAct n m (tabP n w x) (invT n (tabP n w x)) (tabP n w t)) ||
      (cands.map (List.map (tabP n w))).any
        (orbIs n (orbTabs n m (tabP n w x) (invT n (tabP n w x)) (tabP n w t)))) =
      porbOne n w m x cands t := by
  rw [invT_tabP hx, badAct_tabP hx hx.pinv ht, orbTabs_tabP hx hx.pinv ht, porbOne]
  congr 1
  exact any_map_congr fun c hcc =>
    orbIs_tabP hsz (PP_porbTabs hx hx.pinv ht) (hc c hcc)

theorem actOne_tabP {m x t : Nat} (hx : PP n w x) (ht : PP n w t) :
    (!(badAct n m (tabP n w x) (invT n (tabP n w x)) (tabP n w t))) = pactOne n w m x t := by
  rw [invT_tabP hx, badAct_tabP hx hx.pinv ht, pactOne]

theorem apPowW_eq (T : Table) {i : Nat} (hn : n < 2 ^ 32) (hi : i < n) :
    ∀ e, apPowW [T] e i = ap (powT n e T) i
  | 0 => by
    rw [powT, apPowW]
    unfold ap idT
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  | e + 1 => by
    rw [apPowW, apPowW_eq T hn hi e, powT]
    unfold apW
    simp only [List.foldr_cons, List.foldr_nil]
    unfold ap compT
    rw [getElem!_pos (Array.ofFn _) i (by simpa using hi), Array.getElem_ofFn]

theorem powFixW_eq (T : Table) (hn : n < 2 ^ 32) (e : Nat) :
    powFixW n [T] e = tblEq n (powT n e T) (idT n) := by
  rw [powFixW, tblEq, Bool.eq_iff_iff, allIn_eq_true, allIn_eq_true]
  refine forall_congr' fun i => forall_congr' fun _ => forall_congr' fun hi => ?_
  rw [apPowW_eq T hn hi e]
  have : ap (idT n) i = i := by
    unfold ap idT
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  rw [this]

theorem ordTest_tabP {x : Nat} (hx : PP n w x) (m : Nat) :
    ordTest n m (tabP n w x) = pord n w m x := by
  have hn := hx.lt32
  have h : ∀ e, powFixW n [tabP n w x] e = Nat.beq (ppw n w x e) (pidn n w) := fun e => by
    rw [powFixW_eq _ hn, powT_tabP hx, idT_tabP hx.sz, tblEq_tabP (PP_ppw hx e) (PP.id hx.sz)]
  rw [ordTest, ordW, pord, h]
  congr 1
  exact all_congr' fun e _ => by rw [h]

theorem elabOK_tabP {gs : List Nat} (hg : ∀ g ∈ gs, PP n w g) :
    elabOK n (gs.map (tabP n w)) = pelab n w gs := by
  rw [elabOK, pelab]
  congr 1
  · exact all_map_congr fun g hgg => by
      rw [compT_tabP' (hg g hgg) (hg g hgg), idT_tabP (hg g hgg).sz,
        tblEq_tabP ((hg g hgg).pc (hg g hgg)) (PP.id (hg g hgg).sz)]
  · exact all_map_congr fun g hgg => all_map_congr fun h hh => commT_tabP (hg g hgg) (hg h hh)

theorem frameOne_tabP (hsz : szOK n w = true) {m x v : Nat} {ub : List Nat}
    {cands : List (List Nat)} (hx : PP n w x) (hv : PP n w v) (hu : ∀ b ∈ ub, PP n w b)
    (hc : ∀ c ∈ cands, ∀ b ∈ c, PP n w b) :
    (inSpan n (ub.map (tabP n w)) (tabP n w v) ||
      !(elabOK n (ub.map (tabP n w) ++ orbTabs n m (tabP n w x) (invT n (tabP n w x)) (tabP n w v))) ||
      (cands.map (List.map (tabP n w))).any
        (orbIs n (ub.map (tabP n w) ++ orbTabs n m (tabP n w x) (invT n (tabP n w x)) (tabP n w v)))) =
      pframeOne n w m x ub cands v := by
  have hl : ∀ s ∈ ub ++ porbTabs n w m x (pinv n w x) v, PP n w s := by
    intro s hs
    rcases List.mem_append.1 hs with h | h
    · exact hu s h
    · exact PP_porbTabs hx hx.pinv hv s h
  rw [invT_tabP hx, orbTabs_tabP hx hx.pinv hv, ← List.map_append, inSpan_tabP hsz hu hv,
    elabOK_tabP hl, pframeOne]
  congr 1
  exact any_map_congr fun c hcc => orbIs_tabP hsz hl (hc c hcc)

theorem ebasisOK_tabP (hsz : szOK n w = true) {bs : List Nat} (h : ∀ b ∈ bs, PP n w b) :
    ebasisOK n (bs.map (tabP n w)) = pebasis n w bs := by
  rw [ebasisOK, pebasis, List.length_map]
  congr 1
  · congr 1
    · exact all_map_congr fun b hb => by
        rw [compT_tabP' (h b hb) (h b hb), idT_tabP hsz,
          tblEq_tabP ((h b hb).pc (h b hb)) (PP.id hsz)]
    · exact all_map_congr fun b hb => all_map_congr fun c hc => commT_tabP (h b hb) (h c hc)
  · refine all_congr' fun m _ => ?_
    rw [maskProd_tabP hsz bs h m, idT_tabP hsz, tblEq_tabP (PP_pmask hsz bs h m) (PP.id hsz)]

end CFSG.KC.KGC31P

end
