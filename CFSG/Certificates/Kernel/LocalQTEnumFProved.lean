module

public import CFSG.Certificates.Kernel.LocalQTEnumWProved
public import Certificates.Data.Kernel.LocalQT.RankF

public section

namespace CFSG.KC.LQT.RF.Pf

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.RW CFSG.KC.LQT.RF
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BW.Cl
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem ofFnW_congr (w : Nat) {f g : Nat → Nat} : ∀ m, (∀ j < m, f j = g j) →
    ofFnW m w f = ofFnW m w g
  | 0, _ => rfl
  | m + 1, h => by
    have e : ∀ f : Nat → Nat, ofFnW (m + 1) w f = ofFnW m w f ||| (f m <<< (w * m)) :=
      fun _ => rfl
    rw [e, e, ofFnW_congr w m (fun j hj => h j (by omega)), h m (by omega)]

theorem testBit_codeK_hi {w : Nat} : ∀ (l : List Nat), (∀ x ∈ l, x < 2 ^ w) →
    ∀ p, w * l.length ≤ p → (codeK w l).testBit p = false
  | [], _, p, _ => by
    have e : codeK w [] = 0 := rfl
    rw [e, Nat.zero_testBit]
  | x :: t, hl, p, hp => by
    have e : codeK w (x :: t) = 2 ^ w * codeK w t + x := by
      change Nat.add x (Nat.shiftLeft (codeK w t) w) = _
      change x + (codeK w t <<< w) = _
      rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]
    have hx := hl x (List.mem_cons_self ..)
    rw [e, Nat.testBit_two_pow_mul_add _ hx]
    simp only [List.length_cons, Nat.mul_succ] at hp
    have hpw : ¬ p < w := by
      have : w ≤ w * t.length + w := Nat.le_add_left _ _
      omega
    simp only [hpw, ite_false]
    exact testBit_codeK_hi t (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _ (by omega)

theorem testBit_ofFnW_hi {w m : Nat} {f : Nat → Nat} (hf : ∀ j < m, f j < 2 ^ w) {p : Nat}
    (hp : w * m ≤ p) : (ofFnW m w f).testBit p = false := by
  rw [testBit_ofFnW]
  apply Bool.eq_false_iff.2
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨j, hj, h⟩ := h
  rw [List.mem_range] at hj
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  have hle : w * (j + 1) ≤ w * m := Nat.mul_le_mul_left _ hj
  rw [Nat.mul_succ] at hle
  rw [testBit_lt (hf j hj) (by omega)] at h
  exact Bool.false_ne_true h.2

theorem code_ext {w m x y : Nat} (hx : ∀ p, w * m ≤ p → x.testBit p = false)
    (hy : ∀ p, w * m ≤ p → y.testBit p = false) (h : ∀ j < m, imgW w x j = imgW w y j) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : w * m ≤ p
  · rw [hx p hp, hy p hp]
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · rw [h0, Nat.zero_mul] at hp
        omega
      · exact h0
    have hj : p / w < m := by
      rw [Nat.div_lt_iff_lt_mul hw]
      rw [Nat.mul_comm] at hp
      omega
    have e := congrArg (fun z => z.testBit (p % w)) (h (p / w) hj)
    simp only [testBit_imgW, Nat.mod_lt _ hw, decide_true, Bool.true_and] at e
    rwa [Nat.div_add_mod] at e

theorem codeK_eq_ofFnW {w : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ w) :
    codeK w l = ofFnW l.length w fun j => l.getD j 0 := by
  have hf : ∀ j < l.length, l.getD j 0 < 2 ^ w := fun j hj => hl _ (getD_mem hj)
  apply code_ext (testBit_codeK_hi l hl) (fun p hp => testBit_ofFnW_hi hf hp)
  intro j hj
  rw [imgW_codeK l hl j hj, imgW_ofFnW hf hj]

theorem keyW_eq_ofFnW {n w : Nat} {T : List Nat} (hT : ∀ x ∈ T, x < 2 ^ w) (hn : n ≤ T.length) :
    keyW w n T = ofFnW n w fun j => T.getD j 0 := by
  rw [keyW, takeK_eq, codeK_eq_ofFnW (take_lt hT n), List.length_take, Nat.min_eq_left hn]
  apply ofFnW_congr
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

theorem keyW_imgs {n w g : Nat} {T : List Nat} (hT : ∀ x ∈ T, x < 2 ^ w) (hn : n ≤ T.length) :
    keyW w n (imgsW w g T) = mulW n w g (keyW w n T) := by
  have hT' : ∀ x ∈ imgsW w g T, x < 2 ^ w := by
    intro x hx
    rw [imgsW_eq, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact imgW_lt _ _ _
  have hn' : n ≤ (imgsW w g T).length := by rw [imgsW_eq, List.length_map]; exact hn
  rw [keyW_eq_ofFnW hT' hn', keyW_eq_ofFnW hT hn, mulW]
  apply ofFnW_congr
  intro j hj
  rw [imgW_ofFnW (fun i hi => hT _ (getD_mem (by omega))) hj, imgsW_eq,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega),
    Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some]

@[expose] def eraseT : TT → TT
  | .lf => .lf
  | .nd l k v _ r => .nd (eraseT l) k v [] (eraseT r)

theorem memG_erase (lt : Nat → Nat → Bool) (x : Nat) : ∀ t : TT,
    memG lt (eraseT t) x = memG lt t x
  | .lf => rfl
  | .nd l k v T r => by
    change memG lt (.nd (eraseT l) k v [] (eraseT r)) x = _
    rw [memG_nd, memG_nd, memG_erase lt x l, memG_erase lt x r]

theorem idxG_erase (lt : Nat → Nat → Bool) (x : Nat) : ∀ t : TT,
    idxG lt (eraseT t) x = idxG lt t x
  | .lf => rfl
  | .nd l k v T r => by
    change idxG lt (.nd (eraseT l) k v [] (eraseT r)) x = _
    rw [idxG_nd, idxG_nd, idxG_erase lt x l, idxG_erase lt x r]

theorem insG_erase (lt : Nat → Nat → Bool) (x v : Nat) (T : List Nat) : ∀ t : TT,
    eraseT (insG lt t x v T) = insG lt (eraseT t) x v []
  | .lf => rfl
  | .nd l k u U r => by
    change _ = insG lt (.nd (eraseT l) k u [] (eraseT r)) x v []
    rw [insG_nd, insG_nd]
    cases Nat.beq x k
    · dsimp only
      cases lt x k
      · dsimp only
        change TT.nd (eraseT l) k u [] (eraseT (insG lt r x v T)) = _
        rw [insG_erase lt x v T r]
      · dsimp only
        change TT.nd (eraseT (insG lt l x v T)) k u [] (eraseT r) = _
        rw [insG_erase lt x v T l]
    · rfl

theorem memTT_erase (t : TT) (x : Nat) : memTT (eraseT t) x = memTT t x := by
  rw [memTT_eq, memTT_eq, memG_erase]

theorem idxTT_erase (t : TT) (x : Nat) : idxTT (eraseT t) x = idxTT t x := by
  rw [idxTT_eq, idxTT_eq, idxG_erase]

theorem insTT_erase (t : TT) (x v : Nat) (T : List Nat) :
    eraseT (insTT t x v T) = insTT (eraseT t) x v [] := by
  rw [insTT_eq, insTT_eq, insG_erase]

@[expose] noncomputable def projF (w n : Nat) (es : ES) : EF :=
  EF.mk (eraseT es.kt) es.cnt es.par es.cl (es.fr.map (keyW w n))

theorem letF_eq (y : Nat) (k : Nat → EF) : letF y k = k y := by cases y <;> rfl

theorem kidsF_nil (n w i x : Nat) (st : EF) : kidsF n w [] i x st = st := rfl

theorem kidsF_cons (n w s : Nat) (G : List Nat) (i x : Nat) (st : EF) :
    kidsF n w (s :: G) i x st = kidsF n w G i x
      (if memTT st.kt (mulW n w s x) = true
        then EF.mk st.kt st.cnt st.par (idxTT st.kt (mulW n w s x) :: st.cl) st.fr
        else EF.mk (insTT st.kt (mulW n w s x) st.cnt []) (st.cnt + 1) (i :: st.par)
          (st.cnt :: st.cl) (mulW n w s x :: st.fr)) := by
  have e : kidsF n w (s :: G) i x st = letF (mulW n w s x) fun c =>
      kidsF n w G i x (Bool.rec (motive := fun _ => EF)
        (letF (Nat.succ st.cnt) fun cnt' =>
          EF.mk (insTT st.kt c st.cnt []) cnt' (List.cons i st.par) (List.cons st.cnt st.cl)
            (List.cons c st.fr))
        (letF (idxTT st.kt c) fun j => EF.mk st.kt st.cnt st.par (List.cons j st.cl) st.fr)
        (memTT st.kt c)) := rfl
  rw [e, letF_eq]
  congr 1
  cases memTT st.kt (mulW n w s x)
  · simp only [Bool.false_eq_true, ite_false]
    rw [letF_eq]
  · simp only [ite_true]
    rw [letF_eq]

@[expose] def VW (w n : Nat) (T : List Nat) : Prop := (∀ x ∈ T, x < 2 ^ w) ∧ n ≤ T.length

theorem vw_imgs {w n g : Nat} {T : List Nat} (h : VW w n T) : VW w n (imgsW w g T) := by
  refine ⟨fun x hx => ?_, by rw [imgsW_eq, List.length_map]; exact h.2⟩
  rw [imgsW_eq, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact imgW_lt _ _ _

theorem kids_proj {w n : Nat} {i : Nat} {T : List Nat} (hT : VW w n T) : ∀ (Gc : List Nat) (es : ES),
    projF w n (kidsW w n (imgsW w) Gc i T es) = kidsF n w Gc i (keyW w n T) (projF w n es)
  | [], es => rfl
  | s :: Gc, es => by
    rw [kidsW_cons, kidsF_cons, kids_proj hT Gc]
    congr 1
    rw [keyW_imgs hT.1 hT.2]
    unfold projF
    rw [memTT_erase]
    cases memTT es.kt (mulW n w s (keyW w n T))
    · simp only [Bool.false_eq_true, ite_false, newE, insTT_erase, List.map_cons,
        keyW_imgs hT.1 hT.2]
    · simp only [ite_true, foundE, idxTT_erase]

theorem roundF_nil (n w gi : Nat) (G : List Nat) (i : Nat) (st : EF) :
    roundF n w gi G [] i st = st := rfl

theorem roundF_cons (n w gi : Nat) (G : List Nat) (x : Nat) (F : List Nat) (i : Nat) (st : EF) :
    roundF n w gi G (x :: F) i st = roundF n w gi G F (i + 1)
      ((fun (st' : EF) => EF.mk st'.kt st'.cnt st'.par (zerosOn gi st'.cl) st'.fr)
        (kidsF n w G i x st)) := by
  have e : roundF n w gi G (x :: F) i st = letF (Nat.succ i) fun i' => roundF n w gi G F i'
      ((fun (st' : EF) => EF.mk st'.kt st'.cnt st'.par (zerosOn gi st'.cl) st'.fr)
        (kidsF n w G i x st)) := rfl
  rw [e, letF_eq]

theorem round_proj {w n gi : Nat} (Gc : List Nat) : ∀ (F : List (List Nat)) (i : Nat) (es : ES),
    (∀ T ∈ F, VW w n T) →
    projF w n (roundW w n gi (imgsW w) Gc F i es) =
      roundF n w gi Gc (F.map (keyW w n)) i (projF w n es)
  | [], _, _, _ => rfl
  | T :: F, i, es, hF => by
    rw [roundW_cons, List.map_cons, roundF_cons,
      round_proj Gc F (i + 1) _ (fun U hU => hF U (List.mem_cons_of_mem _ hU)),
      ← kids_proj (hF T (List.mem_cons_self ..)) Gc es]
    rfl

theorem enumF_succ (n w gi : Nat) (G : List Nat) (dd : Nat) (st : EF) (i : Nat) (F : List Nat)
    (h : enumF n w gi G dd = (st, i, F)) :
    enumF n w gi G (dd + 1) =
      ((fun (st' : EF) => (EF.mk st'.kt st'.cnt st'.par st'.cl [], st.cnt, revOn st'.fr []))
        (roundF n w gi G F i (EF.mk st.kt st.cnt st.par st.cl []))) := by
  have e : enumF n w gi G (dd + 1) =
      Prod.rec (motive := fun _ => EF × Nat × List Nat) (fun st p =>
        Prod.rec (motive := fun _ => EF × Nat × List Nat) (fun i F =>
          (fun (st' : EF) => Prod.mk (EF.mk st'.kt st'.cnt st'.par st'.cl [])
              (Prod.mk st.cnt (revOn st'.fr [])))
            (roundF n w gi G F i (EF.mk st.kt st.cnt st.par st.cl []))) p)
        (enumF n w gi G dd) := rfl
  rw [e, h]

theorem enumF_proj {n w : Nat} (hw : n ≤ 2 ^ w) {G : List (Array Nat)} {gi : Nat}
    {Gp : List (Nat × Array Nat)} (hG : ∀ p ∈ Gp, Rep n w p.1 p.2 ∧ p.2 ∈ G)
    (hGs : Gp.map Prod.snd = G) : ∀ dd,
    projF w n (enumW w n gi (imgsW w) (Gp.map Prod.fst) (ptsOf (List.range n) G) dd).1 =
        (enumF n w gi (Gp.map Prod.fst) dd).1 ∧
      (enumW w n gi (imgsW w) (Gp.map Prod.fst) (ptsOf (List.range n) G) dd).2.1 =
        (enumF n w gi (Gp.map Prod.fst) dd).2.1 ∧
      (enumW w n gi (imgsW w) (Gp.map Prod.fst) (ptsOf (List.range n) G) dd).2.2.map
        (keyW w n) = (enumF n w gi (Gp.map Prod.fst) dd).2.2 := by
  have hGrep : ∀ s ∈ G, ∃ c, Rep n w c s := by
    intro s hs
    rw [← hGs, List.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨p.1, (hG p hp).1⟩
  have hov : Val n (ptsOf (List.range n) G).length (ptsOf (List.range n) G) := by
    refine ⟨rfl, fun x hx => ?_⟩
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact List.mem_range.1 hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hGrep s hs
      exact (hc.2 b (List.mem_range.1 hb)).1
  have hlen : n ≤ (ptsOf (List.range n) G).length := by
    rw [ptsOf, List.length_append, List.length_range]
    omega
  have hvw : ∀ {T}, Val n (ptsOf (List.range n) G).length T → VW w n T := fun hT =>
    ⟨fun x hx => Nat.lt_of_lt_of_le (hT.2 x hx) hw, by rw [hT.1]; exact hlen⟩
  have hone : keyW w n (ptsOf (List.range n) G) = oneW n w := by
    rw [keyW_eq_ofFnW (hvw hov).1 hlen, oneW]
    apply ofFnW_congr
    intro j hj
    rw [ptsOf, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_range hj, Option.getD_some]
  intro dd
  induction dd with
  | zero =>
    rw [enumW_zero]
    refine ⟨?_, rfl, ?_⟩
    · change EF.mk (eraseT (insTT TT.lf _ 0 _)) 1 [0] [] [] = _
      rw [insTT_erase, hone]
      rfl
    · change [keyW w n (ptsOf (List.range n) G)] = [oneW n w]
      rw [hone]
  | succ dd ih =>
    obtain ⟨S, hc, -, hF, -, -, -, -⟩ := enum_corr (nb := n) (gi := gi) hw hG hGs hov dd
    rcases hE : enumW w n gi (imgsW w) (Gp.map Prod.fst) (ptsOf (List.range n) G) dd with
      ⟨st, i, F⟩
    rw [hE] at hc hF ih
    dsimp only at hc hF ih
    obtain ⟨ih1, ih2, ih3⟩ := ih
    rcases hEF : enumF n w gi (Gp.map Prod.fst) dd with ⟨stf, i', F'⟩
    rw [hEF] at ih1 ih2 ih3
    dsimp only at ih1 ih2 ih3
    subst ih2 ih3
    rw [enumW_succ w n gi (imgsW w) (Gp.map Prod.fst) _ dd st i F hE,
      enumF_succ n w gi (Gp.map Prod.fst) dd stf i _ hEF]
    have hFv : ∀ T ∈ F, VW w n T := by
      intro T hT
      rw [hF] at hT
      exact hvw (hc.2.2.2.2.1 T (List.mem_of_mem_drop hT))
    have hpr : projF w n (ES.mk st.kt st.cnt st.rev st.par st.cl [] st.ok) =
        EF.mk stf.kt stf.cnt stf.par stf.cl [] := by
      rw [← ih1]
      rfl
    have hround := round_proj (gi := gi) (Gp.map Prod.fst) F i
      (ES.mk st.kt st.cnt st.rev st.par st.cl [] st.ok) hFv
    rw [hpr] at hround
    refine ⟨?_, ?_, ?_⟩
    · dsimp only
      rw [← hround]
      rfl
    · dsimp only
      rw [← ih1]
      rfl
    · dsimp only
      rw [← hround]
      change List.map (keyW w n) (revOn _ []) = revOn (List.map (keyW w n) _) []
      rw [revOn_eq, revOn_eq, List.append_nil, List.append_nil, List.map_reverse]

@[expose] def Form (o T : List Nat) : Prop := T = o.map fun p => T.getD p 0

section Ok

variable {n w : Nat} {G : List (Array Nat)}

theorem form_apply {o T : List Nat} (h : Form o T) (ho : ∀ p ∈ o, p < T.length) (s : Array Nat) :
    Form o (applyTab s T) := by
  have hg : ∀ p ∈ o, (applyTab s T).getD p 0 = img s (T.getD p 0) := by
    intro p hp
    rw [applyTab, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (ho p hp), Option.map_some, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (ho p hp), Option.getD_some]
  have e : o.map (fun p => img s (T.getD p 0)) = (o.map fun p => T.getD p 0).map (img s) := by
    rw [List.map_map]
    rfl
  unfold Form at h ⊢
  rw [List.map_congr_left hg, e, ← h]
  rfl

theorem form_eq {o T U : List Nat} (hT : Form o T) (hU : Form o U)
    (h : ∀ p ∈ o, T.getD p 0 = U.getD p 0) : T = U := by
  rw [hT, hU]
  exact List.map_congr_left h

@[expose] def OkI (w n L : Nat) (o : List Nat) (es : ES) : Prop :=
  es.ok = true ∧ OrdT es.kt ∧
  (∀ y, memKT es.kt y → Form o (tabG ltK es.kt y) ∧ keyW w n (tabG ltK es.kt y) = y ∧
    Val n L (tabG ltK es.kt y)) ∧
  (∀ T ∈ es.rev, Form o T ∧ Val n L T)

variable {L : Nat} {o : List Nat}

theorem take_eq_form {T U : List Nat} (hT : Form o T) (hU : Form o U) (hon : ∀ p ∈ o, p < n)
    (h : T.take n = U.take n) : T = U := by
  apply form_eq hT hU
  intro p hp
  have hpn := hon p hp
  have e := congrArg (fun l => l.getD p 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hpn] at e
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  exact e

theorem step_ok (hw : n ≤ 2 ^ w) (hon : ∀ p ∈ o, p < n) (hnL : n ≤ L) {es : ES}
    (hc : OkI w n L o es) {T : List Nat} (hT : T ∈ es.rev) {g : Nat} {s : Array Nat}
    (hg : Rep n w g s) (i : Nat) :
    OkI w n L o (if memTT es.kt (keyW w n (imgsW w g T)) = true
        then foundE es (keyW w n (imgsW w g T)) (imgsW w g T)
        else newE i es (keyW w n (imgsW w g T)) (imgsW w g T)) ∧
    ∀ U ∈ es.rev, U ∈ (if memTT es.kt (keyW w n (imgsW w g T)) = true
        then foundE es (keyW w n (imgsW w g T)) (imgsW w g T)
        else newE i es (keyW w n (imgsW w g T)) (imgsW w g T)).rev := by
  obtain ⟨hok, ho, hkt, hrev⟩ := hc
  obtain ⟨hTf, hTv⟩ := hrev T hT
  rw [imgsW_rep hg hTv.2]
  have hcv : Val n L (applyTab s T) :=
    ⟨by rw [applyTab, List.length_map]; exact hTv.1, applyTab_lt hg hTv.2⟩
  have hcf : Form o (applyTab s T) :=
    form_apply hTf (fun p hp => by rw [hTv.1]; exact Nat.lt_of_lt_of_le (hon p hp) hnL) s
  generalize applyTab s T = c at hcv hcf
  by_cases hf : memTT es.kt (keyW w n c) = true
  · rw [ite_eq_left hf]
    have hm : memKT es.kt (keyW w n c) := by
      rw [memTT_eq, memG_iff ltK_iff ho] at hf
      exact hf
    obtain ⟨h1, h2, h3⟩ := hkt _ hm
    have htab : tabG ltK es.kt (keyW w n c) = c :=
      take_eq_form h1 hcf hon ((keyW_eq_iff hw h3 hcv).1 h2)
    refine ⟨⟨?_, ho, hkt, hrev⟩, fun U hU => hU⟩
    simp only [foundE, hok, Bool.true_and]
    rw [eqLW_iff, tabTT_eq, htab]
  · rw [ite_eq_right hf]
    have hnot : ¬ memKT es.kt (keyW w n c) := fun h =>
      hf (by rw [memTT_eq]; exact (memG_iff ltK_iff ho _).2 h)
    refine ⟨⟨hok, ?_, fun y hy => ?_, fun U hU => ?_⟩, fun U hU => List.mem_cons_of_mem _ hU⟩
    · simp only [newE]
      rw [insTT_eq]
      exact ord_insG ltK_iff _ _ _ ho
    · simp only [newE] at hy ⊢
      rw [insTT_eq] at hy ⊢
      rcases (mem_insG ltK_iff _ _ _ _ _).1 hy with rfl | hy
      · rw [(look_insG_self _ _ _ hnot).2]
        exact ⟨hcf, rfl, hcv⟩
      · have hne : y ≠ keyW w n c := fun e => hnot (e ▸ hy)
        rw [(look_insG_ne _ _ _ hne _).2]
        exact hkt y hy
    · simp only [newE, List.mem_cons] at hU
      rcases hU with rfl | hU
      · exact ⟨hcf, hcv⟩
      · exact hrev U hU

theorem kids_ok (hw : n ≤ 2 ^ w) (hon : ∀ p ∈ o, p < n) (hnL : n ≤ L) {i : Nat} {T : List Nat} :
    ∀ (Gp : List (Nat × Array Nat)) (es : ES), (∀ p ∈ Gp, Rep n w p.1 p.2) → OkI w n L o es →
    T ∈ es.rev → OkI w n L o (kidsW w n (imgsW w) (Gp.map Prod.fst) i T es) ∧
      ∀ U ∈ es.rev, U ∈ (kidsW w n (imgsW w) (Gp.map Prod.fst) i T es).rev
  | [], es, _, hc, _ => ⟨hc, fun U hU => hU⟩
  | p :: Gp, es, hG, hc, hT => by
    rw [List.map_cons, kidsW_cons]
    obtain ⟨hc1, hm1⟩ := step_ok hw hon hnL hc hT (hG p (List.mem_cons_self ..)) i
    obtain ⟨hc2, hm2⟩ := kids_ok hw hon hnL Gp _ (fun q hq => hG q (List.mem_cons_of_mem _ hq))
      hc1 (hm1 T hT)
    exact ⟨hc2, fun U hU => hm2 U (hm1 U hU)⟩

theorem round_ok (hw : n ≤ 2 ^ w) (hon : ∀ p ∈ o, p < n) (hnL : n ≤ L) {gi : Nat}
    {Gp : List (Nat × Array Nat)} (hG : ∀ p ∈ Gp, Rep n w p.1 p.2) :
    ∀ (F : List (List Nat)) (i : Nat) (es : ES), OkI w n L o es → (∀ T ∈ F, T ∈ es.rev) →
    OkI w n L o (roundW w n gi (imgsW w) (Gp.map Prod.fst) F i es)
  | [], _, _, hc, _ => hc
  | T :: F, i, es, hc, hF => by
    rw [roundW_cons]
    obtain ⟨hc1, hm1⟩ := kids_ok (i := i) hw hon hnL Gp es hG hc (hF T (List.mem_cons_self ..))
    exact round_ok hw hon hnL hG F (i + 1) _ hc1
      (fun U hU => hm1 U (hF U (List.mem_cons_of_mem _ hU)))

theorem enum_ok (hw : n ≤ 2 ^ w) {G : List (Array Nat)} {gi : Nat} {Gp : List (Nat × Array Nat)}
    (hG : ∀ p ∈ Gp, Rep n w p.1 p.2 ∧ p.2 ∈ G) (hGs : Gp.map Prod.snd = G)
    (hov : Val n (ptsOf (List.range n) G).length (ptsOf (List.range n) G))
    (hoid : ∀ p ∈ ptsOf (List.range n) G, (ptsOf (List.range n) G).getD p 0 = p)
    (hnL : n ≤ (ptsOf (List.range n) G).length) : ∀ dd,
    OkI w n (ptsOf (List.range n) G).length (ptsOf (List.range n) G)
      (enumW w n gi (imgsW w) (Gp.map Prod.fst) (ptsOf (List.range n) G) dd).1
  | 0 => by
    rw [enumW_zero]
    have hform : Form (ptsOf (List.range n) G) (ptsOf (List.range n) G) := by
      unfold Form
      conv_lhs => rw [← List.map_id (ptsOf (List.range n) G)]
      exact List.map_congr_left fun p hp => (hoid p hp).symm
    refine ⟨rfl, ?_, fun y hy => ?_, fun T hT => ?_⟩
    · change OrdT (insTT TT.lf _ 0 _)
      rw [insTT_eq]
      exact ord_insG ltK_iff _ _ _ trivial
    · change memKT (insTT TT.lf _ 0 _) y at hy
      change Form _ (tabG ltK (insTT TT.lf _ 0 _) y) ∧ keyW w n (tabG ltK (insTT TT.lf _ 0 _) y) = y ∧
        Val n _ (tabG ltK (insTT TT.lf _ 0 _) y)
      rw [insTT_eq] at hy ⊢
      rcases (mem_insG ltK_iff _ _ _ _ _).1 hy with rfl | hy
      · have hn : ¬ memKT TT.lf (keyW w n (ptsOf (List.range n) G)) := fun h => h
        rw [(look_insG_self _ _ _ hn).2]
        exact ⟨hform, rfl, hov⟩
      · exact absurd hy (fun h => h)
    · change T ∈ [ptsOf (List.range n) G] at hT
      rw [List.mem_singleton] at hT
      rw [hT]
      exact ⟨hform, hov⟩
  | dd + 1 => by
    have hon : ∀ p ∈ ptsOf (List.range n) G, p < n := hov.2
    obtain ⟨S, hc, -, hF, -, -, -, -⟩ := enum_corr (nb := n) (gi := gi) hw hG hGs hov dd
    have ih := enum_ok (gi := gi) hw hG hGs hov hoid hnL dd
    rcases hE : enumW w n gi (imgsW w) (Gp.map Prod.fst) (ptsOf (List.range n) G) dd with
      ⟨st, i, F⟩
    rw [hE] at hc hF ih
    dsimp only at hc hF ih
    rw [enumW_succ w n gi (imgsW w) (Gp.map Prod.fst) _ dd st i F hE]
    have hr : S.1.toList = st.rev.reverse := hc.1
    rw [hr] at hF
    exact round_ok hw hon hnL (fun p hp => (hG p hp).1) F i _ ih (fun T hT => by
      rw [hF] at hT
      exact List.mem_reverse.1 (List.mem_of_mem_drop hT))

end Ok

end CFSG.KC.LQT.RF.Pf

end
