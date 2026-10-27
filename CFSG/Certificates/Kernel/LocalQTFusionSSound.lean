module

public import CFSG.Certificates.Kernel.LocalQTFusionSReg

public section

namespace CFSG.KC.LQT.FS.Pf

open CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS CFSG.KC.LQT.RW CFSG.KC.LQT.RB
open CFSG.KC.LQT.FS CFSG.KC.LQT.FB CFSG.KC.LQT.BSP
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BS.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2 CFSG.QuasithinUnique.Lin2.RankCert
open CFSG.QuasithinUnique.Lin2.FusionCert
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem mulG_spec' {N g gi : Nat} {par cl : Array Nat} {fP fC : Nat → Nat}
    (hfP : ∀ i < N, 0 < i → fP i = par[i]!)
    (hfC : ∀ i < N, ∀ j < g, fC (i * (g + gi) + j) = cl[i * (g + gi) + j]!)
    (hpar : ∀ i < N, 0 < i → par[i]! < i ∧ 0 < g)
    (hcl : ∀ i < N, ∀ j < g, cl[i * (g + gi) + j]! < N) :
    ∀ f i k, i < N → k < N →
      mulG fP fC g (g + gi) f i k = mulIdx g gi par cl f i k ∧ mulIdx g gi par cl f i k < N := by
  intro f
  induction f with
  | zero => intro i k _ hk; exact ⟨rfl, hk⟩
  | succ f ih =>
    intro i k hi hk
    by_cases hi0 : i = 0
    · subst hi0
      exact ⟨rfl, by simp [mulIdx, hk]⟩
    · obtain ⟨hp, hg⟩ := hpar i hi (Nat.pos_of_ne_zero hi0)
      obtain ⟨e1, h1⟩ := ih par[i]! k (by omega) hk
      have hgen : genG fP fC g (g + gi) i = genIdx g gi par cl i := by
        rw [genG, genIdx, hfP i hi (Nat.pos_of_ne_zero hi0)]
        apply findW_eq
        intro j hj
        rw [nbeq_eq]
        change (fC (par[i]! * (g + gi) + j) == i) = _
        rw [hfC _ (by omega) j hj]
      have hglt : genIdx g gi par cl i < g := by
        rw [genIdx]
        exact find_getD_lt hg _
      have e : mulG fP fC g (g + gi) (f + 1) i k =
          fC (mulG fP fC g (g + gi) f (fP i) k * (g + gi) + genG fP fC g (g + gi) i) := by
        change Bool.rec (motive := fun _ => Nat) _ k (Nat.beq i 0) = _
        rw [beq_false hi0]
        rfl
      have e2 : mulIdx g gi par cl (f + 1) i k =
          cl[mulIdx g gi par cl f par[i]! k * (g + gi) + genIdx g gi par cl i]! := by
        simp [mulIdx, hi0]
      rw [e, e2, hfP i hi (Nat.pos_of_ne_zero hi0), e1, hgen, hfC _ h1 _ hglt]
      exact ⟨rfl, hcl _ h1 _ hglt⟩

theorem img_range {n i : Nat} (hi : i < n) : img (Array.range n) i = i := by
  simp [img, hi]

theorem rep_one {n w : Nat} (hw : n ≤ 2 ^ w) : Rep n w (oneW n w) (Array.range n) := by
  refine ⟨Array.size_range, fun i hi => ?_⟩
  rw [img_range hi, oneW, imgW_ofFnW (fun j hj => by omega) hi]
  exact ⟨hi, rfl⟩

theorem idx_rep {n w W g M : Nat} (hw : n ≤ 2 ^ w) {PT CT : Nat → Nat} {Gc : List Nat}
    {G : List (Array Nat)} {par cl : Array Nat}
    (hGrep : ∀ j < g, Rep n w (genW n w Gc j) (G.getD j #[]))
    (hfP : ∀ i < M, 0 < i → fieldT W PT i = par[i]!)
    (hfC : ∀ i < M, ∀ j < g, fieldT W CT (i * (g + g) + j) = cl[i * (g + g) + j]!)
    (hpar : ∀ i < M, 0 < i → par[i]! < i ∧ 0 < g) :
    ∀ f i, i < M → Rep n w (idxW n w W g PT CT Gc f i) (idxTab n G g g par cl f i) := by
  intro f
  induction f with
  | zero =>
    intro i _
    exact rep_one hw
  | succ f ih =>
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      have e1 : idxW n w W g PT CT Gc (f + 1) 0 = oneW n w := rfl
      have e2 : idxTab n G g g par cl (f + 1) 0 = Array.range n := by simp [idxTab]
      rw [e1, e2]
      exact rep_one hw
    · obtain ⟨hp, hg⟩ := hpar i hi (Nat.pos_of_ne_zero hi0)
      have hgen : genIdxT W g (Nat.add g g) PT CT i = genIdx g g par cl i := by
        rw [genIdxT, genIdx, hfP i hi (Nat.pos_of_ne_zero hi0)]
        apply findW_eq
        intro j hj
        rw [nbeq_eq]
        change (fieldT W CT (par[i]! * (g + g) + j) == i) = _
        rw [hfC _ (by omega) j hj]
      have hglt : genIdx g g par cl i < g := by
        rw [genIdx]
        exact find_getD_lt hg _
      have e1 : idxW n w W g PT CT Gc (f + 1) i =
          mulW n w (genW n w Gc (genIdxT W g (Nat.add g g) PT CT i))
            (idxW n w W g PT CT Gc f (fieldT W PT i)) := by
        change Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq i 0) = _
        rw [beq_false hi0]
        exact letN_eq _ _
      have e2 : idxTab n G g g par cl (f + 1) i =
          compArr (G.getD (genIdx g g par cl i) #[]) (idxTab n G g g par cl f par[i]!) := by
        simp [idxTab, hi0]
      rw [e1, e2, hgen, hfP i hi (Nat.pos_of_ne_zero hi0)]
      exact rep_mul (hGrep _ hglt) (ih _ (by omega))

@[expose] def ev (a b : Array Nat) (l : List Nat) (p : Nat) : Nat :=
  l.foldr (fun x acc => img (if x = 0 then a else b) acc) p

theorem ev_nil (a b : Array Nat) (p : Nat) : ev a b [] p = p := rfl

theorem ev_cons (a b : Array Nat) (x : Nat) (l : List Nat) (p : Nat) :
    ev a b (x :: l) p = img (if x = 0 then a else b) (ev a b l p) := rfl

theorem ev_append (a b : Array Nat) (l m : List Nat) (p : Nat) :
    ev a b (l ++ m) p = ev a b l (ev a b m p) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.cons_append, ev_cons, ev_cons, ih]

theorem wordTab_img {n : Nat} {a b : Array Nat} (ha : a.size = n ∧ ∀ i < n, img a i < n)
    (hb : b.size = n ∧ ∀ i < n, img b i < n) :
    ∀ l : List Nat, (wordTab n a b l).size = n ∧
      ∀ p < n, img (wordTab n a b l) p = ev a b l p ∧ ev a b l p < n := by
  intro l
  induction l with
  | nil =>
    refine ⟨Array.size_range, fun p hp => ?_⟩
    rw [ev_nil]
    exact ⟨img_range hp, hp⟩
  | cons x l ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e : wordTab n a b (x :: l) =
        compArr (if x = 0 then a else b) (wordTab n a b l) := rfl
    have hx : (if x = 0 then a else b).size = n ∧ ∀ i < n, img (if x = 0 then a else b) i < n := by
      split
      · exact ha
      · exact hb
    rw [e]
    refine ⟨by simp [compArr, ih1], fun p hp => ?_⟩
    have htl : ∀ i < n, img (wordTab n a b l) i < n := fun i hi => by
      rw [(ih2 i hi).1]
      exact (ih2 i hi).2
    rw [img_compArr hx.1 ih1 htl hp, (ih2 p hp).1, ← ev_cons]
    exact ⟨rfl, hx.2 _ (ih2 p hp).2⟩

@[expose] def FR (n w c : Nat) (f : Nat → Nat) : Prop := ∀ q < n, imgW w c q = f q ∧ f q < n

theorem fr_one {n w : Nat} (hw : n ≤ 2 ^ w) : FR n w (oneW n w) (fun p => p) := by
  intro q hq
  rw [oneW, imgW_ofFnW (fun j hj => by omega) hq]
  exact ⟨rfl, hq⟩

theorem fr_mul {n w : Nat} {c d : Nat} {f g : Nat → Nat} (hc : FR n w c f) (hd : FR n w d g) :
    FR n w (mulW n w c d) (fun p => f (g p)) := by
  intro q hq
  rw [mulW, imgW_ofFnW (fun j _ => imgW_lt _ _ _) hq, (hd q hq).1, (hc _ (hd q hq).2).1]
  exact ⟨rfl, (hc _ (hd q hq).2).2⟩

theorem fr_rep {n w c : Nat} {s : Array Nat} (h : Rep n w c s) : FR n w c (img s) := fun q hq =>
  ⟨(h.2 q hq).2, (h.2 q hq).1⟩

theorem fr_congr {n w c : Nat} {f g : Nat → Nat} (h : FR n w c f) (e : ∀ p < n, f p = g p) :
    FR n w c g := fun q hq => by
  rw [← e q hq]
  exact h q hq

theorem fr_eq {n w c d : Nat} {f : Nat → Nat} (hc : FR n w c f) (hd : FR n w d f) {q : Nat}
    (hq : q < n) : imgW w c q = imgW w d q := by
  rw [(hc q hq).1, (hd q hq).1]

theorem segW_fr {n w a b : Nat} {ta tb : Array Nat} (ha : FR n w a (img ta))
    (hb : FR n w b (img tb)) : ∀ (seg : List Nat) (acc : Nat) (f : Nat → Nat), FR n w acc f →
    FR n w (segW n w a b seg acc) (fun p => f (ev ta tb seg p)) := by
  intro seg
  induction seg with
  | nil =>
    intro acc f hf
    exact hf
  | cons x l ih =>
    intro acc f hf
    have e : segW n w a b (x :: l) acc =
        segW n w a b l (mulW n w acc (Bool.rec (motive := fun _ => Nat) b a (Nat.beq x 0))) :=
      letN_eq _ _
    rw [e]
    by_cases hx : x = 0
    · have hb0 : Nat.beq x 0 = true := by rw [hx]; rfl
      rw [hb0]
      have := ih _ _ (fr_mul hf ha)
      refine fr_congr this fun p hp => ?_
      rw [ev_cons]
      simp [hx]
    · have hb0 : Nat.beq x 0 = false := beq_false hx
      rw [hb0]
      have := ih _ _ (fr_mul hf hb)
      refine fr_congr this fun p hp => ?_
      rw [ev_cons]
      simp [hx]

theorem getLL_eq : ∀ (l : List (List Nat)) (i : Nat), getLL l i = l.getD i []
  | [], i => by simp [getLL]
  | x :: t, 0 => rfl
  | x :: t, i + 1 => by
    have e : getLL (x :: t) (i + 1) = getLL t i := rfl
    rw [e, getLL_eq t i, List.getD_cons_succ]

theorem getW_eq : ∀ (l : List (List Nat × List Nat × Nat)) (i : Nat),
    getW l i = l.getD i ([], [], 0)
  | [], i => by simp [getW]
  | x :: t, 0 => rfl
  | x :: t, i + 1 => by
    have e : getW (x :: t) (i + 1) = getW t i := rfl
    rw [e, getW_eq t i, List.getD_cons_succ]

theorem wordsOf_get : ∀ (wits : List (List Nat × List Nat × Nat)) (j : Nat) (hj : j < wits.length),
    getLL (wordsOf wits) (2 * j) = (wits[j]).1 ∧ getLL (wordsOf wits) (2 * j + 1) = (wits[j]).2.1
  | [], j, hj => by simp at hj
  | wt :: t, 0, _ => ⟨rfl, rfl⟩
  | wt :: t, j + 1, hj => by
    have := wordsOf_get t j (by simpa using hj)
    have e : wordsOf (wt :: t) = wt.1 :: wt.2.1 :: wordsOf t := rfl
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, e]
      exact this.1
    · rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by omega, e]
      exact this.2

theorem wordsOf_length : ∀ wits : List (List Nat × List Nat × Nat),
    (wordsOf wits).length = 2 * wits.length
  | [] => rfl
  | wt :: t => by
    have e : wordsOf (wt :: t) = wt.1 :: wt.2.1 :: wordsOf t := rfl
    rw [e, List.length_cons, List.length_cons, wordsOf_length t, List.length_cons]
    omega

theorem wordCk_spec {n w a b : Nat} {ws : List (List Nat)} {s R : Nat} {CP : Nat → Nat} {q : Nat}
    (h : wordCk n w a b ws s R CP q = true) :
    (q % R = 0 → CP (q / R * R) = oneW n w) ∧
    (q % R + 1 < R → CP (q + 1) =
      segW n w a b (sliceK (getLL ws (q / R)) (q % R * s) s) (CP q)) := by
  rw [wordCk] at h
  dsimp only at h
  rw [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun hc => P.beq_iff.1 (impB_true h1 (P.beq_iff.2 hc)),
    fun hc => P.beq_iff.1 (impB_true h2 (P.blt_iff.2 hc))⟩

theorem qdiv_mod {u R c : Nat} (hc : c < R) : (u * R + c) / R = u ∧ (u * R + c) % R = c := by
  have hR : 0 < R := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem ck_fr {n w a b : Nat} {ta tb : Array Nat} (hw : n ≤ 2 ^ w) (ha : FR n w a (img ta))
    (hb : FR n w b (img tb)) {ws : List (List Nat)} {s R : Nat} {CP : Nat → Nat}
    (hcp : ∀ q < ws.length * R, wordCk n w a b ws s R CP q = true) :
    ∀ u < ws.length, ∀ c, c < R →
      FR n w (CP (u * R + c)) (ev ta tb ((getLL ws u).take (c * s))) := by
  intro u hu c
  induction c with
  | zero =>
    intro hc
    have hq : u * R + 0 < ws.length * R := by
      calc u * R + 0 < (u + 1) * R := by rw [Nat.succ_mul]; omega
        _ ≤ ws.length * R := Nat.mul_le_mul_right _ hu
    obtain ⟨hd, hm⟩ := qdiv_mod (u := u) hc
    have := (wordCk_spec (hcp _ hq)).1 (by rw [Nat.add_zero] at hm ⊢; exact hm)
    rw [Nat.add_zero] at this ⊢
    rw [Nat.add_zero] at hd
    rw [hd] at this
    rw [this]
    have e : ev ta tb ((getLL ws u).take (0 * s)) = fun p => p := by
      funext p
      simp [ev_nil]
    rw [e]
    exact fr_one hw
  | succ c ih =>
    intro hc
    have hq : u * R + c < ws.length * R := by
      calc u * R + c < (u + 1) * R := by rw [Nat.succ_mul]; omega
        _ ≤ ws.length * R := Nat.mul_le_mul_right _ hu
    obtain ⟨hd, hm⟩ := qdiv_mod (u := u) (show c < R by omega)
    have h1 := (wordCk_spec (hcp _ hq)).2 (by rw [hm]; exact hc)
    rw [hd, hm] at h1
    have h2 := segW_fr ha hb (sliceK (getLL ws u) (c * s) s) _ _ (ih (by omega))
    rw [← h1, show u * R + c + 1 = u * R + (c + 1) by omega] at h2
    refine fr_congr h2 fun p hp => ?_
    rw [show (c + 1) * s = c * s + s by rw [Nat.succ_mul], List.take_add, ← ev_append]
    rfl

theorem recMap (f : Nat → Nat) : ∀ l : List Nat,
    List.rec (motive := fun _ => List Nat) [] (fun p _ ih => List.cons (f p) ih) l = l.map f
  | [] => rfl
  | x :: t => by
    change f x :: List.rec (motive := fun _ => List Nat) [] (fun p _ ih => List.cons (f p) ih) t = _
    rw [recMap f t, List.map_cons]

theorem witOK_of {n w : Nat} (hw : n ≤ 2 ^ w) {ta tb zt : Array Nat} {B : List Nat}
    {qp : List (Nat × Nat)} {TF : Nat → Nat} {ZT : Nat} {TS : Nat → Nat}
    {wits : List (List Nat × List Nat × Nat)} {s R : Nat} {CP : Nat → Nat} {Pt : List Nat}
    {Ts : Array (List Nat)} (hR : 0 < R)
    (ha : Rep n w (TF 0) ta) (hb : Rep n w (TF 1) tb) (hz : Rep n w ZT zt)
    (hP : ∀ p ∈ Pt, p < n) (hpts : ptsW w B (fstT TF qp) = Pt)
    (hcp : ∀ q < (wordsOf wits).length * R, wordCk n w (TF 0) (TF 1) (wordsOf wits) s R CP q = true)
    {j : Nat} (hj : j < wits.length)
    (hwit : fusBW n w B qp TF ZT TS wits s R CP j = true)
    (hc : (wits[j]).2.2 < Ts.size) (hT : Ts[(wits[j]).2.2]! = decW w Pt.length (TS j)) :
    witOK n ta tb zt Pt Ts wits[j] = true := by
  have hg : getW wits j = wits[j] := by
    rw [getW_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [fusBW, hg] at hwit
  dsimp only at hwit
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hwit
  obtain ⟨hl1, hl2, hinv, hcode⟩ := hwit
  have hl1' : (wits[j]).1.length ≤ (R - 1) * s := by
    have := Nat.le_of_ble_eq_true hl1
    rwa [lenA_eq] at this
  have hl2' : (wits[j]).2.1.length ≤ (R - 1) * s := by
    have := Nat.le_of_ble_eq_true hl2
    rwa [lenA_eq] at this
  have hfa := fr_rep ha
  have hfb := fr_rep hb
  have hws := wordsOf_get wits j hj
  have hlen : (wordsOf wits).length = 2 * wits.length := wordsOf_length wits
  have hck := ck_fr hw hfa hfb hcp
  have hx : FR n w (CP ((j + j) * R + (R - 1))) (ev ta tb (wits[j]).1) := by
    have := hck (2 * j) (by omega) (R - 1) (by omega)
    rw [hws.1, List.take_of_length_le hl1', show 2 * j * R = (j + j) * R by
      rw [Nat.two_mul]] at this
    exact this
  have hy : FR n w (CP ((j + j + 1) * R + (R - 1))) (ev ta tb (wits[j]).2.1) := by
    have := hck (2 * j + 1) (by omega) (R - 1) (by omega)
    rw [hws.2, List.take_of_length_le hl2', show (2 * j + 1) * R = (j + j + 1) * R by
      rw [Nat.two_mul]] at this
    exact this
  have hXt := wordTab_img (a := ta) (b := tb) ⟨ha.1, fun i hi => (ha.2 i hi).1⟩
    ⟨hb.1, fun i hi => (hb.2 i hi).1⟩ (wits[j]).1
  have hYt := wordTab_img (a := ta) (b := tb) ⟨ha.1, fun i hi => (ha.2 i hi).1⟩
    ⟨hb.1, fun i hi => (hb.2 i hi).1⟩ (wits[j]).2.1
  have hinvq : ∀ q < n, ev ta tb (wits[j]).2.1 (ev ta tb (wits[j]).1 q) = q := by
    intro q hq
    have h1 := (fr_mul hy hx q hq).1
    have e : mulW n w (CP ((j + j + 1) * R + (R - 1))) (CP ((j + j) * R + (R - 1))) =
        oneW n w := P.beq_iff.1 hinv
    rw [e, (fr_one hw q hq).1] at h1
    exact h1.symm
  have hcode' := P.beq_iff.1 hcode
  rw [recMap, hpts] at hcode'
  have hdec : decW w Pt.length (TS j) = Pt.map (cjW w ZT (CP ((j + j) * R + (R - 1)))
      (CP ((j + j + 1) * R + (R - 1)))) := by
    rw [← hcode']
    exact decW_codeK' (fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      exact imgW_lt _ _ _) (List.length_map _)
  unfold witOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hc, ?_⟩, ?_⟩
  · rw [invTabs, List.all_eq_true]
    intro q hq
    rw [List.mem_range] at hq
    rw [beq_iff_eq, (hXt.2 q hq).1, (hYt.2 _ (hXt.2 q hq).2).1, hinvq q hq]
  · rw [hT, hdec]
    apply List.map_congr_left
    intro p hp
    have hpn := hP p hp
    have e2 := hz.2 _ (hXt.2 p hpn).2
    rw [conjImg, (hXt.2 p hpn).1, (hYt.2 _ e2.1).1, cjW, (hx p hpn).1, e2.2, (hy _ e2.1).1]


theorem genW_eq (n w : Nat) : ∀ (G : List Nat) (i : Nat), genW n w G i = G.getD i (oneW n w)
  | [], i => by simp [genW]
  | x :: t, 0 => rfl
  | x :: t, i + 1 => by
    have e : genW n w (x :: t) (i + 1) = genW n w t i := rfl
    rw [e, genW_eq n w t i, List.getD_cons_succ]

theorem witIdx_eq : ∀ wits : List (List Nat × List Nat × Nat),
    witIdx wits = wits.map fun wt => wt.2.2
  | [] => rfl
  | wt :: t => by
    have e : witIdx (wt :: t) = wt.2.2 :: witIdx t := rfl
    rw [e, witIdx_eq t, List.map_cons]

theorem evalIdx_eq {M : Nat} {mt mu : Nat → Nat → Nat} (hM : 0 < M)
    (hm : ∀ i < M, ∀ k < M, mt i k = mu i k ∧ mu i k < M) {cs : List Nat} (hcs : ∀ c ∈ cs, c < M) :
    ∀ wd : List Nat, evalIdxW mt cs wd = evalIdxWord mu cs wd ∧ evalIdxWord mu cs wd < M := by
  intro wd
  induction wd with
  | nil => exact ⟨rfl, hM⟩
  | cons p wd ih =>
    have e1 : evalIdxW mt cs (p :: wd) = mt (getK cs p) (evalIdxW mt cs wd) := rfl
    have e2 : evalIdxWord mu cs (p :: wd) = mu (cs.getD p 0) (evalIdxWord mu cs wd) := rfl
    have hlt : cs.getD p 0 < M := by
      by_cases hp : p < cs.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
        exact hcs _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
        exact hM
    rw [e1, e2, getK_eq, ih.1]
    exact hm _ hlt _ ih.2

theorem base_qinv {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (zn gn gin hn hin k fuel M lg : Nat)
    (E : Nat → Nat) (K2 L2 : Nat)
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (T : Array (Array Nat)) (hRepT : ∀ j < T.size, Rep n w (TF j) T[j]!)
    (hq1' : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size) :
    ∀ p ∈ qp, ∀ x < n, img T[p.2]! (img T[p.1]! x) = x := by
  rw [baseSK] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hqinv, -⟩ := h
  rw [allA_eq, List.all_eq_true] at hqinv
  intro p hp x hx
  have e : mulW n w (TF p.2) (TF p.1) = oneW n w := P.beq_iff.1 (hqinv p hp)
  have h2 := fr_rep (hRepT p.2 (hq1' p hp).2)
  have h1 := fr_rep (hRepT p.1 (hq1' p hp).1)
  have h3 := (fr_mul h2 h1 x hx).1
  rw [e, (fr_one hw x hx).1] at h3
  exact h3.symm

theorem fusS_core {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (zn gn gin hn hin k fuel M lg : Nat)
    (E : Nat → Nat) (K2 L2 : Nat) (PG : Nat → Nat) (W : Nat) (BO IB PT CT : Nat → Nat)
    (K3 L3 K4 L4 zi ZT : Nat) (wits : List (List Nat × List Nat × Nat)) (gws : List (List Nat))
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hs : ∀ c < K2, setS w B qp TF RS RT zn M lg E PG (c * L2) L2 = true)
    (hb : ∀ c < K3, bfsS w B qp TF RS RT M lg W E BO IB PT CT (c * L3) L3 = true)
    (hcov : M ≤ K3 * L3 ∧ M ≤ K4 * L4)
    (hf : fusSH n w W qp TF M zi PT CT ZT wits gws = true)
    (hc : ∀ c < K4, fusC W qp.length M zi PT CT (c * L4) L4 = true)
    (s R : Nat) (CP : Nat → Nat)
    (hcp : ∀ q < (wordsOf wits).length * R, wordCk n w (TF 0) (TF 1) (wordsOf wits) s R CP q = true)
    (hwit : ∀ j < wits.length, fusBW n w B qp TF ZT (witE E BO wits) wits s R CP j = true) :
    FusionCert.fusionCheck n B ta.toArray tb.toArray
      (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2
      zi wits gws = true := by
  obtain ⟨hTs, hRepT, hq1', hB', happ, hpts, hMk, hMf, hstrict, hRa, hRb⟩ :=
    base_setup hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 PG h hnd hs
  obtain ⟨hM, -, hBO, hsurj, hVal, hparlt, hcllt, hX⟩ :=
    bfsS_enum hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 PG W BO IB PT
      CT K3 L3 h hnd hs hb hcov.1
  obtain ⟨hOrd, hU0⟩ :=
    bfsS_order hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 PG W BO IB PT
      CT K3 L3 h hnd hs hb hcov.1
  have hX' := hX _ rfl
  clear hX
  generalize bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
    (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel = X at hX' ⊢
  generalize slpTabsA ta.toArray tb.toArray prog = T at hTs hRepT hq1' happ hpts hVal hX' hOrd hU0 ⊢
  obtain ⟨hXs, hX1, hX2, hX3⟩ := hX'
  have hqinv := base_qinv hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 h T
    hRepT hq1'
  rw [fusSH] at hf
  dsimp only at hf
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true, lenA_eq] at hf
  obtain ⟨hzM, hz0, hzz, hzc, hZT, hwb, hgws⟩ := hf
  set G := qp.map fun p => T[p.1]! with hGdef
  have hGl : G.length = qp.length := List.length_map _
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hfP : ∀ i < M, 0 < i → fieldT W PT i = X.2.1[i]! := fun i hi hi0 => (hX2 i hi hi0).symm
  have hfC : ∀ i < M, ∀ j < qp.length, fieldT W CT (i * (qp.length + qp.length) + j) =
      X.2.2[i * (qp.length + qp.length) + j]! := fun i hi j hj => (hX3 i hi j hj).symm
  have hpar : ∀ i < M, 0 < i → X.2.1[i]! < i ∧ 0 < qp.length := by
    intro i hi hi0
    rw [hX2 i hi hi0]
    exact hparlt i hi hi0
  have hcl : ∀ i < M, ∀ j < qp.length, X.2.2[i * (qp.length + qp.length) + j]! < M := by
    intro i hi j hj
    rw [hX3 i hi j hj]
    exact hcllt i hi j hj
  have hmulS := mulG_spec' (N := M) (g := qp.length) (gi := qp.length) (par := X.2.1)
    (cl := X.2.2) (fP := fieldT W PT) (fC := fieldT W CT) hfP hfC hpar hcl M
  have hmT : ∀ i < M, ∀ k < M, mulT W qp.length M PT CT i k =
      mulIdx qp.length qp.length X.2.1 X.2.2 M i k ∧
      mulIdx qp.length qp.length X.2.1 X.2.2 M i k < M := fun i hi k hk => hmulS i k hi hk
  have hcj : ∀ j < qp.length, X.2.2[j]! = fieldT W CT j := by
    intro j hj
    have := hX3 0 hM j hj
    rw [Nat.zero_mul, Nat.zero_add] at this
    exact this
  have hcjlt : ∀ j < qp.length, fieldT W CT j < M := by
    intro j hj
    have := hcllt 0 hM j hj
    rwa [Nat.zero_mul, Nat.zero_add] at this
  have hGlt : ∀ t < G.length, ∀ y < n, img G[t]! y < n := by
    intro t ht y hy
    have ht' : t < qp.length := by omega
    rw [hGj t ht']
    exact ((hRepT _ (hq1' _ (List.getElem_mem ht')).1).2 y hy).1
  have hov : ∀ x ∈ ptsOf B G, x < n := by
    intro x hx
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
      rw [← getElem!_pos G t ht]
      exact hGlt t ht b (hB' b hb)
  have hGrep : ∀ j < qp.length, Rep n w (genW n w (fstT TF qp) j) (G.getD j #[]) := by
    intro j hj
    have e1 : (fstT TF qp).getD j (oneW n w) = TF qp[j].1 := by
      rw [fstT_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
      rfl
    have e2 : G.getD j #[] = T[qp[j].1]! := by
      rw [List.getD_eq_getElem?_getD, hGdef, List.getElem?_map, List.getElem?_eq_getElem hj]
      rfl
    rw [genW_eq, e1, e2]
    exact hRepT _ (hq1' _ (List.getElem_mem hj)).1
  have hzlt : zi < M := P.blt_iff.1 hzM
  have hZrep : Rep n w ZT (idxTab n G qp.length qp.length X.2.1 X.2.2 M zi) := by
    rw [P.beq_iff.1 hZT]
    exact idx_rep hw hGrep hfP hfC hpar M zi hzlt
  have hwb' : ∀ c ∈ witIdx wits, c < M := by
    intro c hc
    have h1 := hwb
    rw [allL_eq, List.all_eq_true] at h1
    exact P.blt_iff.1 (h1 c hc)
  have hcomm : ∀ x < M, allL (rangeK qp.length) (fun j => Nat.beq
      (mulT W qp.length M PT CT (fieldT W CT j) x) (mulT W qp.length M PT CT x (fieldT W CT j))) =
        true ↔ ((List.range qp.length).all fun j =>
          mulIdx qp.length qp.length X.2.1 X.2.2 M X.2.2[j]! x ==
            mulIdx qp.length qp.length X.2.1 X.2.2 M x X.2.2[j]!) = true := by
    intro x hx
    rw [allL_eq, rangeK_eq', List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    have hj' := List.mem_range.1 hj
    rw [hcj j hj', ← (hmT _ (hcjlt j hj') _ hx).1, ← (hmT _ hx _ (hcjlt j hj')).1, P.beq_iff,
      beq_iff_eq]
  have hzne : zi ≠ 0 := by
    intro h0
    have := P.notB_iff.1 hz0
    rw [h0] at this
    exact this (by decide)
  have hGinj : ∀ t < G.length, ∀ x < n, ∀ y < n, img G[t]! x = img G[t]! y → x = y := by
    intro t ht x hx y hy e
    have ht' : t < qp.length := by omega
    have hq := hqinv qp[t] (List.getElem_mem ht')
    rw [hGj t ht'] at e
    rw [← hq x hx, ← hq y hy, e]
  have hPtr : ∀ t < G.length, ∀ x ∈ (ptsOf B G).take B.length, img G[t]! x ∈ ptsOf B G := by
    intro t ht x hx
    have hxB : x ∈ B := by
      rw [ptsOf, List.take_left] at hx
      exact hx
    rw [ptsOf, List.mem_append]
    right
    rw [List.mem_flatMap]
    refine ⟨G[t]!, ?_, List.mem_map.2 ⟨x, hxB, rfl⟩⟩
    rw [getElem!_pos G t ht]
    exact List.getElem_mem ht
  have hS : Reg.Setup n B.length M G (fun i => decW w (ptsOf B G).length (E (BO i)))
      (fieldT W PT) (discK W G.length PT CT)
      (fun i t => fieldT W CT (i * (G.length + G.length) + t)) (ptsOf B G) :=
    ⟨hOrd, hM, fun i hi => (hVal i hi).1, hU0, hGlt, hGinj, hPtr⟩
  have hparL : ∀ k < M, 0 < k → X.2.1[k]! = fieldT W PT k := hX2
  have hclAL : ∀ i < M, ∀ t < G.length, X.2.2[i * (G.length + G.length) + t]! =
      fieldT W CT (i * (G.length + G.length) + t) := by
    intro i hi t ht
    rw [hGl]
    exact hX3 i hi t (by omega)
  have hGsz : ∀ t < G.length, G[t]!.size = n := by
    intro t ht
    have ht' : t < qp.length := by omega
    rw [hGj t ht']
    exact (hRepT _ (hq1' _ (List.getElem_mem ht')).1).1
  have hcover : ∀ x < M, (((List.range qp.length).all fun j =>
      mulIdx qp.length qp.length X.2.1 X.2.2 M X.2.2[j]! x ==
        mulIdx qp.length qp.length X.2.1 X.2.2 M x X.2.2[j]!) = false ∨ x = 0) ∨ x = zi := by
    intro x hx
    have hL : 0 < L4 := by
      rcases Nat.eq_zero_or_pos L4 with h0 | h0
      · have := hcov.2
        rw [h0, Nat.mul_zero] at this
        omega
      · exact h0
    have hK : x / L4 < K4 := by
      rw [Nat.div_lt_iff_lt_mul hL]
      exact lt_of_lt_of_le hx hcov.2
    have h1 := hc (x / L4) hK
    rw [fusC] at h1
    dsimp only at h1
    have h2 := allR_true h1 (x % L4) (Nat.mod_lt _ hL)
    rw [Nat.div_add_mod' x L4] at h2
    rcases P.orB_iff.1 (P.impB_iff.1 h2 (P.blt_iff.2 hx)) with h | h
    · left
      left
      exact Bool.eq_false_iff.2 fun hall => P.notB_iff.1 h ((hcomm x hx).2 hall)
    · rcases P.orB_iff.1 h with h | h
      · left
        right
        exact P.beq_iff.1 h
      · right
        exact P.beq_iff.1 h
  have hgwE : ∀ x < qp.length, evalIdxWord (mulIdx qp.length qp.length X.2.1 X.2.2 M)
      (wits.map fun w => w.2.2) (gws.getD x []) = X.2.2[x]! := by
    intro x hx
    have h1 := hgws
    rw [allL_eq, rangeK_eq', List.all_eq_true] at h1
    have h2 := P.beq_iff.1 (h1 x (List.mem_range.2 hx))
    rw [hcj x hx, ← h2, getLL_eq, witIdx_eq]
    have hwb'' : ∀ c ∈ wits.map (fun wt => wt.2.2), c < M := by
      rw [← witIdx_eq]
      exact hwb'
    exact ((evalIdx_eq hM hmT hwb'' _).1).symm
  have hEinj : ∀ a < M, ∀ b < M, E a = E b → a = b := by
    intro a ha b hb e
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd (congrArg (keyC w B.length) e) (Nat.ne_of_lt (hstrict _ _ h hb))
    · exact h
    · exact absurd (congrArg (keyC w B.length) e).symm (Nat.ne_of_lt (hstrict _ _ h ha))
  have hwI : ∀ j (hj : j < wits.length), getK (witIdx wits) j = wits[j].2.2 := by
    intro j hj
    rw [getK_eq, witIdx_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj]
    rfl
  have hwM : ∀ j (hj : j < wits.length), wits[j].2.2 < M := fun j hj => hwb' _ (by
    rw [witIdx_eq]
    exact List.mem_map_of_mem (List.getElem_mem hj))
  have hR0case : R = 0 → ∀ j0 (hj0 : j0 < wits.length), witOK n ta.toArray tb.toArray
      (idxTab n G qp.length qp.length X.2.1 X.2.2 M zi) (ptsOf B G) X.1 wits[j0] = true := by
    intro hR0 j0 hj0
    subst hR0
    have hfw : ∀ j (hj : j < wits.length), (wits[j].1.length = 0 ∧ wits[j].2.1.length = 0) ∧
        codeK w (List.rec (motive := fun _ => List Nat) []
          (fun p _ ih => List.cons (cjW w ZT (CP 0) (CP 0) p) ih)
          (ptsW w B (fstT TF qp))) = witE E BO wits j := by
      intro j hj
      have h1 := hwit j hj
      have hg : getW wits j = wits[j] := by
        rw [getW_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      rw [fusBW, hg] at h1
      dsimp only at h1
      simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h1
      obtain ⟨l1, l2, -, hcode⟩ := h1
      refine ⟨⟨?_, ?_⟩, P.beq_iff.1 hcode⟩
      · have := Nat.le_of_ble_eq_true l1
        rw [lenA_eq] at this
        simpa [Nat.mul_eq] using this
      · have := Nat.le_of_ble_eq_true l2
        rw [lenA_eq] at this
        simpa [Nat.mul_eq] using this
    have hcc : ∀ j (hj : j < wits.length), wits[j].2.2 = wits[j0].2.2 := by
      intro j hj
      have e := (hfw j hj).2.symm.trans (hfw j0 hj0).2
      unfold witE at e
      rw [hwI j hj, hwI j0 hj0] at e
      have e2 := hEinj _ (hBO _ (hwM j hj)).1 _ (hBO _ (hwM j0 hj0)).1 e
      calc wits[j].2.2 = IB (BO wits[j].2.2) := ((hBO _ (hwM j hj)).2).symm
        _ = IB (BO wits[j0].2.2) := by rw [e2]
        _ = wits[j0].2.2 := (hBO _ (hwM j0 hj0)).2
    have hcs : ∀ c ∈ wits.map (fun wt => wt.2.2), c = wits[j0].2.2 := by
      intro c hc
      obtain ⟨wt, hwt, rfl⟩ := List.mem_map.1 hc
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hwt
      exact hcc j hj
    have hcover' : ∀ x < M, (((List.range G.length).all fun j =>
        mulIdx G.length G.length X.2.1 X.2.2 M X.2.2[j]! x ==
          mulIdx G.length G.length X.2.1 X.2.2 M x X.2.2[j]!) = false ∨ x = 0) ∨ x = zi := by
      rw [hGl]
      exact hcover
    have hgw' : ∀ x < G.length, evalIdxWord (mulIdx G.length G.length X.2.1 X.2.2 M)
        (wits.map fun w => w.2.2) (gws.getD x []) = X.2.2[x]! := by
      rw [hGl]
      exact hgwE
    have hz : wits[j0].2.2 = zi :=
      Reg.c0_eq_zi hS hparL hclAL hGsz hzlt hzne (hwM j0 hj0) hcs hcover' hgw'
    have hw1 : wits[j0].1 = [] := List.length_eq_zero_iff.1 (hfw j0 hj0).1.1
    have hw2 : wits[j0].2.1 = [] := List.length_eq_zero_iff.1 (hfw j0 hj0).1.2
    have hwt : wordTab n ta.toArray tb.toArray [] = Array.range n := rfl
    obtain ⟨hs1, hs2⟩ := Reg.idxTab_prop hS hparL hclAL hGsz M zi hzlt
    have hU := Reg.U_idx hS hparL hclAL hGsz hzlt
    rw [hGl] at hs1 hs2 hU
    unfold witOK
    rw [hw1, hw2, hwt]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨by rw [hXs]; exact hwM j0 hj0, ?_⟩, ?_⟩
    · rw [invTabs, List.all_eq_true]
      intro q hq
      rw [List.mem_range] at hq
      simp [Reg.img_range' hq]
    · rw [hz, hX1 zi hzlt]
      rw [hU]
      refine List.map_congr_left fun p hp => ?_
      have hpn := hov p hp
      rw [conjImg, Reg.img_range' hpn, Reg.img_range' (hs2 p hpn)]
  simp only [FusionCert.fusionCheck, hXs, hGl, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨hzlt, hzne⟩, ?_⟩, ?_⟩, hcover⟩, ?_⟩, hgwE⟩
  · rw [← (hmT _ hzlt _ hzlt).1]
    exact P.beq_iff.1 hzz
  · intro x hx
    have h1 := hzc
    rw [allL_eq, rangeK_eq', List.all_eq_true] at h1
    have h2 := P.beq_iff.1 (h1 x (List.mem_range.2 hx))
    rw [hcj x hx, ← (hmT _ (hcjlt x hx) _ hzlt).1, ← (hmT _ hzlt _ (hcjlt x hx)).1]
    exact h2
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    by_cases hR : 0 < R
    · have hc' : (wits[j]).2.2 < M := hwM j hj
      refine witOK_of hw hR hRa hRb hZrep hov hpts hcp hj (hwit j hj) (by rw [hXs]; exact hc') ?_
      rw [hX1 _ hc']
      unfold witE
      rw [hwI j hj]
    · exact hR0case (by omega) j hj

end CFSG.KC.LQT.FS.Pf

namespace CFSG.KC.LQT.FS

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2 CFSG.KC.LQT.BT CFSG.KC.LQT.BS
open CFSG.KC.LQT.FB

theorem fusS_sound {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (zn gn gin hn hin k fuel M lg : Nat)
    (E : Nat → Nat) (K2 L2 : Nat) (PG : Nat → Nat) (W : Nat) (BO IB PT CT : Nat → Nat)
    (K3 L3 K4 L4 zi ZT : Nat) (wits : List (List Nat × List Nat × Nat)) (gws : List (List Nat))
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hs : ∀ c < K2, setS w B qp TF RS RT zn M lg E PG (c * L2) L2 = true)
    (hb : ∀ c < K3, bfsS w B qp TF RS RT M lg W E BO IB PT CT (c * L3) L3 = true)
    (hcov : M ≤ K3 * L3 ∧ M ≤ K4 * L4)
    (hf : fusSH n w W qp TF M zi PT CT ZT wits gws = true)
    (hc : ∀ c < K4, fusC W qp.length M zi PT CT (c * L4) L4 = true)
    (s R : Nat) (CP : Nat → Nat)
    (hcp : ∀ q < (wordsOf wits).length * R, wordCk n w (TF 0) (TF 1) (wordsOf wits) s R CP q = true)
    (hwit : ∀ j < wits.length, fusBW n w B qp TF ZT (witE E BO wits) wits s R CP j = true) :
    FusionCert.fusionCheck n B ta.toArray tb.toArray
      (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2
      zi wits gws = true := by
  exact Pf.fusS_core hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 PG W
    BO IB PT CT K3 L3 K4 L4 zi ZT wits gws h hnd hs hb hcov hf hc s R CP hcp hwit

end CFSG.KC.LQT.FS
