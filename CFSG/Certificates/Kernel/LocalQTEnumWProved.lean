module

public import CFSG.Certificates.Kernel.LocalQTBaseWProved

public section

namespace CFSG.KC.LQT.BW.Cl

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.BW.Pf
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem pos_uniq {t i j j0 gg : Nat} (hj : j < gg) (hj0 : j0 < gg)
    (h : t * gg + j = i * gg + j0) : t = i ∧ j = j0 := by
  rcases Nat.lt_trichotomy t i with hti | rfl | hti
  · have := Nat.mul_le_mul_right gg (Nat.succ_le_of_lt hti)
    rw [Nat.succ_mul] at this
    omega
  · omega
  · have := Nat.mul_le_mul_right gg (Nat.succ_le_of_lt hti)
    rw [Nat.succ_mul] at this
    omega

theorem pos_gap {t i j g gg : Nat} (hj : j < g) (hg : g ≤ gg) (h1 : i * gg + g ≤ t * gg + j)
    (h2 : t * gg + j < (i + 1) * gg) : False := by
  rcases Nat.lt_trichotomy t i with hti | rfl | hti
  · have := Nat.mul_le_mul_right gg (Nat.succ_le_of_lt hti)
    rw [Nat.succ_mul] at this
    omega
  · omega
  · have : (i + 1) * gg ≤ t * gg := Nat.mul_le_mul_right gg hti
    omega

theorem pos_lt {t j gg N : Nat} (ht : t < N) (hj : j < gg) : t * gg + j < N * gg := by
  have := Nat.mul_le_mul_right gg (Nat.succ_le_of_lt ht)
  rw [Nat.succ_mul] at this
  omega

theorem zerosOn_eq (l : List Nat) : ∀ m : Nat, zerosOn m l = List.replicate m 0 ++ l
  | 0 => rfl
  | m + 1 => by
    change 0 :: zerosOn m l = _
    rw [zerosOn_eq l m, List.replicate_succ, List.cons_append]

@[expose] def ClI (w nb gg : Nat) (Gc : List Nat) (es : ES) : Prop :=
  OrdT es.kt ∧ ∀ t j, j < Gc.length → t * gg + j < es.cl.length →
    t < es.rev.length ∧
    memKT es.kt (keyW w nb (imgsW w (Gc.getD j 0) (es.rev.reverse.getD t []))) ∧
    idxG ltK es.kt (keyW w nb (imgsW w (Gc.getD j 0) (es.rev.reverse.getD t []))) =
      es.cl.reverse.getD (t * gg + j) 0

section Inv

variable {w nb gg : Nat} {Gc : List Nat}

theorem step_cl {es : ES} (hc : ClI w nb gg Gc es) {i j0 : Nat} {T : List Nat} (hj0 : j0 < Gc.length)
    (hg : Gc.length ≤ gg) (hi : i < es.rev.length) (hT : es.rev.reverse.getD i [] = T)
    (hl : es.cl.length = i * gg + j0) :
    ClI w nb gg Gc (if memTT es.kt (keyW w nb (imgsW w (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)
        else newE i es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)) ∧
    (if memTT es.kt (keyW w nb (imgsW w (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)
        else newE i es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)).cl.length =
      es.cl.length + 1 ∧
    ∃ new, (if memTT es.kt (keyW w nb (imgsW w (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)
        else newE i es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)).rev.reverse =
      es.rev.reverse ++ new := by
  obtain ⟨ho, hcl⟩ := hc
  generalize hc' : imgsW w (Gc.getD j0 0) T = c
  have hpos : ∀ t j, j < Gc.length → t * gg + j = es.cl.length → t = i ∧ j = j0 := by
    intro t j hj e
    rw [hl] at e
    exact pos_uniq (Nat.lt_of_lt_of_le hj hg) (Nat.lt_of_lt_of_le hj0 hg) e
  by_cases hf : memTT es.kt (keyW w nb c) = true
  · rw [ite_eq_left hf]
    refine ⟨⟨ho, fun t j hj ht => ?_⟩, by simp [foundE], [], by simp [foundE]⟩
    simp only [foundE, List.length_cons] at ht ⊢
    rw [List.reverse_cons]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
    · rw [getD_append_left (by simpa using ht)]
      exact hcl t j hj ht
    · obtain ⟨rfl, rfl⟩ := hpos t j hj ht
      rw [ht, show es.cl.length = es.cl.reverse.length by simp, getD_append_len, hT, hc',
        ← idxTT_eq]
      refine ⟨hi, ?_, rfl⟩
      rw [memTT_eq, memG_iff ltK_iff ho] at hf
      exact hf
  · rw [ite_eq_right hf]
    have hnot : ¬ memKT es.kt (keyW w nb c) := fun h =>
      hf (by rw [memTT_eq]; exact (memG_iff ltK_iff ho _).2 h)
    refine ⟨⟨?_, fun t j hj ht => ?_⟩, by simp [newE], [c], by simp [newE]⟩
    · simp only [newE]
      rw [insTT_eq]
      exact ord_insG ltK_iff _ _ _ ho
    · simp only [newE, List.length_cons] at ht ⊢
      rw [List.reverse_cons, List.reverse_cons, insTT_eq]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · obtain ⟨h1, h2, h3⟩ := hcl t j hj ht
        rw [getD_append_left (by simpa using h1), getD_append_left (by simpa using ht)]
        have hne : keyW w nb (imgsW w (Gc.getD j 0) (es.rev.reverse.getD t [])) ≠ keyW w nb c :=
          fun e => hnot (e ▸ h2)
        refine ⟨by omega, (mem_insG ltK_iff _ _ _ _ _).2 (Or.inr h2), ?_⟩
        rw [(look_insG_ne _ _ _ hne _).1]
        exact h3
      · obtain ⟨rfl, rfl⟩ := hpos t j hj ht
        rw [ht, show es.cl.length = es.cl.reverse.length by simp, getD_append_len,
          getD_append_left (by simpa using hi), hT, hc']
        exact ⟨by omega, (mem_insG ltK_iff _ _ _ _ _).2 (Or.inl rfl),
          (look_insG_self _ _ _ hnot).1⟩

theorem kids_cl {i : Nat} {T : List Nat} (hg : Gc.length ≤ gg) : ∀ (Gs : List Nat) (j0 : Nat)
    (es : ES), Gc.drop j0 = Gs → ClI w nb gg Gc es → es.cl.length = i * gg + j0 →
    i < es.rev.length → es.rev.reverse.getD i [] = T →
    ClI w nb gg Gc (kidsW w nb (imgsW w) Gs i T es) ∧
    (kidsW w nb (imgsW w) Gs i T es).cl.length = i * gg + j0 + Gs.length ∧
    ∃ new, (kidsW w nb (imgsW w) Gs i T es).rev.reverse = es.rev.reverse ++ new
  | [], _, es, _, hc, hl, _, _ => ⟨hc, by rw [kidsW_nil, hl]; rfl, [], by simp [kidsW_nil]⟩
  | s :: Gs, j0, es, hd, hc, hl, hi, hT => by
    have hj0 : j0 < Gc.length := by
      have := congrArg List.length hd
      simp at this
      omega
    have hs : Gc.getD j0 0 = s := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0, Option.getD_some]
      have := congrArg List.head? hd
      rw [List.head?_drop, List.head?_cons] at this
      rw [List.getElem?_eq_getElem hj0] at this
      exact Option.some.inj this
    have hd' : Gc.drop (j0 + 1) = Gs := by
      rw [← List.drop_drop, hd, List.drop_one, List.tail_cons]
    rw [kidsW_cons]
    rw [← hs]
    obtain ⟨hc1, hl1, new1, hr1⟩ := step_cl hc hj0 hg hi hT hl
    have hi1 : i < (if memTT es.kt (keyW w nb (imgsW w (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)
        else newE i es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)).rev.length := by
      have := congrArg List.length hr1
      simp only [List.length_reverse, List.length_append] at this
      omega
    have hT1 : (if memTT es.kt (keyW w nb (imgsW w (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)
        else newE i es (keyW w nb (imgsW w (Gc.getD j0 0) T)) (imgsW w (Gc.getD j0 0) T)).rev.reverse.getD
          i [] = T := by
      rw [hr1, getD_append_left (by simpa using hi), hT]
    rw [hs] at hc1 hl1 hr1 hi1 hT1 ⊢
    obtain ⟨hc2, hl2, new2, hr2⟩ := kids_cl hg Gs (j0 + 1) _ hd' hc1 (by rw [hl1, hl]; omega) hi1 hT1
    refine ⟨hc2, by rw [hl2, List.length_cons]; omega, new1 ++ new2, by
      rw [hr2, hr1, List.append_assoc]⟩

theorem clfix_cl {gi : Nat} (hgg : gg = Gc.length + gi) {es : ES} {i : Nat}
    (hc : ClI w nb gg Gc es) (hl : es.cl.length = i * gg + Gc.length) :
    ClI w nb gg Gc (clfix gi es) ∧ (clfix gi es).cl.length = (i + 1) * gg := by
  obtain ⟨ho, hcl⟩ := hc
  have hlen : (clfix gi es).cl.length = (i + 1) * gg := by
    simp only [clfix, zerosOn_eq, List.length_append, List.length_replicate, hl, Nat.succ_mul]
    omega
  refine ⟨⟨ho, fun t j hj ht => ?_⟩, hlen⟩
  rw [hlen] at ht
  have hrev : (clfix gi es).cl.reverse = es.cl.reverse ++ List.replicate gi 0 := by
    simp [clfix, zerosOn_eq]
  have hold : t * gg + j < es.cl.length := by
    apply Nat.lt_of_not_le
    intro hge
    rw [hl] at hge
    exact pos_gap hj (by omega) hge ht
  rw [hrev, getD_append_left (by simpa using hold)]
  exact hcl t j hj hold

theorem round_cl {gi : Nat} (hgg : gg = Gc.length + gi) : ∀ (F : List (List Nat)) (i : Nat)
    (es : ES), ClI w nb gg Gc es → es.cl.length = i * gg →
    (∀ t < F.length, i + t < es.rev.length ∧ es.rev.reverse.getD (i + t) [] = F.getD t []) →
    ClI w nb gg Gc (roundW w nb gi (imgsW w) Gc F i es) ∧
    (roundW w nb gi (imgsW w) Gc F i es).cl.length = (i + F.length) * gg ∧
    ∃ new, (roundW w nb gi (imgsW w) Gc F i es).rev.reverse = es.rev.reverse ++ new
  | [], i, es, hc, hl, _ => ⟨hc, by rw [roundW_nil, hl]; rfl, [], by simp [roundW_nil]⟩
  | T :: F, i, es, hc, hl, hF => by
    rw [roundW_cons]
    have h0 := hF 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    obtain ⟨hc1, hl1, new1, hr1⟩ := kids_cl (T := T) (by omega) Gc 0 es rfl hc
      (by rw [hl]; omega) h0.1 h0.2
    rw [Nat.add_zero] at hl1
    obtain ⟨hc2, hl2⟩ := clfix_cl hgg hc1 hl1
    have hF1 : ∀ t < F.length, i + 1 + t < (clfix gi (kidsW w nb (imgsW w) Gc i T es)).rev.length ∧
        (clfix gi (kidsW w nb (imgsW w) Gc i T es)).rev.reverse.getD (i + 1 + t) [] = F.getD t [] := by
      intro t ht
      have := hF (t + 1) (by simp; omega)
      rw [List.getD_cons_succ, show i + (t + 1) = i + 1 + t by omega] at this
      have hr1' : (clfix gi (kidsW w nb (imgsW w) Gc i T es)).rev.reverse = es.rev.reverse ++ new1 :=
        hr1
      refine ⟨?_, ?_⟩
      · have := congrArg List.length hr1'
        simp only [List.length_reverse, List.length_append] at this
        omega
      · rw [hr1', getD_append_left (by simpa using this.1), this.2]
    obtain ⟨hc3, hl3, new2, hr3⟩ := round_cl hgg F (i + 1) _ hc2 hl2 hF1
    refine ⟨hc3, by rw [hl3, List.length_cons]; congr 1; omega, new1 ++ new2, ?_⟩
    rw [hr3, ← List.append_assoc]
    exact congrArg (· ++ new2) hr1

end Inv

theorem enum_cl {n w nb L gg : Nat} {G : List (Array Nat)} (hw : n ≤ 2 ^ w) {gi : Nat}
    {Gp : List (Nat × Array Nat)} (hG : ∀ p ∈ Gp, Rep n w p.1 p.2 ∧ p.2 ∈ G)
    (hGs : Gp.map Prod.snd = G) {o : List Nat} (ho : Val n L o) (hgg : gg = Gp.length + gi) :
    ∀ dd, ClI w nb gg (Gp.map Prod.fst) (enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).1 ∧
      (enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).1.cl.length =
        (enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd).2.1 * gg
  | 0 => by
    rw [enumW_zero]
    refine ⟨⟨?_, fun t j _ ht => by simp at ht⟩, by simp⟩
    change OrdT (insTT TT.lf (keyW w nb o) 0 o)
    rw [insTT_eq]
    exact ord_insG ltK_iff _ _ _ trivial
  | dd + 1 => by
    obtain ⟨S, hc, -, hF, hle, -, -, -⟩ := enum_corr (nb := nb) (gi := gi) hw hG hGs ho dd
    obtain ⟨ih1, ih2⟩ := enum_cl hw hG hGs ho hgg dd
    rcases hE : enumW w nb gi (imgsW w) (Gp.map Prod.fst) o dd with ⟨st, i, F⟩
    rw [hE] at hc hF hle ih1 ih2
    dsimp only at hc hF hle ih1 ih2
    rw [enumW_succ w nb gi (imgsW w) (Gp.map Prod.fst) o dd st i F hE]
    have hr : S.1.toList = st.rev.reverse := hc.1
    have hcnt : st.cnt = S.1.size := hc.2.2.1
    rw [hr] at hF
    have hrl : st.rev.length = S.1.size := by
      have := congrArg List.length hr
      simp only [Array.length_toList, List.length_reverse] at this
      omega
    have hFl : F.length = st.rev.length - i := by rw [hF, List.length_drop, List.length_reverse]
    obtain ⟨h1, h2, -⟩ := round_cl (gi := gi) (by rw [List.length_map]; exact hgg) F i
      (ES.mk st.kt st.cnt st.rev st.par st.cl [] st.ok) ih1 ih2 (by
        intro t ht
        rw [hFl] at ht
        refine ⟨by dsimp only; omega, ?_⟩
        dsimp only
        rw [hF, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop])
    refine ⟨h1, ?_⟩
    dsimp only
    rw [h2, hFl]
    congr 1
    omega

theorem enumW_bfs {n w : Nat} (hw : n ≤ 2 ^ w) {B : List Nat} {T : Array (Array Nat)}
    {R : List Nat} (hlen : lenA R = T.size) (hrep : ∀ j < T.size, Rep n w (nodeK R j) T[j]!)
    {qp : List (Nat × Nat)} (hqp : qpW n w B R qp = true) {k fuel dd : Nat}
    (X : Array (List Nat) × Array Nat × Array Nat)
    (hX : bfsEnumB n B (qp.map fun p => T[p.1]!) (qp.map fun p => T[p.2]!) fuel = X)
    (E : ES × Nat × List (List Nat))
    (hEd : enumW w (lenA B) (lenA qp) (imgsW w) (fstN R qp) (ptsW w B (fstN R qp)) dd = E)
    (hE : enumOK k fuel E = true) :
    (∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size) ∧
    (∀ p ∈ qp, ∀ q < n, img T[p.2]! (img T[p.1]! q) = q) ∧
    BaseEnumOK n B (qp.map fun p => T[p.1]!) (qp.map fun p => T[p.2]!) X.1 X.2.1 X.2.2 ∧
    X.1.size = 2 ^ k ∧ E.1.cnt = X.1.size ∧ E.1.par.length = X.1.size ∧
    (∀ i < X.1.size, X.2.1[i]! = E.1.par.reverse.getD i 0) ∧
    E.1.cl.length = X.1.size * (qp.length + qp.length) ∧
    (∀ t < X.1.size, ∀ j < qp.length, X.2.2[t * (qp.length + qp.length) + j]! =
      E.1.cl.reverse.getD (t * (qp.length + qp.length) + j) 0) := by
  subst hX hEd
  rw [qpW, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, allA_eq, allA_eq, allL_eq,
    List.all_eq_true, List.all_eq_true, List.all_eq_true] at hqp
  obtain ⟨hq1, hq2, hB⟩ := hqp
  have hq1' : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    intro p hp
    have := hq1 p hp
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, hlen] at this
    exact this
  have hB' : ∀ b ∈ B, b < n := fun b hb => by simpa using hB b hb
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  set Gp := qp.map fun p => (nodeK R p.1, T[p.1]!) with hGpdef
  have hGp : ∀ p ∈ Gp, Rep n w p.1 p.2 ∧ p.2 ∈ G := by
    intro p hp
    rw [hGpdef, List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ⟨hrep a.1 (hq1' a ha).1, List.mem_map.2 ⟨a, ha, rfl⟩⟩
  have hGs : Gp.map Prod.snd = G := by rw [hGpdef, hGdef, List.map_map]; rfl
  have hfst : fstN R qp = Gp.map Prod.fst := by rw [fstN_eq, hGpdef, List.map_map]; rfl
  have hGrep : ∀ s ∈ G, ∃ c, Rep n w c s := by
    intro s hs
    rw [← hGs, List.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨p.1, (hGp p hp).1⟩
  have hpts : ptsW w B (fstN R qp) = ptsOf B G := by
    rw [hfst, ptsW_eq hB' (forall2_pairs Gp fun p hp => (hGp p hp).1), hGs]
  have hov : Val n (ptsOf B G).length (ptsOf B G) := by
    refine ⟨rfl, fun x hx => ?_⟩
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hGrep s hs
      exact (hc.2 b (hB' b hb)).1
  have hGpl : Gp.length = qp.length := by rw [hGpdef, List.length_map]
  rw [hpts, hfst, lenA_eq, lenA_eq] at hE ⊢
  obtain ⟨S, hc, hb, hF, hle, hok, new0, he0⟩ :=
    enum_corr (nb := B.length) (L := (ptsOf B G).length) (gi := qp.length) hw hGp hGs hov dd
  obtain ⟨hcl, hcll⟩ := enum_cl (nb := B.length) (gg := qp.length + qp.length) (gi := qp.length) hw
    hGp hGs hov (by rw [hGpl]) dd
  generalize enumW w B.length qp.length (imgsW w) (Gp.map Prod.fst) (ptsOf B G) dd = E
    at hE hc hb hF hle hok hcl hcll ⊢
  obtain ⟨hE1, hE2, hE3, hE4⟩ := enumOK_spec hE
  have hcnt : E.1.cnt = S.1.size := hc.2.2.1
  have hiS : E.2.1 = S.1.size := by
    rw [hE1] at hF
    have : S.1.toList.length ≤ E.2.1 := List.drop_eq_nil_iff.1 hF.symm
    simp at this
    omega
  have hloop : bfsLoopB n B.length G fuel 0 (S0 n B.length (ptsOf B G)) = S := by
    have := hb (fuel - E.2.1)
    rw [show E.2.1 + (fuel - E.2.1) = fuel by omega, hiS, bfsLoopB_stop] at this
    exact this
  unfold S0 at hloop
  have hbe : bfsEnumB n B G Gi fuel = (S.1, S.2.1, (List.range S.1.size).foldl (fun acc i =>
      (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc) #[]) := by
    simp only [bfsEnumB, hloop]
  rw [hbe]
  dsimp only
  have hc' := hc
  obtain ⟨hr, hp, -, hps, hv, -, hm, hl, -, hmg, hpar⟩ := hc'
  have hGl : G.length = qp.length := by rw [hGdef, List.length_map]
  have hGil : Gi.length = qp.length := by rw [hGidef, List.length_map]
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGij : ∀ j (hj : j < qp.length), Gi[j]! = T[qp[j].2]! := by
    intro j hj
    rw [getElem!_pos Gi j (by omega)]
    simp only [hGidef, List.getElem_map]
  have hinvq : ∀ a ∈ qp, ∀ q < n, img T[a.2]! (img T[a.1]! q) = q := fun a ha =>
    rep_inv (hrep a.1 (hq1' a ha).1) (hrep a.2 (hq1' a ha).2) hw
      (Nat.eq_of_beq_eq_true (by simpa using hq2 a ha))
  have hokc := hok hE4
  rw [hiS] at hokc
  have hclget : ∀ i < S.1.size, ∀ j < (G ++ Gi).length,
      ((List.range S.1.size).foldl (fun acc i => (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc)
        (#[] : Array Nat))[i * (G.length + Gi.length) + j]! =
      S.2.2.getD (keyNat n B.length (applyTab (G ++ Gi)[j]! S.1[i]!)) 0 := by
    intro i hi j hj
    rw [arr_getN, cl_fold, ← List.length_append]
    exact (flatMap_getD (G ++ Gi) _ S.1.size).2 i hi j hj
  have hidx : ∀ i < S.1.size, ∀ {s : Array Nat} {k' : Nat}, k' < S.1.size →
      S.1[k']! = applyTab s S.1[i]! →
      S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0 = k' := by
    intro i _ s k' hk' e
    rw [← e]
    exact hmg k' hk'
  have hpl : E.1.par.length = S.1.size := by
    have := congrArg List.length hp
    simp only [Array.length_toList, List.length_reverse] at this
    omega
  refine ⟨hq1', hinvq, ⟨by rw [ext_size he0]; simp [S0], by rw [ext_get he0 (by simp [S0])]; rfl,
    hps, hpar, keys_nodup hw hc, fun i hi j hj => ?_, fun i hi j hj => ?_⟩,
    by rw [← hcnt]; exact hE3, hcnt, hpl, fun i hi => by rw [arr_getN, hp],
    by rw [hcll, hiS], fun t ht j hj => ?_⟩
  · have hs : G[j]! ∈ G := by rw [getElem!_pos G j hj]; exact List.getElem_mem _
    obtain ⟨k', hk', e⟩ := hokc i hi _ hs
    rw [hclget i hi j (by simp; omega), getBang_append_left hj, hidx i hi hk' e]
    exact ⟨hk', e⟩
  · have hjq : j < qp.length := by omega
    have hmem : applyTab Gi[j]! S.1[i]! ∈ S.1.toList := by
      apply closed_inv (s := G[j]!) (n := n)
      · intro q hq
        rw [hGj j hjq, hGij j hjq]
        exact hinvq _ (List.getElem_mem _) q hq
      · exact fun U hU => (hv U hU).2
      · intro U hU
        obtain ⟨i', hi', rfl⟩ := mem_idx hU
        have hs : G[j]! ∈ G := by rw [getElem!_pos G j (by omega)]; exact List.getElem_mem _
        obtain ⟨k', hk', e⟩ := hokc i' hi' _ hs
        rw [← e]
        exact get_mem hk'
      · exact get_mem hi
    obtain ⟨k', hk', e⟩ := mem_idx hmem
    rw [Nat.add_assoc, hclget i hi _ (by simp; omega), getBang_append_right hj,
      hidx i hi hk' e]
    exact ⟨hk', e⟩
  · have hjG : j < Gp.length := by omega
    have hpos : t * (qp.length + qp.length) + j < E.1.cl.length := by
      rw [hcll, hiS]
      exact pos_lt ht (by omega)
    obtain ⟨-, hmem, hix⟩ := hcl.2 t j (by rw [List.length_map]; exact hjG) hpos
    have hgd : (Gp.map Prod.fst).getD j 0 = Gp[j].1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjG]
      rfl
    have hGpj := hGp Gp[j] (List.getElem_mem _)
    have hGjp : G[j]! = Gp[j].2 := by
      rw [getElem!_pos G j (by omega)]
      simp only [← hGs, List.getElem_map]
    have hrt : E.1.rev.reverse.getD t [] = S.1[t]! := by rw [← hr, arr_getL]
    rw [hgd, hrt, imgsW_rep hGpj.1 (val_get hv ht).2, ← hGjp] at hmem hix
    have hcv : Val n (ptsOf B G).length (applyTab G[j]! S.1[t]!) :=
      ⟨by rw [applyTab, List.length_map]; exact (val_get hv ht).1,
        applyTab_lt (hGjp ▸ hGpj.1) (val_get hv ht).2⟩
    obtain ⟨i', hi', e⟩ := (hm _).1 hmem
    have hix' := (hl i' hi').1
    rw [e, hix] at hix'
    have e' := (keyW_iff_keyNat hw (val_get hv hi') hcv).1 e
    have hcg := hclget t ht j (by simp; omega)
    rw [hGl, hGil] at hcg
    rw [hcg, getBang_append_left (by omega), ← e', hmg i' hi', hix']

end CFSG.KC.LQT.BW.Cl

end
