module

public import CFSG.Certificates.Kernel.TwoNodeSmall.ExclLane
public import CFSG.Certificates.Kernel.TwoNodeSmall.PosBKSound

public section

namespace CFSG.TwoNodeSmall.ExclK

open CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exclFilt (p N s : Nat) (o : Nat × Nat × Nat) (c : Vec) : Bool :=
  (List.range (N - 1)).all fun j =>
    !(s ≤ j && j < s + (N - 3)) || dotP p (cartanRowP p N j) c == if j - s = o.1 then o.2.1 else 0

@[expose] def exclGrp (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (cs : List Vec) :
    List SPt :=
  let inJ := fun k => s ≤ k && k < s + (N - 3)
  let outs := (List.range (N - 1)).filter fun k => !(inJ k)
  cs.flatMap fun c =>
    (allVecsP p 2).map fun fr =>
      let vv : Nat → Nat := fun k =>
        if inJ k then (if k - s = o.1 then o.2.2 else 0)
        else if outs.head? = some k then fr.getD 0 0 else fr.getD 1 0
      let D := if lift then N else N - 1
      let ext := fun (v : Vec) (e : Nat) => if lift then v ++ [e] else v
      ⟨{ p := p, D := D, nFrame := N - 1,
         gens := (List.range (N - 1)).map (fun k =>
             (⟨ext (cartanRowP p N k) (if k = 0 then 1 else 0), unitP D k⟩ : Refl)) ++
           [⟨ext ((List.range (N - 1)).map vv) 0, ext c 0⟩],
         x := ext ((List.range (N - 1)).map (· + 1)) 0, bound := posBound p N }, s⟩

theorem exclCell_eq (lift : Bool) (p N : Nat) : exclCell lift p N = [0, 1, 2].flatMap fun s =>
    (posOpts p N).flatMap fun o => exclGrp lift p N s o ((allVecsP p (N - 1)).filter (exclFilt p N s o)) :=
  rfl

section Walk

open LaneSound PosBK.GBS

theorem exw_two_mod {p : Nat} (hp57 : p = 5 ∨ p = 7) : 2 % p = 2 := by
  rcases hp57 with rfl | rfl <;> rfl

theorem exw_easy {Q : SPt} {p : Nat} (hp : Q.pt.p = p) (hp57 : p = 5 ∨ p = 7) (hD : Q.pt.D ≤ 10)
    {G : List (Nat × Nat)}
    (hGq : G ++ [packR p Q.pt.D Q.pt.lastRefl] = Q.pt.gens.map (packR p Q.pt.D))
    (h : (Nat.beq (dotK (fdOf p Q.pt.D) (packR p Q.pt.D Q.pt.lastRefl).2 (pkP p Q.pt.D Q.pt.x)) 0 ||
      !(reflOK (fdOf p Q.pt.D) (packR p Q.pt.D Q.pt.lastRefl))) = true) :
    ∃ w, verifyExcl Q w = true := by
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · refine ⟨.fixed, ?_⟩
    have h' := Nat.eq_of_beq_eq_true h
    have e : dotK (fdOf p Q.pt.D) (packR p Q.pt.D Q.pt.lastRefl).2 (pkP p Q.pt.D Q.pt.x) =
        Q.pt.dotv Q.pt.lastRefl.f Q.pt.x := dotKP_pk hp (by omega) (by omega) hD _ _
    rw [e] at h'
    simp only [verifyExcl, verifyPos, verifyF, h', beq_self_eq_true]
  · refine ⟨.self_, ?_⟩
    have hq : reflOK (fdOf p Q.pt.D) (packR p Q.pt.D Q.pt.lastRefl) = false := by simpa using h
    have hmem : packR p Q.pt.D Q.pt.lastRefl ∈ Q.pt.gens.map (packR p Q.pt.D) := by
      rw [← hGq]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    obtain ⟨r, hr, hrq⟩ := List.mem_map.mp hmem
    have hw : wfCheck Q.pt = false := by
      rw [← Bool.not_eq_true]
      intro hw
      have h1 := beq_iff_eq.mp (List.all_eq_true.mp hw r hr)
      rw [hp, exw_two_mod hp57] at h1
      have h2 : reflOK (fdOf p Q.pt.D) (packR p Q.pt.D r) = true :=
        (reflOKP_pk hp (by omega) (by omega) hD r.h r.f).mpr h1
      rw [hrq, hq] at h2
      exact Bool.false_ne_true h2
    simp only [verifyExcl, verifyPos, verifyS, hw, Bool.not_false]

theorem exw_wf {Q : SPt} {p : Nat} (hp : Q.pt.p = p) (hp57 : p = 5 ∨ p = 7) (hD : Q.pt.D ≤ 10)
    {G : List (Nat × Nat)}
    (hGq : G ++ [packR p Q.pt.D Q.pt.lastRefl] = Q.pt.gens.map (packR p Q.pt.D))
    (hG : G.all (reflOK (fdOf p Q.pt.D)) = true)
    (hq : reflOK (fdOf p Q.pt.D) (packR p Q.pt.D Q.pt.lastRefl) = true) : wfCheck Q.pt = true := by
  unfold wfCheck
  rw [List.all_eq_true]
  intro r hr
  have hm : packR p Q.pt.D r ∈ G ++ [packR p Q.pt.D Q.pt.lastRefl] := by
    rw [hGq]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  have h2 : reflOK (fdOf p Q.pt.D) (packR p Q.pt.D r) = true := by
    rcases List.mem_append.mp hm with h | h
    · exact List.all_eq_true.mp hG _ h
    · rw [List.mem_singleton.mp h]
      exact hq
  have h3 := (reflOKP_pk hp (by omega) (by omega) hD r.h r.f).mp h2
  rw [h3, hp, exw_two_mod hp57]
  exact beq_self_eq_true 2

theorem exw_hard {Q : SPt} {p n m : Nat} (hp : Q.pt.p = p) (hp57 : p = 5 ∨ p = 7)
    (hD : Q.pt.D ≤ 10) (hn : n = Q.pt.gens.length) (hm : m = Q.pt.nFrame - 2)
    (hsm : Q.s + m ≤ n) (hwf : wfCheck Q.pt = true) {r : Rec}
    (h : recOK (fdOf p Q.pt.D) (Q.pt.gens.map (packR p Q.pt.D)) n Q.s m Q.pt.D r = true) :
    ∃ w, verifyExcl Q w = true := by
  subst hn hm hp
  rw [← fdB_of_ne (p := Q.pt.p) Q.pt.D (by omega)] at h
  rcases recOK_verify (Or.inr hp57) hD hwf hsm h with ⟨t, ht⟩ | ⟨c, hc⟩
  · exact ⟨.transv t, by simp only [verifyExcl, verifyPos, hwf, ht, Bool.and_self]⟩
  · exact ⟨.cycle c, by simp only [verifyExcl, verifyPos, hwf, hc, Bool.and_self]⟩

theorem exw_walk {F : Fd} {G : List (Nat × Nat)} {X n s m D : Nat} {pk : SPt → Nat × Nat}
    {V : SPt → Prop} : ∀ Qs : List SPt,
    (∀ Q ∈ Qs, (Nat.beq (dotK F (pk Q).2 X) 0 || !(reflOK F (pk Q))) = true → V Q) →
    (∀ Q ∈ Qs, ∀ r : Rec, (Nat.beq (dotK F (pk Q).2 X) 0 || !(reflOK F (pk Q))) = false →
      recOK F (G ++ [pk Q]) n s m D r = true → V Q) →
    ∀ rs : List Rec, grpK F G X n s m D (Qs.map pk) rs = true → ∀ Q ∈ Qs, V Q
  | [], _, _, _, _, Q, hQ => by simp at hQ
  | Q :: Qs, he, hh, rs, h, Q', hQ' => by
    change (bif (Nat.beq (dotK F (pk Q).2 X) 0 || !(reflOK F (pk Q))) then
        grpK F G X n s m D (Qs.map pk) rs
      else List.rec (motive := fun _ => Bool) false
        (fun r rs' _ => recOK F (G ++ [pk Q]) n s m D r && grpK F G X n s m D (Qs.map pk) rs')
        rs) = true at h
    have he' := fun Q (hm : Q ∈ Qs) => he Q (List.mem_cons_of_mem _ hm)
    have hh' := fun Q (hm : Q ∈ Qs) => hh Q (List.mem_cons_of_mem _ hm)
    cases hb : (Nat.beq (dotK F (pk Q).2 X) 0 || !(reflOK F (pk Q))) with
    | true =>
      rw [hb, cond_true] at h
      rcases List.mem_cons.mp hQ' with rfl | hm
      · exact he _ List.mem_cons_self hb
      · exact exw_walk Qs he' hh' rs h Q' hm
    | false =>
      rw [hb, cond_false] at h
      cases rs with
      | nil => exact absurd h Bool.false_ne_true
      | cons r rs' =>
        change (recOK F (G ++ [pk Q]) n s m D r && grpK F G X n s m D (Qs.map pk) rs') = true at h
        rw [Bool.and_eq_true] at h
        rcases List.mem_cons.mp hQ' with rfl | hm
        · exact hh _ List.mem_cons_self r hb h.1
        · exact exw_walk Qs he' hh' rs' h.2 Q' hm

end Walk

open LaneSound in
theorem grpAt_verify {lift : Bool} {p N s oi : Nat} {cs : List Vec} {rs : List Rec}
    (_hpN : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7)) (_hs : s < 3)
    (_h : grpAt lift p N s oi cs rs = true) :
    ∀ Q ∈ exclGrp lift p N s (optOf p N oi) cs, ∃ w, verifyExcl Q w = true := by
  have hp57 : p = 5 ∨ p = 7 := by omega
  have hD : dimOf lift N ≤ 10 := by
    unfold dimOf
    split <;> omega
  have hexcl : exclGrp lift p N s (optOf p N oi) cs = cs.flatMap fun c => (allVecsP p 2).map
      fun fr => (⟨ptOf lift p N s (optOf p N oi) c fr, s⟩ : SPt) := rfl
  have hpts : ptsK lift p N s oi cs = (exclGrp lift p N s (optOf p N oi) cs).map
      fun Q => packR p (dimOf lift N) Q.pt.lastRefl := by
    rw [ptsK_eq _hpN _hs, hexcl, List.map_flatMap]
    congr 1
    funext c
    rw [List.map_map]
    rfl
  have h' : ((frameK lift p N).all (reflOK (fdOf p (dimOf lift N))) &&
      grpK (fdOf p (dimOf lift N)) (frameK lift p N) (xK lift p N) N s (N - 3) (dimOf lift N)
        (ptsK lift p N s oi cs) rs) = true := _h
  rw [Bool.and_eq_true, hpts] at h'
  obtain ⟨hG, hK⟩ := h'
  have mem : ∀ Q ∈ exclGrp lift p N s (optOf p N oi) cs, ∃ c fr,
      Q = (⟨ptOf lift p N s (optOf p N oi) c fr, s⟩ : SPt) := by
    intro Q hQ
    rw [hexcl, List.mem_flatMap] at hQ
    obtain ⟨c, -, hQ⟩ := hQ
    obtain ⟨fr, -, rfl⟩ := List.mem_map.mp hQ
    exact ⟨c, fr, rfl⟩
  have hlen : ∀ c fr, (ptOf lift p N s (optOf p N oi) c fr).gens.length = N := by
    intro c fr
    rw [gens_ptOf, List.length_append, length_frameRefl, List.length_singleton]
    omega
  refine exw_walk (V := fun Q => ∃ w, verifyExcl Q w = true) _ ?_ ?_ rs hK
  · intro Q hQ hb
    obtain ⟨c, fr, rfl⟩ := mem Q hQ
    exact exw_easy rfl hp57 hD (frameK_append lift p N s _ c fr) hb
  · intro Q hQ r hb hr
    obtain ⟨c, fr, rfl⟩ := mem Q hQ
    rw [Bool.or_eq_false_iff] at hb
    have hq : reflOK (fdOf p (dimOf lift N))
        (packR p (dimOf lift N) (ptOf lift p N s (optOf p N oi) c fr).lastRefl) = true := by
      simpa using hb.2
    have hwf := exw_wf (Q := ⟨ptOf lift p N s (optOf p N oi) c fr, s⟩) rfl hp57 hD
      (frameK_append lift p N s _ c fr) hG hq
    have hr' : recOK (fdOf p (dimOf lift N)) ((ptOf lift p N s (optOf p N oi) c fr).gens.map
        (packR p (dimOf lift N))) N s (N - 3) (dimOf lift N) r = true := by
      have e := frameK_append lift p N s (optOf p N oi) c fr
      change recOK (fdOf p (dimOf lift N)) ((ptOf lift p N s (optOf p N oi) c fr).gens.map
        (packR p (ptOf lift p N s (optOf p N oi) c fr).D)) N s (N - 3) (dimOf lift N) r = true
      rw [← e]
      exact hr
    have hm : N - 3 = (ptOf lift p N s (optOf p N oi) c fr).nFrame - 2 := by
      change N - 3 = N - 1 - 2
      omega
    exact exw_hard (Q := ⟨ptOf lift p N s (optOf p N oi) c fr, s⟩) rfl hp57 hD (hlen c fr).symm hm
      (by change s + (N - 3) ≤ N; omega) hwf hr'

theorem grpAt_closed {lift : Bool} {p N s oi : Nat} {cs : List Vec} {rs : List Rec}
    (hpN : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7)) (hs : s < 3) (h : grpAt lift p N s oi cs rs = true) :
    ∀ Q ∈ exclGrp lift p N s (optOf p N oi) cs, ∀ [Fact Q.pt.p.Prime], Q.ClosedExcl := by
  intro Q hQ _
  obtain ⟨w, hw⟩ := grpAt_verify hpN hs h Q hQ
  exact verifyExcl_elim hw Or.inl (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h)))
    (fun h => Or.inr (Or.inr (Or.inr h)))

theorem foldl_add_eq (l : List Nat) (acc : Nat) : l.foldl (· + ·) acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.sum_cons]
    omega

theorem dotS_nil (b : Vec) : dotS [] b = 0 := by
  cases b <;> rfl

theorem dotS_cons_nil (x : Nat) (a : Vec) : dotS (x :: a) [] = 0 := rfl

theorem dotS_cons_cons (x y : Nat) (a b : Vec) : dotS (x :: a) (y :: b) = x * y + dotS a b := rfl

theorem sum_range_getD : ∀ (a b : Vec) (m : Nat), a.length ≤ m → b.length ≤ m →
    ((List.range m).map fun i => a.getD i 0 * b.getD i 0).sum = dotS a b
  | [], b, m, _, _ => by simp [dotS_nil]
  | x :: a, [], m, _, _ => by simp [dotS_cons_nil]
  | x :: a, y :: b, 0, ha, _ => by simp at ha
  | x :: a, y :: b, m + 1, ha, hb => by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def, List.getD_cons_zero,
      List.getD_cons_succ, dotS_cons_cons]
    rw [sum_range_getD a b m (by simpa using ha) (by simpa using hb)]

theorem dotP_eq (p : Nat) (a b : Vec) : dotP p a b = dotS a b % p := by
  unfold dotP
  rw [foldl_add_eq, Nat.zero_add, sum_range_getD a b _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)]

theorem dotS_cons_free (c : Vec) (a : Nat) (v : Vec) (h : (c.headD 0 == 0) = true) :
    dotS c (a :: v) = dotS c.tail v := by
  cases c with
  | nil => rw [dotS_nil, List.tail_nil, dotS_nil]
  | cons x c =>
    simp only [List.headD_cons, beq_iff_eq] at h
    subst h
    rw [dotS_cons_cons, Nat.zero_mul, Nat.zero_add, List.tail_cons]

theorem satC_cons (p : Nat) (cs : List (Vec × Nat)) (a : Nat) (v : Vec) :
    satC p cs (a :: v) =
      (satC p ((cs.filter fun q => q.1.headD 0 == 0).map fun q => (q.1.tail, q.2)) v &&
        satC p (cs.filter fun q => q.1.headD 0 != 0) (a :: v)) := by
  induction cs with
  | nil => rfl
  | cons q cs ih =>
    unfold satC at ih ⊢
    cases hq : (q.1.headD 0 == 0) with
    | true =>
      have hb : (q.1.headD 0 != 0) = false := by rw [bne, hq]; rfl
      simp only [List.filter_cons, hq, hb, if_true, Bool.false_eq_true, if_false, List.map_cons,
        List.all_cons, dotS_cons_free q.1 a v hq, ih, Bool.and_assoc]
    | false =>
      have hb : (q.1.headD 0 != 0) = true := by rw [bne, hq]; rfl
      simp only [List.filter_cons, hq, hb, if_true, Bool.false_eq_true, if_false, List.all_cons, ih]
      cases (dotS q.1 (a :: v) % p == q.2) <;> simp

theorem filter_map_cons (p : Nat) (l : List Nat) (cs : List (Vec × Nat)) (v : Vec) :
    (l.map (· :: v)).filter (satC p cs) =
      if satC p ((cs.filter fun q => q.1.headD 0 == 0).map fun q => (q.1.tail, q.2)) v then
        (l.map (· :: v)).filter (satC p (cs.filter fun q => q.1.headD 0 != 0))
      else [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons, ih, satC_cons]
    cases satC p ((cs.filter fun q => q.1.headD 0 == 0).map fun q => (q.1.tail, q.2)) v <;> simp

theorem filter_allVecsP (p : Nat) :
    ∀ (n : Nat) (cs : List (Vec × Nat)), (allVecsP p n).filter (satC p cs) = enumPf p n cs
  | 0, cs => by
    simp only [allVecsP, enumPf, List.filter_cons, List.filter_nil]
  | n + 1, cs => by
    rw [allVecsP, List.filter_flatMap]
    simp only [filter_map_cons p (List.range p) cs]
    rw [PtsK.flatMap_ite, filter_allVecsP p n, enumPf]

theorem exclFilt_eq (p N s oi : Nat) : exclFilt p N s (optOf p N oi) = satC p (consC p N s oi) := by
  funext c
  simp only [exclFilt, satC, consC, inJ, List.all_map, List.all_filter, dotP_eq, Function.comp_def]

theorem cell_closed {CS : List (List Vec)} {RS : List (List Rec)}
    (hc : ∀ i < 42, csAt i (CS.getD i []) = true) (hg : ∀ g < 84, grpIdx CS RS g = true)
    (lift : Bool) (p N off : Nat) (hpN : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7))
    (hpar : ∀ s < 3, ∀ oi < (posOpts p N).length, off + (posOpts p N).length * s + oi < 42 ∧
      (cpars ()).getD (off + (posOpts p N).length * s + oi) (0, 0, 0, 0) = (p, N, s, oi)) :
    ∀ Q ∈ exclCell lift p N, ∀ [Fact Q.pt.p.Prime], Q.ClosedExcl := by
  intro Q hQ _
  rw [exclCell_eq] at hQ
  simp only [List.mem_flatMap] at hQ
  obtain ⟨s, hs, o, ho, hQ⟩ := hQ
  obtain ⟨oi, hoi, rfl⟩ := List.getElem_of_mem ho
  have hs3 : s < 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    omega
  obtain ⟨hi, hq⟩ := hpar s hs3 oi hoi
  have hopt : optOf p N oi = (posOpts p N)[oi] := by
    simp only [optOf, List.getD_eq_getElem _ _ hoi]
  have hcs : enumPf p (N - 1) (consC p N s oi) = CS.getD (off + (posOpts p N).length * s + oi) [] := by
    have h1 := hc _ hi
    simp only [csAt, hq] at h1
    exact beq_iff_eq.mp h1
  rw [← hopt, exclFilt_eq, filter_allVecsP, hcs] at hQ
  have key : ∀ g < 84, g % 42 = off + (posOpts p N).length * s + oi → (!(Nat.blt g 42)) = lift →
      Q.ClosedExcl := by
    intro g hg84 hmod hl
    have hg' := hg g hg84
    simp only [grpIdx, hmod, hq, hl] at hg'
    exact grpAt_closed hpN hs3 hg' Q hQ
  cases lift
  · exact key _ (by omega) (Nat.mod_eq_of_lt hi) (by simp [Nat.blt_eq, hi])
  · refine key (42 + (off + (posOpts p N).length * s + oi)) (by omega) (by omega) ?_
    cases h : Nat.blt (42 + (off + (posOpts p N).length * s + oi)) 42
    · rfl
    · have h' := Nat.le_of_ble_eq_true h
      omega

theorem excl_closed_of {CS : List (List Vec)} {RS : List (List Rec)}
    (hc : ∀ i < 42, csAt i (CS.getD i []) = true) (hg : ∀ g < 84, grpIdx CS RS g = true) :
    ∀ Q ∈ exclPts (), ∀ [Fact Q.pt.p.Prime], Q.ClosedExcl := by
  intro Q hQ _
  simp only [exclPts, List.mem_append] at hQ
  rcases hQ with ((hQ | hQ) | hQ) | hQ
  · exact cell_closed hc hg false 5 5 0 (Or.inl ⟨rfl, rfl⟩) (by decide) Q hQ
  · exact cell_closed hc hg false 7 7 18 (Or.inr ⟨rfl, rfl⟩) (by decide) Q hQ
  · exact cell_closed hc hg true 5 5 0 (Or.inl ⟨rfl, rfl⟩) (by decide) Q hQ
  · exact cell_closed hc hg true 7 7 18 (Or.inr ⟨rfl, rfl⟩) (by decide) Q hQ

end CFSG.TwoNodeSmall.ExclK

end
