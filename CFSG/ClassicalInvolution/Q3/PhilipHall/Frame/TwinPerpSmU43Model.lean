module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmU43Code
public import Certificates.Certificate397503
public import Certificates.Certificate320330

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.U43

open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open CFSG.Monster.B.Fischer
open CFSG.GH74.GLS.C3.Layer1.EndN.U43 (hud P43)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
open Certificates.U43Twin
open scoped MatrixGroups

theorem allOK_parts (h : allOK () = true) :
    t0OK () = true ∧ qOK () = true ∧ orbOK () = true ∧ cOK () = true ∧ tOK () = true ∧
      candsOK () = true ∧ invOK () = true ∧ q8OK () = true ∧ permOK () = true ∧ oddOK () = true ∧
      psiOK () = true ∧ centOK () = true ∧ commOK () = true := by
  have h' : (t0OK () && qOK () && orbOK () && cOK () && tOK () && candsOK () && invOK () &&
      q8OK () && permOK () && oddOK () && psiOK () && centOK () && commOK ()) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h'
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem t0_parts {x : Array ℕ} {G : Array (Array ℕ)}
    (h : (rawValid x && innerShape x && isZ (mulRaw x x) && !isZ x &&
      (List.range G.size).all fun k => commC G[k]! x) = true) :
    rawValid x = true ∧ innerShape x = true ∧ isZ (mulRaw x x) = true ∧ isZ x = false ∧
      ∀ k < G.size, commC G[k]! x = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem q_parts {p1 q1 p2 q2 g : Array ℕ}
    (h : ([p1, q1, p2, q2].all (fun x => rawValid x && innerShape x) && q8PairC p1 q1 &&
      q8PairC p2 q2 && invertC g && innerShape g && commC g T0 &&
      memL (conjBy g p2) (q8Elts p1 q1) && memL (conjBy g q2) (q8Elts p1 q1)) = true) :
    (rawValid p1 = true ∧ innerShape p1 = true) ∧ (rawValid q1 = true ∧ innerShape q1 = true) ∧
      (rawValid p2 = true ∧ innerShape p2 = true) ∧ (rawValid q2 = true ∧ innerShape q2 = true) ∧
      q8PairC p1 q1 = true ∧ q8PairC p2 q2 = true ∧ invertC g = true ∧ innerShape g = true ∧
      commC g T0 = true ∧ memL (conjBy g p2) (q8Elts p1 q1) = true ∧
      memL (conjBy g q2) (q8Elts p1 q1) = true := by
  simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  obtain ⟨ha, hb, hc, hd⟩ := h1
  exact ⟨ha, hb, hc, hd, h2, h3, h4, h5, h6, h7, h8⟩

theorem c_parts {G : Array (Array ℕ)} {f : ℕ → Array ℕ → Array ℕ} {x : Array ℕ} {c : ArrCert}
    {n : ℕ}
    (h : ((List.range G.size).all (fun k => rawValid G[k]! && innerShape G[k]! && commC G[k]! x) &&
      (arrCertOK f G.size valid keyOf idCode c && c.pts.size == n)) = true) :
    (∀ k < G.size, rawValid G[k]! = true ∧ innerShape G[k]! = true ∧ commC G[k]! x = true) ∧
      arrCertOK f G.size valid keyOf idCode c = true ∧ c.pts.size = n := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨hg, hc, hs⟩ := h
  refine ⟨fun k hk => ?_, hc, hs⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg k hk
  exact ⟨h1, h2, h3⟩

theorem t_parts {G : Array (Array ℕ)} {f : ℕ → Array ℕ → Array ℕ} {c : ArrCert} {n : ℕ}
    (h : ((List.range G.size).all (fun k => rawValid G[k]! && innerShape G[k]!) &&
      (arrCertOK f G.size valid keyOf idCode c && c.pts.size == n)) = true) :
    (∀ k < G.size, rawValid G[k]! = true ∧ innerShape G[k]! = true) ∧
      arrCertOK f G.size valid keyOf idCode c = true ∧ c.pts.size = n := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨hg, hc, hs⟩ := h
  exact ⟨fun k hk => hg k hk, hc, hs⟩

theorem cands_parts {L : Array (Array ℕ)}
    (h : (L.toList.all fun c => invertC c && innerShape c && commC c T0) = true) :
    ∀ c ∈ L.toList, invertC c = true ∧ innerShape c = true ∧ commC c T0 = true := by
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  intro c hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := h c hc
  exact ⟨h1, h2, h3⟩

theorem inv_at {pts : Array (Array ℕ)} {L : List (Array ℕ)} {t : Array ℕ}
    (h : ((List.range pts.size).all fun i =>
      !(isZ (mulRaw pts[i]! pts[i]!) && !isZ pts[i]!) ||
        L.any fun e => rawValid e && eqZ (mulRaw e pts[i]!) (mulRaw t e)) = true)
    {i : ℕ} (hi : i < pts.size) (h2 : isZ (mulRaw pts[i]! pts[i]!) = true)
    (h1 : isZ pts[i]! = false) :
    ∃ e ∈ L, rawValid e = true ∧ eqZ (mulRaw e pts[i]!) (mulRaw t e) = true := by
  rw [List.all_eq_true] at h
  have h3 := h i (List.mem_range.mpr hi)
  rw [h2, h1] at h3
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
    Bool.and_eq_true] at h3
  obtain ⟨e, he, h4, h5⟩ := h3
  exact ⟨e, he, h4, h5⟩

theorem q8_at {pts : Array (Array ℕ)} {E1 E2 L : List (Array ℕ)} {t : Array ℕ}
    (h : ((List.range pts.size).filter (fun i => eqZ (mulRaw pts[i]! pts[i]!) t)).all (fun i =>
      ((List.range pts.size).filter (fun i => eqZ (mulRaw pts[i]! pts[i]!) t)).all fun j =>
        !eqZ (mulRaw pts[j]! pts[i]!) (mulRaw (mulRaw t pts[i]!) pts[j]!) ||
          (memL pts[i]! E1 && memL pts[j]! E1) || (memL pts[i]! E2 && memL pts[j]! E2) ||
          L.any fun c => violC (q8Elts pts[i]! pts[j]!) c) = true)
    {i j : ℕ} (hi : i < pts.size) (hj : j < pts.size)
    (hsi : eqZ (mulRaw pts[i]! pts[i]!) t = true) (hsj : eqZ (mulRaw pts[j]! pts[j]!) t = true)
    (hr : eqZ (mulRaw pts[j]! pts[i]!) (mulRaw (mulRaw t pts[i]!) pts[j]!) = true) :
    (memL pts[i]! E1 = true ∧ memL pts[j]! E1 = true) ∨
      (memL pts[i]! E2 = true ∧ memL pts[j]! E2 = true) ∨
      ∃ c ∈ L, violC (q8Elts pts[i]! pts[j]!) c = true := by
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_filter.mpr ⟨List.mem_range.mpr hi, hsi⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 j (List.mem_filter.mpr ⟨List.mem_range.mpr hj, hsj⟩)
  rw [hr] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    List.any_eq_true] at h2
  rcases h2 with (h3 | h3) | h3
  · exact Or.inl h3
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h3)

theorem perm_at {pts : Array (Array ℕ)} {E1 E2 : List (Array ℕ)} {a b : Array ℕ}
    (h : ((List.range pts.size).all fun i => invertC pts[i]! &&
      ((memL (conjBy pts[i]! a) E1 && memL (conjBy pts[i]! b) E1) ||
        (memL (conjBy pts[i]! a) E2 && memL (conjBy pts[i]! b) E2))) = true)
    {i : ℕ} (hi : i < pts.size) :
    invertC pts[i]! = true ∧
      ((memL (conjBy pts[i]! a) E1 = true ∧ memL (conjBy pts[i]! b) E1 = true) ∨
        (memL (conjBy pts[i]! a) E2 = true ∧ memL (conjBy pts[i]! b) E2 = true)) := by
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
  exact h1

theorem odd_at {pts : Array (Array ℕ)} {G : List (Array ℕ)}
    (h : ((List.range pts.size).all fun i => isZ pts[i]! || !isZ (powRaw pts[i]! 9) ||
      G.any fun g => evenC (mulRaw (mulRaw (mulRaw pts[i]! g) (powRaw pts[i]! 8)) (powRaw g 3))) =
      true)
    {i : ℕ} (hi : i < pts.size) (h1 : isZ pts[i]! = false) (h9 : isZ (powRaw pts[i]! 9) = true) :
    ∃ g ∈ G, evenC (mulRaw (mulRaw (mulRaw pts[i]! g) (powRaw pts[i]! 8)) (powRaw g 3)) = true := by
  rw [List.all_eq_true] at h
  have h2 := h i (List.mem_range.mpr hi)
  rw [h1, h9] at h2
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at h2
  exact h2

theorem psi_parts {tab : Array (Array ℕ)} {a b : Array ℕ}
    (h : ((slQuads.all fun m => rawValid tab[qidx m]! && innerShape tab[qidx m]! &&
      commC tab[qidx m]! a && commC tab[qidx m]! b && (m == (1, 0, 0, 1) || !isZ tab[qidx m]!)) &&
      slQuads.all fun m => slQuads.all fun n =>
        eqZ tab[qidx (qmul m n)]! (mulRaw tab[qidx m]! tab[qidx n]!)) = true) :
    (∀ m ∈ slQuads, rawValid tab[qidx m]! = true ∧ innerShape tab[qidx m]! = true ∧
      commC tab[qidx m]! a = true ∧ commC tab[qidx m]! b = true ∧
      (m = (1, 0, 0, 1) ∨ isZ tab[qidx m]! = false)) ∧
    ∀ m ∈ slQuads, ∀ n ∈ slQuads,
      eqZ tab[qidx (qmul m n)]! (mulRaw tab[qidx m]! tab[qidx n]!) = true := by
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun m hm => ?_, h2⟩
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩ := h1 m hm
  exact ⟨ha, hb, hc, hd, he⟩

theorem cent_at {pts : Array (Array ℕ)} {psiL H : List (Array ℕ)} {a2 b2 a1 b1 : Array ℕ}
    (h : ((List.range pts.size).all fun i =>
      (!(commC pts[i]! a2 && commC pts[i]! b2) || memL pts[i]! psiL) &&
        (!(commC pts[i]! a1 && commC pts[i]! b1) || memL pts[i]! H)) = true)
    {i : ℕ} (hi : i < pts.size) :
    (commC pts[i]! a2 = true → commC pts[i]! b2 = true → memL pts[i]! psiL = true) ∧
      (commC pts[i]! a1 = true → commC pts[i]! b1 = true → memL pts[i]! H = true) := by
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true] at h1
  obtain ⟨h2, h3⟩ := h1
  refine ⟨fun ha hb => ?_, fun ha hb => ?_⟩
  · rw [ha, hb] at h2
    simpa using h2
  · rw [ha, hb] at h3
    simpa using h3

theorem comm_parts {tab H : Array (Array ℕ)}
    (h : (H.toList.all fun h => rawValid h && slQuads.all fun m => commC tab[qidx m]! h) = true) :
    ∀ y ∈ H.toList, rawValid y = true ∧ ∀ m ∈ slQuads, commC tab[qidx m]! y = true := by
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h

section Model

theorem allOK_true : allOK () = true := Certificates.certificate397503

@[expose] noncomputable def tz : MulAut P43 := ev T0

theorem t0_facts : rawValid T0 = true ∧ innerShape T0 = true ∧ isZ (mulRaw T0 T0) = true ∧
    isZ T0 = false ∧ ∀ k < u43Data.gens.size, commC u43Data.gens[k]! T0 = true :=
  t0_parts (allOK_parts allOK_true).1

theorem rawValid_T0 : rawValid T0 = true := t0_facts.1

theorem tz_mul_self : tz * tz = 1 := by
  unfold tz
  rw [← ev_mulRaw rawValid_T0 rawValid_T0]
  exact (ev_eq_one_iff (rawValid_mulRaw rawValid_T0 rawValid_T0)).2 t0_facts.2.2.1

theorem tz_ne_one : tz ≠ 1 := by
  intro h
  have := (ev_eq_one_iff rawValid_T0).1 h
  rw [t0_facts.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem sylowOK_parts {D : Data} (h : sylowOK D = true) :
    (∀ k < D.gens.size, rawValid D.gens[k]! = true) ∧
      arrCertOK (act D.gens) D.gens.size valid keyOf idCode (bfs D) = true ∧
      (bfs D).pts.size = 1024 := by
  unfold sylowOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨hg, hc⟩, hs⟩ := h
  exact ⟨hg, hc, hs⟩

@[expose] noncomputable def sylS : Subgroup (MulAut P43) := codeSub u43Data.gens

theorem sylS_spec :
    (∀ g : MulAut P43, g ∈ sylS ↔ ∃ i < (bfs u43Data).pts.size, ev (bfs u43Data).pts[i]! = g) ∧
      Nat.card sylS = 1024 ∧ ∀ i < (bfs u43Data).pts.size, valid (bfs u43Data).pts[i]! = true := by
  obtain ⟨hg, hc, hs⟩ := sylowOK_parts (Certificates.certificate320330)
  obtain ⟨h1, h2, h3⟩ := codeSub_spec hg hc
  exact ⟨h1, h2.trans hs, h3⟩

theorem sylS_isPGroup : IsPGroup 2 sylS :=
  IsPGroup.of_card (n := 10) (by rw [sylS_spec.2.1]; norm_num)

theorem sylS_index_odd : ¬ 2 ∣ sylS.index := by
  intro h2
  have hc := Subgroup.card_mul_index sylS
  rw [sylS_spec.2.1] at hc
  have hd : 1024 * sylS.index ∣ 2 ^ 10 * 25515 := hc ▸ card_mulAut_dvd
  have hd' : sylS.index ∣ 25515 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 1024) (by simpa using hd)
  have := h2.trans hd'
  omega

theorem sylS_le_centralizer : sylS ≤ Subgroup.centralizer ({tz} : Set (MulAut P43)) := by
  obtain ⟨hg, -, -⟩ := sylowOK_parts (Certificates.certificate320330)
  rw [sylS, codeSub, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    ((commC_iff (hg k hk) rawValid_T0).1 (t0_facts.2.2.2.2 k hk))

@[expose] noncomputable def centT : Subgroup (MulAut P43) := codeSub gC

theorem centT_spec :
    (∀ g : MulAut P43, g ∈ centT ↔ ∃ i < (cCert ()).pts.size, ev (cCert ()).pts[i]! = g) ∧
      Nat.card centT = 1152 ∧ ∀ i < (cCert ()).pts.size, valid (cCert ()).pts[i]! = true := by
  obtain ⟨hg, hc, hs⟩ := c_parts (f := act gC) (c := cCert ()) (allOK_parts allOK_true).2.2.2.1
  obtain ⟨h1, h2, h3⟩ := codeSub_spec (fun k hk => (hg k hk).1) hc
  exact ⟨h1, h2.trans hs, h3⟩

theorem centT_le : centT ≤ inner P43 ⊓ Subgroup.centralizer ({tz} : Set (MulAut P43)) := by
  obtain ⟨hg, -, -⟩ := c_parts (f := act gC) (c := cCert ()) (allOK_parts allOK_true).2.2.2.1
  rw [centT, codeSub, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨hv, hin, hcm⟩ := hg k hk
  exact Subgroup.mem_inf.mpr ⟨innerShape_mem_inner hv hin,
    Subgroup.mem_centralizer_singleton_iff.mpr ((commC_iff hv rawValid_T0).1 hcm)⟩

theorem mem_centT_iff (x : MulAut P43) : x ∈ centT ↔ x ∈ inner P43 ∧ x * tz = tz * x := by
  have heq : centT = inner P43 ⊓ Subgroup.centralizer ({tz} : Set (MulAut P43)) := by
    refine Subgroup.eq_of_le_of_card_ge centT_le ?_
    rw [centT_spec.2.1]
    exact card_inner_centralizer_le (allOK_parts allOK_true).2.2.1
  rw [heq, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem exists_conj_tz {u : MulAut P43} (hu : u ∈ inner P43) (hu2 : orderOf u = 2) :
    ∃ d : MulAut P43, d * u * d⁻¹ = tz := by
  obtain ⟨hg, hc, hs⟩ := t_parts (f := act gT) (c := tCert ()) (allOK_parts allOK_true).2.2.2.2.1
  obtain ⟨hmem, hcard, hvalid⟩ := codeSub_spec (fun k hk => (hg k hk).1) hc
  have hle : codeSub gT ≤ inner P43 := by
    rw [codeSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact innerShape_mem_inner (hg k hk).1 (hg k hk).2
  have hcardT : Nat.card (codeSub gT) = 128 := hcard.trans hs
  have hp : IsPGroup 2 (codeSub gT) := IsPGroup.of_card (n := 7) (by rw [hcardT]; norm_num)
  have hidx : ¬ 2 ∣ (codeSub gT).relIndex (inner P43) := by
    intro h2
    have h1 := Subgroup.relIndex_mul_card (codeSub gT) (inner P43)
    rw [inf_eq_left.mpr hle, hcardT] at h1
    have hd := card_inner_dvd
    rw [card_P43, ← h1] at hd
    have hd' : (codeSub gT).relIndex (inner P43) ∣ 25515 :=
      Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 128) (by simpa using hd)
    have := h2.trans hd'
    omega
  have hP : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2]; norm_num)
  have hPle : Subgroup.zpowers u ≤ inner P43 := (Subgroup.zpowers_le).mpr hu
  obtain ⟨h, -, hh⟩ := exists_conj_le hle hp hidx hPle hP
  have hv : h * u * h⁻¹ ∈ codeSub gT := hh u (Subgroup.mem_zpowers u)
  obtain ⟨i, hi, hev⟩ := (hmem _).1 hv
  have hxv := rawValid_of_valid (hvalid i hi)
  have hv2 : orderOf (h * u * h⁻¹) = 2 := by rw [orderOf_conj_eq, hu2]
  have h2 : isZ (mulRaw (tCert ()).pts[i]! (tCert ()).pts[i]!) = true := by
    refine (ev_eq_one_iff (rawValid_mulRaw hxv hxv)).1 ?_
    rw [ev_mulRaw hxv hxv, hev, ← pow_two, ← hv2, pow_orderOf_eq_one]
  have h1 : isZ (tCert ()).pts[i]! = false := by
    by_contra hcon
    have h1' : isZ (tCert ()).pts[i]! = true := by simpa using hcon
    have := (ev_eq_one_iff hxv).2 h1'
    rw [hev] at this
    rw [this, orderOf_one] at hv2
    omega
  obtain ⟨e, -, he, hee⟩ := inv_at (pts := (tCert ()).pts) (L := invCands.toList) (t := T0)
    (allOK_parts allOK_true).2.2.2.2.2.2.1 hi h2 h1
  have e1 := (eqZ_iff_ev (rawValid_mulRaw he hxv) (rawValid_mulRaw rawValid_T0 he)).1 hee
  rw [ev_mulRaw he hxv, ev_mulRaw rawValid_T0 he, hev] at e1
  refine ⟨ev e * h, ?_⟩
  calc ev e * h * u * (ev e * h)⁻¹ = ev e * (h * u * h⁻¹) * (ev e)⁻¹ := by group
    _ = tz := by rw [e1]; unfold tz; group

theorem q_facts :
    (rawValid P1 = true ∧ innerShape P1 = true) ∧ (rawValid Q1 = true ∧ innerShape Q1 = true) ∧
      (rawValid P2 = true ∧ innerShape P2 = true) ∧ (rawValid Q2 = true ∧ innerShape Q2 = true) ∧
      q8PairC P1 Q1 = true ∧ q8PairC P2 Q2 = true ∧ invertC G0 = true ∧ innerShape G0 = true ∧
      commC G0 T0 = true ∧ memL (conjBy G0 P2) (q8Elts P1 Q1) = true ∧
      memL (conjBy G0 Q2) (q8Elts P1 Q1) = true :=
  q_parts (allOK_parts allOK_true).2.1

theorem q8PairC_sound {p q : Array ℕ} (hp : rawValid p = true) (hq : rawValid q = true)
    (h : q8PairC p q = true) : ev p ^ 2 = tz ∧ ev q ^ 2 = tz ∧ ev q * ev p = tz * ev p * ev q := by
  simp only [q8PairC, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e1 := (eqZ_iff_ev (rawValid_mulRaw hp hp) rawValid_T0).1 h1
  have e2 := (eqZ_iff_ev (rawValid_mulRaw hq hq) rawValid_T0).1 h2
  have e3 := (eqZ_iff_ev (rawValid_mulRaw hq hp)
    (rawValid_mulRaw (rawValid_mulRaw rawValid_T0 hp) hq)).1 h3
  rw [ev_mulRaw hp hp] at e1
  rw [ev_mulRaw hq hq] at e2
  rw [ev_mulRaw hq hp, ev_mulRaw (rawValid_mulRaw rawValid_T0 hp) hq,
    ev_mulRaw rawValid_T0 hp] at e3
  exact ⟨by rw [pow_two]; exact e1, by rw [pow_two]; exact e2, e3⟩

theorem isQ8Pair_of_q8PairC {p q : Array ℕ} (hp : rawValid p = true) (hq : rawValid q = true)
    (h : q8PairC p q = true) : IsQ8Pair (ev p) (ev q) := by
  obtain ⟨h1, h2, h3⟩ := q8PairC_sound hp hq h
  exact isQ8Pair_of_rel tz_mul_self tz_ne_one h1 h2 h3

@[expose] noncomputable def quat1 : Subgroup (MulAut P43) := Subgroup.closure {ev P1, ev Q1}

@[expose] noncomputable def quat2 : Subgroup (MulAut P43) := Subgroup.closure {ev P2, ev Q2}

theorem isQ8Pair_quat1 : IsQ8Pair (ev P1) (ev Q1) :=
  isQ8Pair_of_q8PairC q_facts.1.1 q_facts.2.1.1 q_facts.2.2.2.2.1

theorem isQ8Pair_quat2 : IsQ8Pair (ev P2) (ev Q2) :=
  isQ8Pair_of_q8PairC q_facts.2.2.1.1 q_facts.2.2.2.1.1 q_facts.2.2.2.2.2.1

theorem card_quat1 : Nat.card quat1 = 8 := card_closure_pair isQ8Pair_quat1

theorem card_quat2 : Nat.card quat2 = 8 := card_closure_pair isQ8Pair_quat2

theorem mem_quat1_iff_code {x : Array ℕ} (hx : rawValid x = true) :
    ev x ∈ quat1 ↔ memL x (q8Elts P1 Q1) = true := by
  rw [memL_iff hx (q8Elts_valid q_facts.1.1 q_facts.2.1.1), quat1,
    mem_closure_pair_iff isQ8Pair_quat1, ← map_ev_q8Elts q_facts.1.1 q_facts.2.1.1, List.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, e.symm⟩
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, e.symm⟩

theorem mem_quat2_iff_code {x : Array ℕ} (hx : rawValid x = true) :
    ev x ∈ quat2 ↔ memL x (q8Elts P2 Q2) = true := by
  rw [memL_iff hx (q8Elts_valid q_facts.2.2.1.1 q_facts.2.2.2.1.1), quat2,
    mem_closure_pair_iff isQ8Pair_quat2, ← map_ev_q8Elts q_facts.2.2.1.1 q_facts.2.2.2.1.1,
    List.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, e.symm⟩
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, e.symm⟩

theorem closure_le_centT {a b : MulAut P43} (ha : a ∈ inner P43) (hb : b ∈ inner P43)
    (hat : a * tz = tz * a) (hbt : b * tz = tz * b) : Subgroup.closure {a, b} ≤ centT := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact (mem_centT_iff _).2 ⟨ha, hat⟩
  · exact (mem_centT_iff _).2 ⟨hb, hbt⟩

theorem comm_of_sq {p : MulAut P43} (hp : p ^ 2 = tz) : p * tz = tz * p := by
  rw [← hp, pow_two, mul_assoc]

theorem quat1_le_centT : quat1 ≤ centT := by
  obtain ⟨h1, h2, -⟩ := q8PairC_sound q_facts.1.1 q_facts.2.1.1 q_facts.2.2.2.2.1
  exact closure_le_centT (innerShape_mem_inner q_facts.1.1 q_facts.1.2)
    (innerShape_mem_inner q_facts.2.1.1 q_facts.2.1.2) (comm_of_sq h1) (comm_of_sq h2)

theorem quat2_le_centT : quat2 ≤ centT := by
  obtain ⟨h1, h2, -⟩ := q8PairC_sound q_facts.2.2.1.1 q_facts.2.2.2.1.1 q_facts.2.2.2.2.2.1
  exact closure_le_centT (innerShape_mem_inner q_facts.2.2.1.1 q_facts.2.2.1.2)
    (innerShape_mem_inner q_facts.2.2.2.1.1 q_facts.2.2.2.1.2) (comm_of_sq h1) (comm_of_sq h2)

theorem quat1_le_inner : quat1 ≤ inner P43 := quat1_le_centT.trans (centT_le.trans inf_le_left)

theorem tz_mem_quat2 : tz ∈ quat2 := by
  rw [← (q8PairC_sound q_facts.2.2.1.1 q_facts.2.2.2.1.1 q_facts.2.2.2.2.2.1).1]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _

theorem tz_mem_quat1 : tz ∈ quat1 := by
  rw [← (q8PairC_sound q_facts.1.1 q_facts.2.1.1 q_facts.2.2.2.2.1).1]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _

theorem map_conj_eq_of_mem {p q c : MulAut P43} (h : IsQ8Pair p q) {Q : Subgroup (MulAut P43)}
    (hQ : Nat.card Q = 8) (hp : c * p * c⁻¹ ∈ Q) (hq : c * q * c⁻¹ ∈ Q) :
    (Subgroup.closure ({p, q} : Set (MulAut P43))).map (MulAut.conj c).toMonoidHom = Q := by
  rw [map_conj_closure_pair]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq
  · rw [hQ, card_closure_pair (isQ8Pair_conj h c)]

theorem g0_facts : ev G0 ∈ centT ∧ quat2.map (MulAut.conj (ev G0)).toMonoidHom = quat1 := by
  obtain ⟨hg, hgv, hgi⟩ := invertC_spec q_facts.2.2.2.2.2.2.1
  refine ⟨(mem_centT_iff _).2 ⟨innerShape_mem_inner hg q_facts.2.2.2.2.2.2.2.1,
    (commC_iff hg rawValid_T0).1 q_facts.2.2.2.2.2.2.2.2.1⟩, ?_⟩
  obtain ⟨hv1, he1⟩ := conjBy_spec q_facts.2.2.2.2.2.2.1 q_facts.2.2.1.1
  obtain ⟨hv2, he2⟩ := conjBy_spec q_facts.2.2.2.2.2.2.1 q_facts.2.2.2.1.1
  refine map_conj_eq_of_mem isQ8Pair_quat2 card_quat1 ?_ ?_
  · rw [← he1, mem_quat1_iff_code hv1]
    exact q_facts.2.2.2.2.2.2.2.2.2.1
  · rw [← he2, mem_quat1_iff_code hv2]
    exact q_facts.2.2.2.2.2.2.2.2.2.2

theorem violC_sound {p q c : Array ℕ} (hp : rawValid p = true) (hq : rawValid q = true)
    (hpq : IsQ8Pair (ev p) (ev q)) (hc : invertC c = true) (h : violC (q8Elts p q) c = true) :
    Viol (Subgroup.closure ({ev p, ev q} : Set (MulAut P43))) (ev c) := by
  set E := q8Elts p q with hE
  have hEv : ∀ y ∈ E, rawValid y = true := q8Elts_valid hp hq
  have hmemE : ∀ y ∈ E, ev y ∈ Subgroup.closure ({ev p, ev q} : Set (MulAut P43)) := by
    intro y hy
    rw [mem_closure_pair_iff hpq, ← map_ev_q8Elts hp hq]
    exact List.mem_map_of_mem hy
  have hmemQ : ∀ x : Array ℕ, rawValid x = true →
      (ev x ∈ Subgroup.closure ({ev p, ev q} : Set (MulAut P43)) ↔ memL x E = true) := by
    intro x hx
    rw [memL_iff hx hEv, mem_closure_pair_iff hpq, ← map_ev_q8Elts hp hq, List.mem_map]
    constructor
    · rintro ⟨y, hy, e⟩
      exact ⟨y, hy, e.symm⟩
    · rintro ⟨y, hy, e⟩
      exact ⟨y, hy, e.symm⟩
  unfold violC at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.mem_map,
    Bool.not_eq_true'] at h
  obtain ⟨⟨_, ⟨x, hx, rfl⟩, h1⟩, h2⟩ := h
  have hxv := hEv x hx
  obtain ⟨hcx, ecx⟩ := conjBy_spec hc hxv
  refine ⟨⟨ev x, hmemE x hx, fun hin => ?_⟩, ?_⟩
  · rw [← ecx, hmemQ _ hcx, h1] at hin
    exact Bool.false_ne_true hin
  · rcases h2 with ⟨y, hy, _, ⟨z, hz, rfl⟩, h3⟩ | ⟨_, ⟨z, hz, rfl⟩, h3, h4⟩
    · have hyv := hEv y hy
      obtain ⟨hcz, ecz⟩ := conjBy_spec hc (hEv z hz)
      refine Or.inl ⟨ev y, hmemE y hy, ev z, hmemE z hz, fun hc' => ?_⟩
      rw [← ecz] at hc'
      rw [(commC_iff hyv hcz).2 hc'] at h3
      exact Bool.false_ne_true h3.symm
    · obtain ⟨hcz, ecz⟩ := conjBy_spec hc (hEv z hz)
      refine Or.inr ⟨ev z, hmemE z hz, ?_, fun hc' => ?_⟩
      · rw [← ecz, hmemQ _ hcz]
        exact h3
      · rw [← ecz, ← ev_mulRaw hcz hcz, ev_eq_one_iff (rawValid_mulRaw hcz hcz)] at hc'
        rw [hc'] at h4
        exact Bool.false_ne_true h4.symm

theorem q8_dichotomy {p q : MulAut P43} (h : IsQ8Pair p q) (hp : p ^ 2 = tz) :
    (∃ c ∈ centT, Viol (Subgroup.closure ({p, q} : Set (MulAut P43))) c) ∨
      ∃ d : MulAut P43, d * tz = tz * d ∧
        (Subgroup.closure ({p, q} : Set (MulAut P43))).map (MulAut.conj d).toMonoidHom = quat1 := by
  obtain ⟨hSmem, -, hSvalid⟩ := sylS_spec
  obtain ⟨hq2, hqp⟩ := rel_of_isQ8Pair h hp
  set Q := Subgroup.closure ({p, q} : Set (MulAut P43)) with hQ
  have hQC : Q ≤ Subgroup.centralizer ({tz} : Set (MulAut P43)) := by
    rw [hQ, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl
    · exact comm_of_sq hp
    · exact comm_of_sq hq2
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [card_closure_pair h]; norm_num)
  have hidx : ¬ 2 ∣ sylS.relIndex (Subgroup.centralizer ({tz} : Set (MulAut P43))) :=
    fun h2 => sylS_index_odd (h2.trans (Subgroup.relIndex_dvd_index_of_le sylS_le_centralizer))
  obtain ⟨d, hdC, hd⟩ := exists_conj_le sylS_le_centralizer sylS_isPGroup hidx hQC hQ2
  have hdt : d * tz = tz * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
  obtain ⟨i, hi, hevi⟩ := (hSmem _).1 (hd p (Subgroup.subset_closure (by simp)))
  obtain ⟨j, hj, hevj⟩ := (hSmem _).1 (hd q (Subgroup.subset_closure (by simp)))
  set pts := (bfs u43Data).pts with hpts
  have hvi := rawValid_of_valid (hSvalid i hi)
  have hvj := rawValid_of_valid (hSvalid j hj)
  have hconjt : d * tz * d⁻¹ = tz := by rw [hdt]; group
  have hp' : (d * p * d⁻¹) ^ 2 = tz := by
    rw [pow_two, show d * p * d⁻¹ * (d * p * d⁻¹) = d * (p ^ 2) * d⁻¹ by rw [pow_two]; group,
      hp, hconjt]
  have hq' : (d * q * d⁻¹) ^ 2 = tz := by
    rw [pow_two, show d * q * d⁻¹ * (d * q * d⁻¹) = d * (q ^ 2) * d⁻¹ by rw [pow_two]; group,
      hq2, hconjt]
  have hr' : (d * q * d⁻¹) * (d * p * d⁻¹) = tz * (d * p * d⁻¹) * (d * q * d⁻¹) := by
    calc (d * q * d⁻¹) * (d * p * d⁻¹) = d * (q * p) * d⁻¹ := by group
      _ = (d * tz * d⁻¹) * (d * p * d⁻¹) * (d * q * d⁻¹) := by rw [hqp]; group
      _ = tz * (d * p * d⁻¹) * (d * q * d⁻¹) := by rw [hconjt]
  have hsi : eqZ (mulRaw pts[i]! pts[i]!) T0 = true := by
    refine (eqZ_iff_ev (rawValid_mulRaw hvi hvi) rawValid_T0).2 ?_
    rw [ev_mulRaw hvi hvi, hevi, ← pow_two, hp']
    rfl
  have hsj : eqZ (mulRaw pts[j]! pts[j]!) T0 = true := by
    refine (eqZ_iff_ev (rawValid_mulRaw hvj hvj) rawValid_T0).2 ?_
    rw [ev_mulRaw hvj hvj, hevj, ← pow_two, hq']
    rfl
  have hr : eqZ (mulRaw pts[j]! pts[i]!) (mulRaw (mulRaw T0 pts[i]!) pts[j]!) = true := by
    refine (eqZ_iff_ev (rawValid_mulRaw hvj hvi)
      (rawValid_mulRaw (rawValid_mulRaw rawValid_T0 hvi) hvj)).2 ?_
    rw [ev_mulRaw hvj hvi, ev_mulRaw (rawValid_mulRaw rawValid_T0 hvi) hvj,
      ev_mulRaw rawValid_T0 hvi, hevi, hevj, hr']
    rfl
  have hpair : IsQ8Pair (d * p * d⁻¹) (d * q * d⁻¹) := isQ8Pair_conj h d
  have hmapQ : Q.map (MulAut.conj d).toMonoidHom =
      Subgroup.closure ({d * p * d⁻¹, d * q * d⁻¹} : Set (MulAut P43)) :=
    map_conj_closure_pair p q d
  rcases q8_at (pts := pts) (E1 := q8Elts P1 Q1) (E2 := q8Elts P2 Q2) (L := q8Cands.toList)
    (t := T0) (allOK_parts allOK_true).2.2.2.2.2.2.2.1 hi hj hsi hsj hr with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨c, hc, hv⟩
  · refine Or.inr ⟨d, hdt, map_conj_eq_of_mem h card_quat1 ?_ ?_⟩
    · rw [← hevi, mem_quat1_iff_code hvi]
      exact h1
    · rw [← hevj, mem_quat1_iff_code hvj]
      exact h2
  · have h3 : Q.map (MulAut.conj d).toMonoidHom = quat2 := by
      refine map_conj_eq_of_mem h card_quat2 ?_ ?_
      · rw [← hevi, mem_quat2_iff_code hvi]
        exact h1
      · rw [← hevj, mem_quat2_iff_code hvj]
        exact h2
    obtain ⟨hg0, hg0Q⟩ := g0_facts
    have hg0t : ev G0 * tz = tz * ev G0 := ((mem_centT_iff _).1 hg0).2
    refine Or.inr ⟨ev G0 * d, ?_, ?_⟩
    · rw [mul_assoc, hdt, ← mul_assoc, hg0t, mul_assoc]
    · have hcomp : (MulAut.conj (ev G0 * d)).toMonoidHom =
          (MulAut.conj (ev G0)).toMonoidHom.comp (MulAut.conj d).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp, ← Subgroup.map_map, h3, hg0Q]
  · obtain ⟨hci, hcin, hct⟩ := cands_parts (allOK_parts allOK_true).2.2.2.2.2.1 c hc
    have hcv := (invertC_spec hci).1
    have hV : Viol (Q.map (MulAut.conj d).toMonoidHom) (ev c) := by
      rw [hmapQ, ← hevi, ← hevj]
      exact violC_sound hvi hvj (by rw [hevi, hevj]; exact hpair) hci hv
    refine Or.inl ⟨d⁻¹ * ev c * d, (mem_centT_iff _).2 ⟨?_, ?_⟩, hV.of_map⟩
    · have := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal P43).conj_mem _
        (innerShape_mem_inner hcv hcin) d⁻¹
      simpa using this
    · have hct' : ev c * tz = tz * ev c := (commC_iff hcv rawValid_T0).1 hct
      have hdt' : d⁻¹ * tz = tz * d⁻¹ := (Commute.inv_left (show Commute d tz from hdt)).eq
      calc d⁻¹ * ev c * d * tz = d⁻¹ * ev c * (d * tz) := by group
        _ = d⁻¹ * ev c * (tz * d) := by rw [hdt]
        _ = d⁻¹ * (ev c * tz) * d := by group
        _ = d⁻¹ * (tz * ev c) * d := by rw [hct']
        _ = (d⁻¹ * tz) * ev c * d := by group
        _ = (tz * d⁻¹) * ev c * d := by rw [hdt']
        _ = tz * (d⁻¹ * ev c * d) := by group

theorem perm_quat1 {c : MulAut P43} (hc : c ∈ centT) :
    quat1.map (MulAut.conj c).toMonoidHom = quat1 ∨
      quat1.map (MulAut.conj c).toMonoidHom = quat2 := by
  obtain ⟨i, hi, rfl⟩ := (centT_spec.1 c).1 hc
  obtain ⟨hinv, h⟩ := perm_at (pts := (cCert ()).pts) (E1 := q8Elts P1 Q1) (E2 := q8Elts P2 Q2)
    (a := P1) (b := Q1) (allOK_parts allOK_true).2.2.2.2.2.2.2.2.1 hi
  obtain ⟨h1v, h1e⟩ := conjBy_spec hinv q_facts.1.1
  obtain ⟨h2v, h2e⟩ := conjBy_spec hinv q_facts.2.1.1
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine Or.inl (map_conj_eq_of_mem isQ8Pair_quat1 card_quat1 ?_ ?_)
    · rw [← h1e, mem_quat1_iff_code h1v]
      exact ha
    · rw [← h2e, mem_quat1_iff_code h2v]
      exact hb
  · refine Or.inr (map_conj_eq_of_mem isQ8Pair_quat1 card_quat2 ?_ ?_)
    · rw [← h1e, mem_quat2_iff_code h1v]
      exact ha
    · rw [← h2e, mem_quat2_iff_code h2v]
      exact hb

theorem eq_bot_of_odd {N : Subgroup (MulAut P43)} (hN : N ≤ centT)
    (hnorm : ∀ c ∈ centT, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨i, hi, hev⟩ := (centT_spec.1 x).1 (hN hx)
  have hxv := rawValid_of_valid (centT_spec.2.2 i hi)
  have hoN : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  have hoC : orderOf x ∣ 1152 := by
    rw [← centT_spec.2.1]
    exact Subgroup.orderOf_dvd_natCard centT (hN hx)
  have hoddx : Odd (orderOf x) := Odd.of_dvd_nat hodd hoN
  have ho9 : orderOf x ∣ 9 := by
    have hcop : Nat.Coprime (orderOf x) 128 :=
      Nat.Coprime.pow_right 7 (Nat.coprime_two_right.mpr hoddx)
    exact hcop.dvd_of_dvd_mul_left (by simpa using hoC)
  have hx9 : x ^ 9 = 1 := orderOf_dvd_iff_pow_eq_one.mp ho9
  have h9 : isZ (powRaw (cCert ()).pts[i]! 9) = true := by
    refine (ev_eq_one_iff (powRaw_spec hxv 9).1).1 ?_
    rw [ev_powRaw hxv, hev, hx9]
  have h1 : isZ (cCert ()).pts[i]! = false := by
    by_contra hcon
    exact hx1 (by rw [← hev]; exact (ev_eq_one_iff hxv).2 (by simpa using hcon))
  obtain ⟨g, hg, hw⟩ := odd_at (pts := (cCert ()).pts) (G := q8Elts P1 Q1 ++ q8Elts P2 Q2)
    (allOK_parts allOK_true).2.2.2.2.2.2.2.2.2.1 hi h1 h9
  have hgv : rawValid g = true := by
    rcases List.mem_append.mp hg with hg' | hg'
    · exact q8Elts_valid q_facts.1.1 q_facts.2.1.1 g hg'
    · exact q8Elts_valid q_facts.2.2.1.1 q_facts.2.2.2.1.1 g hg'
  have hgQ : ev g ∈ centT ∧ ev g ^ 4 = 1 := by
    rcases List.mem_append.mp hg with hg' | hg'
    · have hm : ev g ∈ quat1 := (mem_quat1_iff_code hgv).2
        ((memL_iff hgv (q8Elts_valid q_facts.1.1 q_facts.2.1.1)).2 ⟨g, hg', rfl⟩)
      exact ⟨quat1_le_centT hm, pow_four_of_mem_closure_pair isQ8Pair_quat1 hm⟩
    · have hm : ev g ∈ quat2 := (mem_quat2_iff_code hgv).2
        ((memL_iff hgv (q8Elts_valid q_facts.2.2.1.1 q_facts.2.2.2.1.1)).2 ⟨g, hg', rfl⟩)
      exact ⟨quat2_le_centT hm, pow_four_of_mem_closure_pair isQ8Pair_quat2 hm⟩
  set w := mulRaw (mulRaw (mulRaw (cCert ()).pts[i]! g) (powRaw (cCert ()).pts[i]! 8))
    (powRaw g 3) with hw'
  have h8 := powRaw_spec hxv 8
  have h3 := powRaw_spec hgv 3
  have hwv : rawValid w = true :=
    rawValid_mulRaw (rawValid_mulRaw (rawValid_mulRaw hxv hgv) h8.1) h3.1
  have hx8 : x ^ 8 = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx9]
  have hg3 : ev g ^ 3 = (ev g)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hgQ.2]
  have hevw : ev w = x * (ev g * x⁻¹ * (ev g)⁻¹) := by
    rw [hw', ev_mulRaw (rawValid_mulRaw (rawValid_mulRaw hxv hgv) h8.1) h3.1,
      ev_mulRaw (rawValid_mulRaw hxv hgv) h8.1, ev_mulRaw hxv hgv, h8.2, h3.2, hev, hx8, hg3]
    group
  have hwN : ev w ∈ N := by
    rw [hevw]
    exact N.mul_mem hx (hnorm _ hgQ.1 _ (N.inv_mem hx))
  have heven := evenC_spec hwv hw
  have hdvd : orderOf (ev w) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hwN
  obtain ⟨k, hk⟩ := heven
  have : 2 ∣ Nat.card N := (Dvd.intro_left k (by omega)).trans hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)

@[expose] def quadOf (M : SL(2, ZMod 3)) : ℕ × ℕ × ℕ × ℕ :=
  (((M : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0).val,
    ((M : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1).val,
    ((M : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0).val,
    ((M : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1).val)

theorem quadOf_mem : ∀ M : SL(2, ZMod 3), quadOf M ∈ slQuads := by decide +kernel

theorem exists_quadOf : ∀ m ∈ slQuads, ∃ M : SL(2, ZMod 3), quadOf M = m := by decide +kernel

theorem quadOf_eq_one : ∀ M : SL(2, ZMod 3), quadOf M = (1, 0, 0, 1) → M = 1 := by decide +kernel

theorem quadOf_mul (M N : SL(2, ZMod 3)) : quadOf (M * N) = qmul (quadOf M) (quadOf N) := by
  simp only [quadOf, qmul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    ZMod.val_add, ZMod.val_mul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> exact (Nat.add_mod _ _ _).symm

theorem psi_facts :
    (∀ m ∈ slQuads, rawValid psiTab[qidx m]! = true ∧ innerShape psiTab[qidx m]! = true ∧
      commC psiTab[qidx m]! P2 = true ∧ commC psiTab[qidx m]! Q2 = true ∧
      (m = (1, 0, 0, 1) ∨ isZ psiTab[qidx m]! = false)) ∧
    ∀ m ∈ slQuads, ∀ n ∈ slQuads,
      eqZ psiTab[qidx (qmul m n)]! (mulRaw psiTab[qidx m]! psiTab[qidx n]!) = true :=
  psi_parts (allOK_parts allOK_true).2.2.2.2.2.2.2.2.2.2.1

@[expose] noncomputable def psiFun (M : SL(2, ZMod 3)) : MulAut P43 := ev psiTab[qidx (quadOf M)]!

theorem psiFun_mul (M N : SL(2, ZMod 3)) : psiFun (M * N) = psiFun M * psiFun N := by
  have hM := quadOf_mem M
  have hN := quadOf_mem N
  have hMN := quadOf_mem (M * N)
  unfold psiFun
  rw [← ev_mulRaw (psi_facts.1 _ hM).1 (psi_facts.1 _ hN).1]
  refine (eqZ_iff_ev (psi_facts.1 _ hMN).1
    (rawValid_mulRaw (psi_facts.1 _ hM).1 (psi_facts.1 _ hN).1)).1 ?_
  rw [quadOf_mul]
  exact psi_facts.2 _ hM _ hN

@[expose] noncomputable def psiHom : SL(2, ZMod 3) →* MulAut P43 where
  toFun := psiFun
  map_one' := by
    have h := psiFun_mul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  map_mul' := psiFun_mul

theorem psiHom_injective : Function.Injective psiHom := by
  rw [injective_iff_map_eq_one]
  intro M hM
  have hm := quadOf_mem M
  have h1 : isZ psiTab[qidx (quadOf M)]! = true := (ev_eq_one_iff (psi_facts.1 _ hm).1).1 hM
  rcases (psi_facts.1 _ hm).2.2.2.2 with h2 | h2
  · exact quadOf_eq_one M h2
  · rw [h1] at h2
    exact absurd h2 (by decide)

theorem forall_comm_closure {x a b : MulAut P43} (ha : x * a = a * x) (hb : x * b = b * x) :
    ∀ y ∈ Subgroup.closure ({a, b} : Set (MulAut P43)), x * y = y * x := by
  have hle : Subgroup.closure ({a, b} : Set (MulAut P43)) ≤
      Subgroup.centralizer ({x} : Set (MulAut P43)) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl
    · exact ha.symm
    · exact hb.symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem mem_range_psiHom_iff (x : MulAut P43) :
    (x ∈ inner P43 ∧ ∀ y ∈ quat2, x * y = y * x) ↔ x ∈ psiHom.range := by
  constructor
  · rintro ⟨hx, hc⟩
    have hxt : x * tz = tz * x := hc tz tz_mem_quat2
    obtain ⟨i, hi, rfl⟩ := (centT_spec.1 x).1 ((mem_centT_iff x).2 ⟨hx, hxt⟩)
    have hxv := rawValid_of_valid (centT_spec.2.2 i hi)
    have hcP := (commC_iff hxv q_facts.2.2.1.1).2 (hc _ (Subgroup.subset_closure (by simp)))
    have hcQ := (commC_iff hxv q_facts.2.2.2.1.1).2 (hc _ (Subgroup.subset_closure (by simp)))
    have hmem := (cent_at (pts := (cCert ()).pts) (psiL := slQuads.map fun m => psiTab[qidx m]!)
      (H := H2tab.toList) (a2 := P2) (b2 := Q2) (a1 := P1) (b1 := Q1)
      (allOK_parts allOK_true).2.2.2.2.2.2.2.2.2.2.2.1 hi).1 hcP hcQ
    have hLv : ∀ y ∈ slQuads.map (fun m => psiTab[qidx m]!), rawValid y = true := by
      intro y hy
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hy
      exact (psi_facts.1 m hm).1
    obtain ⟨y, hy, hxy⟩ := (memL_iff hxv hLv).1 hmem
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hy
    obtain ⟨M, rfl⟩ := exists_quadOf m hm
    exact ⟨M, hxy.symm⟩
  · rintro ⟨M, rfl⟩
    have hm := quadOf_mem M
    obtain ⟨hv, hin, hcP, hcQ, -⟩ := psi_facts.1 _ hm
    refine ⟨innerShape_mem_inner hv hin, forall_comm_closure ?_ ?_⟩
    · exact (commC_iff hv q_facts.2.2.1.1).1 hcP
    · exact (commC_iff hv q_facts.2.2.2.1.1).1 hcQ

theorem commute_of_cent {x y : MulAut P43} (hx : x ∈ inner P43 ∧ ∀ w ∈ quat1, x * w = w * x)
    (hy : y ∈ inner P43 ∧ ∀ w ∈ quat2, y * w = w * y) : x * y = y * x := by
  obtain ⟨M, rfl⟩ := (mem_range_psiHom_iff y).1 hy
  have hxt : x * tz = tz * x := hx.2 tz tz_mem_quat1
  obtain ⟨i, hi, rfl⟩ := (centT_spec.1 x).1 ((mem_centT_iff _).2 ⟨hx.1, hxt⟩)
  have hxv := rawValid_of_valid (centT_spec.2.2 i hi)
  have hcP := (commC_iff hxv q_facts.1.1).2 (hx.2 _ (Subgroup.subset_closure (by simp)))
  have hcQ := (commC_iff hxv q_facts.2.1.1).2 (hx.2 _ (Subgroup.subset_closure (by simp)))
  have hmem := (cent_at (pts := (cCert ()).pts) (psiL := slQuads.map fun m => psiTab[qidx m]!)
    (H := H2tab.toList) (a2 := P2) (b2 := Q2) (a1 := P1) (b1 := Q1)
    (allOK_parts allOK_true).2.2.2.2.2.2.2.2.2.2.2.1 hi).2 hcP hcQ
  have hcomm := comm_parts (allOK_parts allOK_true).2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨h, hh, hxh⟩ := (memL_iff hxv (fun y hy => (hcomm y hy).1)).1 hmem
  have hm := quadOf_mem M
  have hc := (commC_iff (psi_facts.1 _ hm).1 (hcomm h hh).1).1 ((hcomm h hh).2 _ hm)
  show ev (cCert ()).pts[i]! * psiFun M = psiFun M * ev (cCert ()).pts[i]!
  rw [hxh]
  exact hc.symm

end Model

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.U43
