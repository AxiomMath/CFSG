module

public import Certificates.Data.Kernel.U43.Pair
public import CFSG.Certificates.Kernel.U43.ClassSound

public section

namespace CFSG.KC.U43

open CFSG.KC.Loop CFSG.KD.U43 CFSG.RankThree.PartTwo.Sec4.Item434RemU43 CFSG.KC.G2Three

theorem pw_dat {c c2 : List ℕ} {C C2 : ℕ} (hc : DatF c C) (hc2 : DatF c2 C2) {k : ℕ}
    (hk : k < 3) : DatF ([one4, c, c2].getD k []) (pw C C2 k) := by
  interval_cases k
  · exact oneDF
  · exact hc
  · exact hc2

theorem e9_getD (a b : List ℕ) {e : ℕ} (he : e < 9) : (e9Elems a b).getD e [] =
    mul4 ([one4, a, sq4 a].getD (e / 3) []) ([one4, b, sq4 b].getD (e % 3) []) := by
  interval_cases e <;> rfl

theorem e9_dat {a b : List ℕ} {A A2 B B2 : ℕ} (ha : DatF a A) (ha2 : DatF (sq4 a) A2)
    (hb : DatF b B) (hb2 : DatF (sq4 b) B2) {e : ℕ} (he : e < 9) :
    DatF ((e9Elems a b).getD e []) (e9F A A2 B B2 e) := by
  rw [e9_getD a b he]
  exact mulDF (pw_dat ha ha2 (by omega)) (pw_dat hb hb2 (by omega))

theorem memF_eq (r : ℕ) : ∀ l : List ℕ, memF r l = l.contains r
  | [] => rfl
  | a :: t => by
    have e : memF r (a :: t) = bIf(Nat.beq a r, true, memF r t) := rfl
    rw [e, memF_eq r t, List.contains_cons]
    by_cases h : a = r
    · subst h
      rw [Nat.beq_refl]
      simp
    · have hb : Nat.beq a r = false := by
        cases hq : Nat.beq a r
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) h
      rw [hb]
      change t.contains r = (r == a || t.contains r)
      simp [Ne.symm h]

theorem inRt_eq {r : ℕ} (hr : r < 729) : inRt r = memF r uRt := by
  rw [memF_eq]
  unfold inRt uRtArr
  simp [Array.getD, hr]

theorem convPair_eq {q : ℕ} (hq : q < 729) :
    convPairArr.getD q (wordPair []) = wordPair (convRWord q) := by
  unfold convPairArr
  simp [Array.getD, hq]

@[expose] def TabF (X : ℕ → ℕ) : Prop :=
  (∀ t < 729, DatF (uAt t) (X t)) ∧ ∀ t < 729, posOf (uAt t) = t

theorem pos_of {X : ℕ → ℕ} (hT : TabF X) {c : List ℕ} {C q : ℕ} (hc : DatF c C) (hq : q < 729)
    (h : X q = C) : c = uAt q ∧ posOf c = q := by
  have e : c = uAt q := fmtF_inj hc.1 (hT.1 q hq).1 (by rw [hc.2, (hT.1 q hq).2, h])
  exact ⟨e, by rw [e, hT.2 q hq]⟩

theorem conv_dat {A CA CB : ℕ → ℕ} (hA : lettersF A = true) (hconv : convF A CA CB = true)
    {q : ℕ} (hq : q < 729) {x : List ℕ} {Y : ℕ} (hx : DatF x Y) :
    DatF (conjStep (convPairArr.getD q (wordPair [])) x) (MF (MF (CA q) Y) (CB q)) := by
  have h := allBelow_g2 hconv (by decide) q hq
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  rw [convPair_eq hq, h.1, h.2]
  exact conjDF hA _ hx

theorem inRtF_sound {X : ℕ → ℕ} (hT : TabF X) {g c : List ℕ} {ca cb y r : ℕ}
    (hg : ∀ (x : List ℕ) (Y : ℕ), DatF x Y → DatF (conjStep g x) (MF (MF ca Y) cb))
    (hy : DatF c y) (h : inRtF X ca cb y r = true) :
    (!(c == one4) && inRt (posOf (conjStep g c))) = true := by
  unfold inRtF at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [beqDF hy oneDF, h1, Bool.true_and, (pos_of hT (hg c y hy) h2 h4).2, inRt_eq h2, h3]

theorem commF_eq {x y : List ℕ} {X Y : ℕ} (hx : DatF x X) (hy : DatF y Y) :
    commutes4 x y = commF X Y :=
  beqDF (mulDF hx hy) (mulDF hy hx)

theorem yComm_eq {m p : ℕ} (hm : m < 39) (hp : p < 729) :
    (yCommArr.getD m #[]).getD p false =
      commutes4 (uAt ((yTriple (m / 3)).getD (m % 3) 0)) (uAt p) := by
  unfold yCommArr
  simp [Array.getD, hm, hp]

theorem cvF_sound {X SQ A CA CB : ℕ → ℕ} (hT : TabF X) (hA : lettersF A = true)
    (hconv : convF A CA CB = true) (hsq : ∀ t < 729, SQ t = MF (X t) (X t)) {ia ib w : ℕ}
    (hia : ia < 729) (hib : ib < 729) (h : cvF X SQ CA CB ia ib w = true) :
    (dependent9 (uAt ia) (uAt ib) || cover1 (e9Elems (uAt ia) (uAt ib)) ||
      cover2 (e9Elems (uAt ia) (uAt ib))) = true := by
  have ha := hT.1 ia hia
  have hb := hT.1 ib hib
  have ha2 : DatF (sq4 (uAt ia)) (SQ ia) := by rw [hsq ia hia]; exact mulDF ha ha
  have hb2 : DatF (sq4 (uAt ib)) (SQ ib) := by rw [hsq ib hib]; exact mulDF hb hb
  simp only [cvF, letB_eq] at h
  cases h1 : Nat.beq (wf w 0) 1
  · rw [h1] at h
    cases h2 : Nat.beq (wf w 0) 2
    · rw [h2] at h
      cases h3 : Nat.beq (wf w 0) 3
      · rw [h3] at h
        exact absurd h (by simp)
      · rw [h3] at h
        change (Nat.blt (wf w 1) 13 && allBelow 3 1 _) = true at h
        rw [Bool.and_eq_true, Nat.blt_eq] at h
        have hall := allBelow_g2 h.2 (by decide)
        have c2 : cover2 (e9Elems (uAt ia) (uAt ib)) = true := by
          unfold cover2
          rw [List.any_eq_true]
          refine ⟨wf w 1, List.mem_range.2 h.1, ?_⟩
          rw [List.all_eq_true]
          intro i hi
          have hi3 := List.mem_range.1 hi
          have hc := hall i hi3
          simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq,
            Nat.succ_eq_add_one] at hc
          obtain ⟨⟨⟨⟨⟨ht, hq⟩, hy⟩, hx⟩, hne⟩, hcm⟩ := hc
          rw [List.any_eq_true]
          refine ⟨wf w (2 + i), List.mem_range.2 ht, ?_⟩
          have he := e9_dat ha ha2 hb hb2 (e := wf w (2 + i) + 1) (by omega)
          obtain ⟨ec, ep⟩ := pos_of hT he hq hx
          rw [beqDF he oneDF, hne, Bool.true_and, ep,
            yComm_eq (by omega) hq, ← ec]
          have e3 : (3 * wf w 1 + i) / 3 = wf w 1 := by omega
          have e3' : (3 * wf w 1 + i) % 3 = i := by omega
          rw [e3, e3', commF_eq (hT.1 _ hy) he, ← hx]
          exact hcm
        rw [c2, Bool.or_true]
    · rw [h2] at h
      change (Nat.blt (wf w 1) 8 && Nat.blt (wf w 2) 729 &&
        Nat.beq (X (wf w 2)) (e9F (X ia) (SQ ia) (X ib) (SQ ib) (wf w 1 + 1)) &&
        inRtF X (CA (wf w 2)) (CB (wf w 2)) (e9F (X ia) (SQ ia) (X ib) (SQ ib) (wf w 1 + 1))
          (wf w 3)) = true at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
      obtain ⟨⟨⟨ht, hq⟩, hx⟩, hr⟩ := h
      have he := e9_dat ha ha2 hb hb2 (e := wf w 1 + 1) (by omega)
      have c1 : cover1 (e9Elems (uAt ia) (uAt ib)) = true := by
        unfold cover1
        rw [List.any_eq_true]
        refine ⟨wf w 1, List.mem_range.2 ht, ?_⟩
        rw [(pos_of hT he hq hx).2]
        exact inRtF_sound hT (fun x Y hx' => conv_dat hA hconv hq hx') he hr
      rw [c1, Bool.or_true, Bool.true_or]
  · rw [h1] at h
    change Nat.beq (X ib) (SQ ia) = true at h
    have d : dependent9 (uAt ia) (uAt ib) = true := by
      unfold dependent9
      rw [beqDF hb ha2, h, Bool.or_true]
    rw [d, Bool.true_or, Bool.true_or]

theorem za_eq (a : List ℕ) : zaList a = [mul4 one4 one4, mul4 one4 a, mul4 one4 (sq4 a),
    mul4 zc one4, mul4 zc a, mul4 zc (sq4 a), mul4 zc2 one4, mul4 zc2 a, mul4 zc2 (sq4 a)] := by
  simp [zaList]

theorem za_getD (a : List ℕ) {m : ℕ} (hm : m < 9) : (zaList a).getD m [] =
    mul4 ([one4, zc, zc2].getD (m / 3) []) ([one4, a, sq4 a].getD (m % 3) []) := by
  rw [za_eq]
  interval_cases m <;> simp

theorem els_getD (a b : List ℕ) {e : ℕ} (he : e < 27) : (pElemsOf (zaList a) b).getD e [] =
    [(zaList a).getD (e / 3) [], mul4 ((zaList a).getD (e / 3) []) b,
      mul4 ((zaList a).getD (e / 3) []) (sq4 b)].getD (e % 3) [] := by
  unfold pElemsOf
  rw [za_eq]
  interval_cases e <;> simp

theorem els_size (a b : List ℕ) : (pElemsOf (zaList a) b).size = 27 := rfl

theorem za_dat {a : List ℕ} {Z Z2 A A2 : ℕ} (hz : DatF zc Z) (hz2 : DatF zc2 Z2) (ha : DatF a A)
    (ha2 : DatF (sq4 a) A2) {m : ℕ} (hm : m < 9) :
    DatF ((zaList a).getD m []) (MF (pw Z Z2 (m / 3)) (pw A A2 (m % 3))) := by
  rw [za_getD a hm]
  exact mulDF (pw_dat hz hz2 (by omega)) (pw_dat ha ha2 (by omega))

theorem els_dat {a b : List ℕ} {Z Z2 A A2 B B2 : ℕ} (hz : DatF zc Z) (hz2 : DatF zc2 Z2)
    (ha : DatF a A) (ha2 : DatF (sq4 a) A2) (hb : DatF b B) (hb2 : DatF (sq4 b) B2) {e : ℕ}
    (he : e < 27) : DatF ((pElemsOf (zaList a) b).getD e []) (elsF Z Z2 A A2 B B2 e) := by
  have hu := za_dat hz hz2 ha ha2 (m := e / 3) (by omega)
  rw [els_getD a b he]
  simp only [elsF, letN_eq]
  obtain h | h | h : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
  · have h' : Nat.mod e 3 = 0 := h
    rw [h, h']
    exact hu
  · have h' : Nat.mod e 3 = 1 := h
    rw [h, h']
    exact mulDF hu hb
  · have h' : Nat.mod e 3 = 2 := h
    rw [h, h']
    exact mulDF hu hb2

theorem listF_at (K : ℕ → ℕ) : ∀ (l : List ℕ) (p : ℕ), listF K l p = true →
    ∀ i < l.length, K (p + i) = l.getD i 0
  | [], _, _, i, hi => absurd hi (by simp)
  | k :: l, p, h, i, hi => by
    have h' : Bool.rec (motive := fun _ => Bool) false (listF K l (p + 1)) (Nat.beq (K p) k) =
        true := h
    obtain ⟨h1, h2⟩ := bAnd_g2 h'
    cases i with
    | zero => simpa using Nat.eq_of_beq_eq_true h1
    | succ i =>
      have := listF_at K l (p + 1) h2 i (by simpa using hi)
      have ep : p + (i + 1) = p + 1 + i := by omega
      rw [ep, this]
      simp

theorem contains_of_getD {l : List (List ℕ)} {m : ℕ} (hm : m < l.length) :
    l.contains (l.getD m []) = true := by
  rw [List.contains_iff_mem, List.getD_eq_getElem _ _ hm]
  exact List.getElem_mem hm

theorem acontains_of_getD {l : Array (List ℕ)} {m : ℕ} (hm : m < l.size) :
    l.contains (l.getD m []) = true := by
  rw [Array.contains_iff_mem, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hm,
    Option.getD_some]
  exact Array.getElem_mem hm

theorem ppF_sound {X SQ KND A CA CB : ℕ → ℕ} (hT : TabF X) (hA : lettersF A = true)
    (hconv : convF A CA CB = true) (hsq : ∀ t < 729, SQ t = MF (X t) (X t))
    (hknd : ∀ q < 729, KND q = uKind.getD q 0) {ia ib w : ℕ}
    (hia : ia < 729) (hib : ib < 729) (h : ppF X SQ KND CA CB (X uZ) (SQ uZ) ia ib w = true) :
    pairOKE (uAt ia) (uAt ib) = true := by
  have ha := hT.1 ia hia
  have hb := hT.1 ib hib
  have ha2 : DatF (sq4 (uAt ia)) (SQ ia) := by rw [hsq ia hia]; exact mulDF ha ha
  have hb2 : DatF (sq4 (uAt ib)) (SQ ib) := by rw [hsq ib hib]; exact mulDF hb hb
  have hz : DatF zc (X uZ) := hT.1 uZ (by decide)
  have hz2 : DatF zc2 (SQ uZ) := by rw [hsq uZ (by decide)]; exact mulDF hz hz
  have hE := fun {e : ℕ} (he : e < 27) => els_dat hz hz2 ha ha2 hb hb2 he
  simp only [pairOKE]
  simp only [ppF, letB_eq] at h
  cases h1 : Nat.beq (wf w 0) 1
  · rw [h1] at h
    cases h2 : Nat.beq (wf w 0) 2
    · rw [h2] at h
      have hgb : (pairGood (pElemsOf (zaList (uAt ia)) (uAt ib)) ||
          pairBad (pElemsOf (zaList (uAt ia)) (uAt ib))) = true := by
        cases h3 : Nat.beq (wf w 0) 3
        · rw [h3] at h
          cases h4 : Nat.beq (wf w 0) 4
          · rw [h4] at h
            exact absurd h (by simp)
          · rw [h4] at h
            change badF X (elsF (X uZ) (SQ uZ) (X ia) (SQ ia) (X ib) (SQ ib)) w = true at h
            simp only [badF, letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
            obtain ⟨⟨⟨hk, hea⟩, heb⟩, ⟨⟨⟨hpa, hpb⟩, hxa⟩, hxb⟩⟩ := h
            have c : pairBad (pElemsOf (zaList (uAt ia)) (uAt ib)) = true := by
              unfold pairBad
              rw [List.any_eq_true]
              refine ⟨wf w 1, List.mem_range.2 hk, ?_⟩
              have ea := (pos_of hT (hE hea) hpa hxa.symm).1
              have eb := (pos_of hT (hE heb) hpb hxb.symm).1
              unfold badA badB
              rw [← ea, ← eb, acontains_of_getD (by rw [els_size]; exact hea),
                acontains_of_getD (by rw [els_size]; exact heb)]
              rfl
            rw [c, Bool.or_true]
        · rw [h3] at h
          change goodF X KND CA CB (elsF (X uZ) (SQ uZ) (X ia) (SQ ia) (X ib) (SQ ib)) w = true at h
          simp only [goodF, letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at h
          obtain ⟨⟨⟨hx0, hx27⟩, hpre⟩, ⟨hu, hv⟩, ⟨⟨hru, hrv⟩, hvu⟩, hvuu⟩ := h
          have hpre' := allBelow_g2 hpre (by omega)
          have hq : ∀ i < wf w 1, wf w (6 + i) < 729 ∧
              X (wf w (6 + i)) = elsF (X uZ) (SQ uZ) (X ia) (SQ ia) (X ib) (SQ ib) (i + 1) ∧
              (kindOf ((pElemsOf (zaList (uAt ia)) (uAt ib)).getD (i + 1) []) == 2) =
                (i + 1 == wf w 1) := by
            intro i hi
            have hc := hpre' i hi
            simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq,
              Nat.succ_eq_add_one] at hc
            obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hc
            obtain ⟨ec, ep⟩ := pos_of hT (hE (e := i + 1) (by omega)) hq1 hq2
            refine ⟨hq1, hq2, ?_⟩
            unfold kindOf kindAt uKindArr
            rw [ep, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
              ← hknd _ hq1]
            by_cases hix : i + 1 = wf w 1
            · rw [hix, Nat.beq_refl] at hq3
              rw [Nat.eq_of_beq_eq_true hq3, hix]
              simp
            · have hne : Nat.beq (i + 1) (wf w 1) = false := by
                cases e : Nat.beq (i + 1) (wf w 1)
                · rfl
                · exact absurd (Nat.eq_of_beq_eq_true e) hix
              rw [hne] at hq3
              have hk : KND (wf w (6 + i)) ≠ 2 := by
                simp only [Bool.not_eq_true'] at hq3
                exact Nat.ne_of_beq_eq_false hq3
              simp [hk, hix]
          have hfind : (List.range 27).find? (fun e => e != 0 &&
              kindOf ((pElemsOf (zaList (uAt ia)) (uAt ib)).getD e []) == 2) = some (wf w 1) := by
            rw [List.find?_range_eq_some]
            refine ⟨?_, List.mem_range.2 hx27, fun j hj => ?_⟩
            · obtain ⟨-, -, hk⟩ := hq (wf w 1 - 1) (by omega)
              have e1 : wf w 1 - 1 + 1 = wf w 1 := by omega
              rw [e1] at hk
              simp only [hk, beq_self_eq_true, Bool.and_true]
              simpa using (by omega : wf w 1 ≠ 0)
            · rcases Nat.eq_zero_or_pos j with hj0 | hj0
              · subst hj0
                simp
              · obtain ⟨-, -, hk⟩ := hq (j - 1) (by omega)
                have ej : j - 1 + 1 = j := by omega
                rw [ej] at hk
                rw [hk]
                simp
                omega
          have hgood : pairGood (pElemsOf (zaList (uAt ia)) (uAt ib)) = true := by
            unfold pairGood
            rw [hfind]
            obtain ⟨hqx, hxx, -⟩ := hq (wf w 1 - 1) (by omega)
            have e6 : 6 + (wf w 1 - 1) = 5 + wf w 1 := by omega
            have e1 : wf w 1 - 1 + 1 = wf w 1 := by omega
            rw [e6] at hqx
            rw [e6, e1] at hxx
            obtain ⟨-, epx⟩ := pos_of hT (hE hx27) hqx hxx
            simp only [pairGoodAt]
            rw [epx, List.any_eq_true]
            have hg : ∀ (x : List ℕ) (Y : ℕ), DatF x Y →
                DatF (conjStep (convPairArr.getD (wf w (5 + wf w 1)) (wordPair [])) x)
                  (MF (MF (CA (wf w (5 + wf w 1))) Y) (CB (wf w (5 + wf w 1)))) :=
              fun x Y hx => conv_dat hA hconv hqx hx
            have su := inRtF_sound hT hg (hE hu) hru
            have sv := inRtF_sound hT hg (hE hv) hrv
            have nvu : (!((pElemsOf (zaList (uAt ia)) (uAt ib)).getD (wf w 3) [] ==
                (pElemsOf (zaList (uAt ia)) (uAt ib)).getD (wf w 2) [])) = true := by
              rw [beqDF (hE hv) (hE hu)]
              exact hvu
            have nvuu : (!((pElemsOf (zaList (uAt ia)) (uAt ib)).getD (wf w 3) [] ==
                sq4 ((pElemsOf (zaList (uAt ia)) (uAt ib)).getD (wf w 2) []))) = true := by
              unfold sq4
              rw [beqDF (hE hv) (mulDF (hE hu) (hE hu))]
              exact hvuu
            refine ⟨wf w 2, List.mem_range.2 hu, ?_⟩
            simp only [Bool.and_eq_true] at su sv ⊢
            refine ⟨su, ?_⟩
            rw [List.any_eq_true]
            refine ⟨wf w 3, List.mem_range.2 hv, ?_⟩
            simp only [Bool.and_eq_true]
            exact ⟨⟨⟨sv.1, nvu⟩, nvuu⟩, sv.2⟩
          rw [hgood, Bool.true_or]
      rw [hgb, Bool.or_true]
    · rw [h2] at h
      change (Nat.blt (wf w 1) 9 && Nat.beq (X ib) (MF (pw (X uZ) (SQ uZ) (wf w 1 / 3))
        (pw (X ia) (SQ ia) (wf w 1 % 3)))) = true at h
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
      have hm := za_dat hz hz2 ha ha2 h.1
      have e : uAt ib = (zaList (uAt ia)).getD (wf w 1) [] :=
        fmtF_inj hb.1 hm.1 (by rw [hb.2, hm.2, h.2])
      have d : dependent (uAt ia) (zaList (uAt ia)) (uAt ib) = true := by
        unfold dependent
        rw [e, contains_of_getD (by have : (zaList (uAt ia)).length = 9 := rfl; omega),
          Bool.or_true]
      rw [d, Bool.true_or]
  · rw [h1] at h
    change (Nat.beq (X ia) (X uZ) || Nat.beq (X ia) (SQ uZ)) = true at h
    have d : dependent (uAt ia) (zaList (uAt ia)) (uAt ib) = true := by
      unfold dependent
      rw [beqDF ha hz, beqDF ha hz2, h, Bool.true_or]
    rw [d, Bool.true_or]

end CFSG.KC.U43

end
