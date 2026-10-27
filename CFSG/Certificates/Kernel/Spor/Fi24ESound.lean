module

public import Certificates.Data.Kernel.Spor.Fi24E
public import CFSG.Certificates.Kernel.Spor.Fi24ThreeOSound

public section

namespace CFSG.KS.Fi24E

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Oct CFSG.KC.Fi24E
  CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt CFSG.KS.Fi24Kit CFSG.KS.Fi24ThreeO Finset

variable {NW : Nat → Nat → Nat} {NT : Nat → Nat}

abbrev Sig (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat)) (p x : Nat) : Prop :=
  x < 306936 ∧ ∀ w ∈ ws, (cP NW NT (dW w) x = x ↔ cP NW NT (dW w) p = p)

abbrev FX (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (y : Nat) : Prop :=
  y < 306936 ∧ cP NW NT cs y = y

theorem andT : ∀ {a b : Bool}, andB a b = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => by cases h
  | false, _, h => by cases h

theorem mem_selW {w : List Nat} {v : Nat} :
    ∀ {ws : List (List Nat)} {j : Nat}, w ∈ selW ws v j → w ∈ ws
  | [], _, h => absurd h List.not_mem_nil
  | w' :: ws, j, h => by
    change w ∈ Bool.rec (motive := fun _ => List (List Nat)) (selW ws v (j + 1))
      (w' :: selW ws v (j + 1)) (Nat.beq (bitN v j) 1) at h
    rcases Bool.eq_false_or_eq_true (Nat.beq (bitN v j) 1) with hb | hb <;> rw [hb] at h
    · rcases List.mem_cons.1 h with e | e
      · rw [e]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_selW e)
    · exact List.mem_cons_of_mem _ (mem_selW h)

theorem prodC_eq : ∀ l : List (List Nat), prodC l = (l.map dW).flatten
  | [] => rfl
  | w :: l => by
    change dW w ++ prodC l = _
    rw [prodC_eq l, List.map_cons, List.flatten_cons]

theorem vC_inW (ws : List (List Nat)) (v : Nat) : InW (ws.map dW) (vC ws v) :=
  ⟨(selW ws v 0).map dW, fun u hu => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    exact List.mem_map.2 ⟨w, mem_selW hw, rfl⟩, prodC_eq _⟩

theorem testBit_ptsM (y : Nat) : ptsM.testBit y = decide (y < 306936) := by
  unfold ptsM
  exact CFSG.KS.Fi24FixP.testBit_ones _ _

theorem beq_bitN (F p : Nat) : Nat.beq (bitN F p) 1 = F.testBit p := by
  have e : bitN F p = F / 2 ^ p % 2 := by
    change (F >>> p) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (F / 2 ^ p) with h | h <;> rw [h] <;> rfl

theorem testBit_same (F p : Nat) {x : Nat} (hx : x < 306936) :
    (same F p).testBit x = true ↔ (F.testBit x = true ↔ F.testBit p = true) := by
  unfold same
  rw [beq_bitN]
  rcases Bool.eq_false_or_eq_true (F.testBit p) with hp | hp <;> rw [hp]
  · change F.testBit x = true ↔ _
    simp
  · change (ptsM ^^^ F).testBit x = true ↔ _
    rw [Nat.testBit_xor, testBit_ptsM, decide_eq_true hx]
    cases F.testBit x <;> simp

theorem testBit_same_hi {F p x : Nat} (hF : ∀ y, F.testBit y = true → y < 306936)
    (hx : 306936 ≤ x) : (same F p).testBit x = false := by
  have hFx : F.testBit x = false := by
    cases h : F.testBit x
    · rfl
    · exact absurd (hF x h) (by omega)
  unfold same
  rw [beq_bitN]
  rcases Bool.eq_false_or_eq_true (F.testBit p) with hp | hp <;> rw [hp]
  · exact hFx
  · change (ptsM ^^^ F).testBit x = false
    rw [Nat.testBit_xor, testBit_ptsM, decide_eq_false (by omega), hFx]
    rfl

theorem testBit_fixC' (hV : VN NW NT) (cs : List Nat) {y : Nat} (hy : y < 306936) :
    (fixC NW NT cs).testBit y = true ↔ cP NW NT cs y = y := by
  rw [testBit_fixC hV]
  exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩

theorem sig_cons (hV : VN NW NT) {w : List Nat} {ws : List (List Nat)} {p x : Nat}
    (hp : p < 306936) :
    Sig NW NT (w :: ws) p x ↔ Sig NW NT ws p x ∧ (same (fixC NW NT (dW w)) p).testBit x = true := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨⟨hx, fun w' hw' => h w' (List.mem_cons_of_mem _ hw')⟩, ?_⟩
    rw [testBit_same _ _ hx, testBit_fixC' hV _ hx, testBit_fixC' hV _ hp]
    exact h w List.mem_cons_self
  · rintro ⟨⟨hx, h⟩, hs⟩
    rw [testBit_same _ _ hx, testBit_fixC' hV _ hx, testBit_fixC' hV _ hp] at hs
    refine ⟨hx, fun w' hw' => ?_⟩
    rcases List.mem_cons.1 hw' with e | e
    · rw [e]
      exact hs
    · exact h w' e

theorem testBit_sigs (hV : VN NW NT) {p q : Nat} (hp : p < 306936) (hq : q < 306936) :
    ∀ (ws : List (List Nat)) {x : Nat}, x < 524288 →
      ((sigs NW NT ws p q).testBit x = true ↔ Sig NW NT ws p x) ∧
      ((sigs NW NT ws p q).testBit (524288 + x) = true ↔ Sig NW NT ws q x)
  | [], x, hx => by
    have e : sigs NW NT [] p q = Nat.lor ptsM (Nat.shiftLeft ptsM (nat_lit 524288)) := rfl
    have h1 : decide (524288 + x ≥ 524288) = true := decide_eq_true (by omega)
    have h2 : decide (x ≥ 524288) = false := decide_eq_false (by omega)
    have h3 : 524288 + x - 524288 = x := by omega
    rw [e, nlor, nshl, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, h1, h2, h3,
      testBit_ptsM, testBit_ptsM, testBit_ptsM, decide_eq_false (by omega : ¬ 524288 + x < 306936)]
    simp
  | w :: ws, x, hx => by
    have e : sigs NW NT (w :: ws) p q = Nat.land (sigs NW NT ws p q)
        (Nat.lor (same (fixC NW NT (dW w)) p) (Nat.shiftLeft (same (fixC NW NT (dW w)) q) 524288)) := by
      have e0 : sigs NW NT (w :: ws) p q = strictN (sigs NW NT ws p q) (fun a =>
          strictN (fixC NW NT (dW w)) (fun F =>
            Nat.land a (Nat.lor (same F p) (Nat.shiftLeft (same F q) 524288)))) := rfl
      rw [e0]
      simp only [Fi24NetPt.strictN_eq]
    obtain ⟨ih1, ih2⟩ := testBit_sigs hV hp hq ws hx
    have hF : ∀ y, (fixC NW NT (dW w)).testBit y = true → y < 306936 :=
      fun y h => ((testBit_fixC hV _ y).1 h).1
    have h1 : decide (524288 + x ≥ 524288) = true := decide_eq_true (by omega)
    have h2 : decide (x ≥ 524288) = false := decide_eq_false (by omega)
    have h3 : 524288 + x - 524288 = x := by omega
    rw [e, nland, nlor, nshl, Nat.testBit_and, Nat.testBit_and, Nat.testBit_or, Nat.testBit_or,
      Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, h1, h2, h3, testBit_same_hi hF (by omega : 306936 ≤ 524288 + x),
      sig_cons hV hp, sig_cons hV hq]
    simp only [Bool.false_and, Bool.or_false, Bool.true_and, Bool.false_or, Bool.and_eq_true]
    rw [ih1, ih2]
    exact ⟨Iff.rfl, Iff.rfl⟩

theorem testBit_cutP (hV : VN NW NT) {ws : List (List Nat)} {F q S : Nat} (hq : q < 524288) :
    ∀ (tv : List Nat) {x : Nat}, x < 306936 →
      ((cutP NW NT ws F q S tv).testBit x = true ↔ S.testBit x = true ∧
        ∀ t ∈ tv, (F.testBit (cP NW NT (vC ws t) x) = true ↔
          F.testBit (cP NW NT (vC ws t) q) = true))
  | [], x, _ => by
    change S.testBit x = true ↔ _
    simp
  | t :: tv, x, hx => by
    have e : cutP NW NT ws F q S (t :: tv) =
        Nat.land (cutP NW NT ws F q S tv) (same (wkC NW NT (vC ws t) F) q) := by
      have e0 : cutP NW NT ws F q S (t :: tv) = strictN (cutP NW NT ws F q S tv) (fun a =>
          strictN (wkC NW NT (vC ws t) F) (fun C => Nat.land a (same C q))) := rfl
      rw [e0]
      simp only [Fi24NetPt.strictN_eq]
    rw [e, nland, Nat.testBit_and, Bool.and_eq_true, testBit_cutP hV hq tv hx, testBit_same _ _ hx,
      testBit_wkC hV _ _ (by omega), testBit_wkC hV _ _ hq, List.forall_mem_cons]
    tauto

theorem testBit_pl1 : ∀ (pp : List (Nat × Nat)) (x : Nat), (pl1 pp).testBit x = true →
    ∃ v, (x, v) ∈ pp
  | [], x, h => by
    change (0 : Nat).testBit x = true at h
    simp at h
  | e :: pp, x, h => by
    change ((1 <<< e.1) ||| pl1 pp).testBit x = true at h
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
    rcases h with h | h
    · have hx : e.1 = x := of_decide_eq_true h
      refine ⟨e.2, ?_⟩
      rw [← hx]
      exact List.mem_cons_self
    · obtain ⟨v, hv⟩ := testBit_pl1 pp x h
      exact ⟨v, List.mem_cons_of_mem _ hv⟩

theorem ppOK_spec {ws : List (List Nat)} {p q : Nat} {pp : List (Nat × Nat)}
    (h : ppOK NW NT ws p q pp = true) :
    ∀ e ∈ pp, cP NW NT (vC ws e.2) p = p ∧ cP NW NT (vC ws e.2) q = e.1 := fun e he => by
  obtain ⟨h1, h2⟩ := andT (CFSG.KS.Fi24ThreeO.allL_spec h e he)
  rw [← ptC_eq, ← ptC_eq]
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem sigOK_spec (hV : VN NW NT) {ws : List (List Nat)} {p q : Nat} {c tv : List Nat}
    {pp : List (Nat × Nat)} {n : Nat} (hp : p < 306936) (hq : q < 306936)
    (h : sigOK NW NT ws p q c tv pp n = true) :
    #((range 306936).filter fun x => ∀ w ∈ ws, (cP NW NT (dW w) x = x ↔ cP NW NT (dW w) p = p)) =
        n ∧
      (∀ x < 306936, (∀ w ∈ ws, (cP NW NT (dW w) x = x ↔ cP NW NT (dW w) q = q)) →
        (∀ t ∈ tv, (FX NW NT c (cP NW NT (vC ws t) x) ↔ FX NW NT c (cP NW NT (vC ws t) q))) →
        ∃ v, (x, v) ∈ pp) ∧
      ∀ e ∈ pp, cP NW NT (vC ws e.2) p = p ∧ cP NW NT (vC ws e.2) q = e.1 := by
  unfold sigOK passOK at h
  rw [letB_eq'] at h
  obtain ⟨h1, h23⟩ := andT h
  obtain ⟨h2, h3⟩ := andT h23
  rw [letB_eq', letB_eq'] at h2
  have hlo : ∀ x < 524288, (Nat.land (sigs NW NT ws p q) (ones 524288)).testBit x =
      (sigs NW NT ws p q).testBit x := fun x hx => by
    rw [nland, Nat.testBit_and, CFSG.KS.Fi24FixP.testBit_ones, decide_eq_true hx, Bool.and_true]
  refine ⟨?_, fun x hx hs ht => ?_, ppOK_spec h3⟩
  · have e := Nat.eq_of_beq_eq_true h1
    rw [CFSG.KS.Fi24FixP.popcount_19, CFSG.KS.Fi24FixP.sum_bits] at e
    rw [← e]
    refine congrArg Finset.card (Finset.ext fun x => ?_)
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hx, hw⟩
      refine ⟨by omega, ?_⟩
      rw [hlo x (by omega)]
      exact (testBit_sigs hV hp hq ws (by omega)).1.2 ⟨hx, hw⟩
    · rintro ⟨hx, hb⟩
      rw [hlo x hx] at hb
      exact (testBit_sigs hV hp hq ws hx).1.1 hb
  · have hC := Nat.eq_of_beq_eq_true h2
    have hS : (Nat.shiftRight (sigs NW NT ws p q) 524288).testBit x = true := by
      rw [nshr, Nat.testBit_shiftRight]
      exact (testBit_sigs hV hp hq ws (by omega)).2.2 ⟨hx, hs⟩
    have hb := (testBit_cutP (ws := ws) (F := fixC NW NT c) (q := q) hV (by omega) tv hx).2 ⟨hS, fun t ht' => by
      rw [testBit_fixC hV, testBit_fixC hV]
      exact ht t ht'⟩
    rw [← hC, nland, Nat.testBit_and, Bool.and_eq_true] at hb
    exact testBit_pl1 pp x hb.2

theorem testBit_fixAll (hV : VN NW NT) : ∀ (css : List (List Nat)) (x : Nat),
    (fixAll NW NT css).testBit x = true ↔ x < 306936 ∧ ∀ cs ∈ css, cP NW NT cs x = x
  | [], x => by
    change ptsM.testBit x = true ↔ _
    rw [testBit_ptsM]
    simp
  | cs :: css, x => by
    have e : fixAll NW NT (cs :: css) = Nat.land (fixC NW NT cs) (fixAll NW NT css) := by
      have e0 : fixAll NW NT (cs :: css) =
          strictN (fixAll NW NT css) (fun a => Nat.land (fixC NW NT cs) a) := rfl
      rw [e0]
      simp only [Fi24NetPt.strictN_eq]
    rw [e, nland, Nat.testBit_and, Bool.and_eq_true, testBit_fixC hV, testBit_fixAll hV css x,
      List.forall_mem_cons]
    tauto

theorem fixAllOK_spec (hV : VN NW NT) {css : List (List Nat)} {P : Nat}
    (h : fixAllOK NW NT css P = true) {x : Nat} (hx : x < 306936)
    (hf : ∀ cs ∈ css, cP NW NT cs x = x) : P.testBit x = true := by
  unfold fixAllOK at h
  rw [letB_eq'] at h
  have e : fixAll NW NT css &&& P = fixAll NW NT css := Nat.eq_of_beq_eq_true h
  have hb : (fixAll NW NT css).testBit x = true := (testBit_fixAll hV css x).2 ⟨hx, hf⟩
  rw [← e, Nat.testBit_and, Bool.and_eq_true] at hb
  exact hb.2

theorem fixOK_cP_spec (hV : VN NW NT) {cs : List Nat} {c : Nat}
    (h : Fi24FixP.fixOK (plC NW NT) cs c = true) :
    #((range 306936).filter fun x => cP NW NT cs x = x) = c := by
  have e := CFSG.KS.Fi24FixP.fixOK_spec (σ := CF NW NT) (fun l _ _ hq => CF_lt hV l hq)
    (fun l _ v q _ => testBit_plC hV l v q) h
  rw [← e]
  exact congrArg Finset.card (Finset.filter_congr fun x _ => Iff.rfl)

end CFSG.KS.Fi24E

end
