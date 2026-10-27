module

public import CFSG.GF2Type.SmithTypeE.E7.E23Four
public import CFSG.GF2Type.SmithTypeE.E7.ModBase
public import CFSG.GF2Type.SmithTypeE.E7.ModWt
public import Certificates.Certificate38772

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 (wt tvCols applyCols mf7Ap mf7Ap_eq mf7Commute mf7SpanOK mf7SpanData Mf7Span
  mf7Reps stabCls stabOrd e4f7ChkWord e4f7ChkPlane e4f7Root e4f7Syn0 e4f7Tree e4f7Word e4f7Gens
  e4f7ApplyWord e4f7FixIdx e4f7FixPre)
open CFSG.GF2Type.SmithTypeE.DMod

theorem relC_of_sq_eq_one {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 2 = 1) : RelC a b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h)
  rw [mul_inv_rev, hainv, hbinv] at hab
  exact hab.symm

theorem relB_of_cube_eq_one {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 3 = 1) : RelB a b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hX : (a * b * a) * (b * a * b) = 1 := by
    rw [← h, pow_three]
    simp only [mul_assoc]
  have hXeq : a * b * a = (b * a * b)⁻¹ := eq_inv_of_mul_eq_one_left hX
  unfold RelB
  rw [hXeq, mul_inv_rev, mul_inv_rev, hainv, hbinv]
  simp only [mul_assoc]

theorem orderOf_ne_of_not_rel
    {a : Fin 365211} (hC : ¬ RelC (tvE 0) (tvE a))
    (hB : ¬ RelB (tvE 0) (tvE a)) :
    orderOf (tvE 0 * tvE a) ≠ 1 ∧ orderOf (tvE 0 * tvE a) ≠ 2 ∧ orderOf (tvE 0 * tvE a) ≠ 3 := by
  have h0 : tvE 0 * tvE 0 = 1 := tvE_mul_self 0
  have ha : tvE a * tvE a = 1 := tvE_mul_self a
  have hsq : (tvE 0 * tvE a) ^ 2 ≠ 1 := fun h => hC (relC_of_sq_eq_one h0 ha h)
  have hcube : (tvE 0 * tvE a) ^ 3 ≠ 1 := fun h => hB (relB_of_cube_eq_one h0 ha h)
  refine ⟨fun h1 => hsq ?_, fun h2 => hsq ?_, fun h3 => hcube ?_⟩
  · rw [orderOf_eq_one_iff.mp h1, one_pow]
  · have := pow_orderOf_eq_one (tvE 0 * tvE a)
    rwa [h2] at this
  · have := pow_orderOf_eq_one (tvE 0 * tvE a)
    rwa [h3] at this

theorem orderOf_tvE_mul
    (a : Fin 365211) : orderOf (tvE 0 * tvE a) = orderOf (tvP 0 * tvP a) := by
  obtain ⟨g, hgdef⟩ : ∃ g : TD6, g = (⟨tvP 0, tvP_mem 0⟩ : TD6) * ⟨tvP a, tvP_mem a⟩ :=
    ⟨_, rfl⟩
  have hg : (g : Equiv.Perm (Fin 365211)) = tvP 0 * tvP a := by
    subst hgdef
    rfl
  have hr : rhoMod g = tvE 0 * tvE a := by
    rw [hgdef, map_mul, rhoMod_tvP, rhoMod_tvP]
    rfl
  rw [← hg, Subgroup.orderOf_coe g, ← orderOf_injective rhoMod rhoMod_injective g, hr]

theorem class_four_of_not
    {c : ℕ} (hc : c < 6) (hr : mf7Reps[c]! < 365211)
    (hC : ¬ RelC (tvE 0) (tvE ⟨mf7Reps[c]!, hr⟩))
    (hB : ¬ RelB (tvE 0) (tvE ⟨mf7Reps[c]!, hr⟩)) : c = 4 := by
  obtain ⟨-, hrc⟩ := reps_cls hc
  have hrc' : stabCls (⟨mf7Reps[c]!, hr⟩ : Fin 365211).val = c := hrc
  have ho : orderOf (tvE 0 * tvE (⟨mf7Reps[c]!, hr⟩ : Fin 365211)) = stabOrd[c]! := by
    rw [orderOf_tvE_mul, orderOf_tvP_mul_tvP, hrc']
  have h := orderOf_ne_of_not_rel hC hB
  rw [ho] at h
  have key : ∀ n < 6, stabOrd[n]! ≠ 1 → stabOrd[n]! ≠ 2 → stabOrd[n]! ≠ 3 → n = 4 := by
    decide
  exact key c hc h.1 h.2.1 h.2.2

theorem inEV_of_inE7
    {k i : Nat} (hk : k < 365211) (h : InE k i) :
    InEV (tvEquiv k) (wtV i) := by
  obtain ⟨c, -, hc⟩ := h
  refine ⟨decode32 c, ?_⟩
  rw [wtV, ← hc, decode32_xor, tvEquiv_decode hk]

theorem inE_of_inEV7
    {k i : Nat}
    (hk : k < 365211) (hi : i < 75735) (h : InEV (tvEquiv k) (wtV i)) : InE k i := by
  obtain ⟨x, hx⟩ := h
  refine ⟨code32 x, code32_lt x, eq_of_decode32_eq ?_ (wt7_lt hi) ?_⟩
  · exact Nat.xor_lt_two_pow (n := 32) (applyCols_tv_lt hk _) (code32_lt x)
  · rw [decode32_xor, ← tvEquiv_decode hk, decode32_code32]
    exact hx.symm

theorem syn_of_inE_span7 {r : Nat} {D : Mf7Span} (hD : mf7SpanOK (tvCols r) D = true) {i : Nat}
    (h : InE r i) : applyCols D.syn (wt i) = 0 := by
  obtain ⟨c, hc, hce⟩ := h
  have hsp := (spanOK_parts hD).2.2
  rw [← hce]
  exact syn_comm32 (size_tvCols r) (fun m hm => (hsp m hm).2.2) hc

theorem applyWord_eq_foldr : ∀ (w : List Nat) (c : Nat),
    applyWord w c = w.foldr (fun r c => applyCols (tvCols r) c) c
  | [], _ => rfl
  | r :: w, c => by
    rw [List.foldr_cons, ← applyWord_eq_foldr w c]
    rfl

theorem e4f7_word_check :
    ∃ r₀ < 75735, ∀ i < 75735, InE 0 i →
      ∃ w : List Nat, (∀ r ∈ w, r < 365211 ∧ ∀ c < 2 ^ 32,
        applyCols (tvCols r) (applyCols (tvCols 0) c) =
          applyCols (tvCols 0) (applyCols (tvCols r) c)) ∧
        applyWord w (wt r₀) = wt i := by
  obtain ⟨r₀, hr₀, hall⟩ := Certificates.certificate38772.1
  refine ⟨r₀, hr₀, fun i hi hE => ?_⟩
  obtain ⟨w, hw, he⟩ := hall i hi hE
  exact ⟨w, hw, (applyWord_eq_foldr w _).trans he⟩

theorem creach_word7 :
    ∀ (w : List Nat),
      (∀ r ∈ w, r < 365211 ∧ ∀ c < 2 ^ 32,
        applyCols (tvCols r) (applyCols (tvCols 0) c) =
          applyCols (tvCols 0) (applyCols (tvCols r) c)) → ∀ c : Nat,
      CReach (tvE 0) (decode32 c) (decode32 (applyWord w c))
  | [], _, _ => CReach.refl _ _
  | r :: w, hw, c => by
    obtain ⟨hr, hcomm⟩ := hw r List.mem_cons_self
    have ih := creach_word7 w (fun r' hr' => hw r' (List.mem_cons_of_mem _ hr')) c
    have h0 : (0 : Nat) < 365211 := by norm_num
    have hR' : RelC (tvEquiv r) (tvEquiv 0) := by
      unfold RelC
      refine LinearEquiv.ext fun v => ?_
      have e := (decode_tv_comm hr h0 (code32 v)).trans
        ((congrArg decode32 (hcomm _ (code32_lt v))).trans (decode_tv_comm h0 hr (code32 v)).symm)
      rw [decode32_code32] at e
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      set_option maxRecDepth 100000 in
      exact e
    have hR : RelC (tvE ⟨r, hr⟩) (tvE 0) := hR'
    have e : decode32 (applyWord (r :: w) c) = tvE ⟨r, hr⟩ (decode32 (applyWord w c)) := by
      show decode32 (applyCols (tvCols r) (applyWord w c)) =
        tvEquiv r (decode32 (applyWord w c))
      rw [tvEquiv_decode hr]
    rw [e]
    exact CReach.cons ⟨r, hr⟩ hR ih

theorem creach_pair7
    {i₀ i : Nat}
    (hi₀ : i₀ < 75735) (hi : i < 75735) (h₀ : InE 0 i₀) (h : InE 0 i) :
    CReach (tvE 0) (wtV i₀) (wtV i) := by
  obtain ⟨r₀, -, hall⟩ := e4f7_word_check
  have key : ∀ j < 75735, InE 0 j → CReach (tvE 0) (wtV r₀) (wtV j) := fun j hj hE => by
    obtain ⟨w, hw, he⟩ := hall j hj hE
    have := creach_word7 w hw (wt r₀)
    rw [he] at this
    exact this
  exact (key i₀ hi₀ h₀).symm.trans (key i hi h)

theorem applyWord_decode7 :
    ∀ (w : List (Fin 365211)) (c : Nat),
      decode32 (applyWord (w.map Fin.val) c) = wordF w (decode32 c)
  | [], _ => rfl
  | r :: w, c => by
    have ih := applyWord_decode7 w c
    show decode32 (applyCols (tvCols r.val) (applyWord (w.map Fin.val) c)) =
      tvEquiv r.val (wordF w (decode32 c))
    rw [← ih, tvEquiv_decode r.2]

theorem applyWord_lt7
    (w : List Nat) (hw : ∀ r ∈ w, r < 365211) {c : Nat}
    (hc : c < 2 ^ 32) : applyWord w c < 2 ^ 32 := by
  cases w with
  | nil => exact hc
  | cons r w => exact applyCols_tv_lt (hw r List.mem_cons_self) _

theorem word7
    {k i₀ i : Nat} (hk : k < 365211) (hi₀ : i₀ < 75735)
    (hi : i < 75735) (h₀ : InE k i₀) (h : InE k i) :
    ∃ w : List Nat, (∀ r ∈ w, r < 365211 ∧ ∀ c < 2 ^ 32,
      applyCols (tvCols r) (applyCols (tvCols k) c) =
        applyCols (tvCols k) (applyCols (tvCols r) c)) ∧ applyWord w (wt i₀) = wt i := by
  obtain ⟨g, hg, hg0⟩ := exists_mem_TD6_apply_zero_eq (⟨k, hk⟩ : Fin 365211)
  obtain ⟨G, hG0⟩ : ∃ G : TD6, (G : Equiv.Perm (Fin 365211)) 0 = ⟨k, hk⟩ :=
    ⟨⟨g, hg⟩, hg0⟩
  have e₀ : rhoMod G (wtV (G⁻¹ • (⟨i₀, hi₀⟩ : Fin 75735)).val) = wtV i₀ := by
    rw [rhoMod_wtV, smul_inv_smul]
  have e₁ : rhoMod G (wtV (G⁻¹ • (⟨i, hi⟩ : Fin 75735)).val) = wtV i := by
    rw [rhoMod_wtV, smul_inv_smul]
  have hV₀ : InEV (tvE 0) (wtV (G⁻¹ • (⟨i₀, hi₀⟩ : Fin 75735)).val) := by
    refine (inEV_tvE_smul G 0 _).mp ?_
    rw [hG0, e₀]
    exact inEV_of_inE7 hk h₀
  have hV₁ : InEV (tvE 0) (wtV (G⁻¹ • (⟨i, hi⟩ : Fin 75735)).val) := by
    refine (inEV_tvE_smul G 0 _).mp ?_
    rw [hG0, e₁]
    exact inEV_of_inE7 hk h
  have hS₀ : InE 0 (G⁻¹ • (⟨i₀, hi₀⟩ : Fin 75735)).val :=
    inE_of_inEV7 (k := 0) (by norm_num) (G⁻¹ • (⟨i₀, hi₀⟩ : Fin 75735)).isLt hV₀
  have hS₁ : InE 0 (G⁻¹ • (⟨i, hi⟩ : Fin 75735)).val :=
    inE_of_inEV7 (k := 0) (by norm_num) (G⁻¹ • (⟨i, hi⟩ : Fin 75735)).isLt hV₁
  have hR := (creach_pair7 (G⁻¹ • (⟨i₀, hi₀⟩ : Fin 75735)).isLt
    (G⁻¹ • (⟨i, hi⟩ : Fin 75735)).isLt hS₀ hS₁).smul G
  rw [hG0, e₀, e₁] at hR
  obtain ⟨w', hw', hw'e⟩ := hR
  have hlt : ∀ r ∈ w'.map Fin.val, r < 365211 := by
    intro r hr
    obtain ⟨r', -, rfl⟩ := List.mem_map.mp hr
    exact r'.2
  refine ⟨w'.map Fin.val, fun r hr => ?_, ?_⟩
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact ⟨r'.2, comm_code_of_relC r'.2 hk (hw' r' hr')⟩
  · refine eq_of_decode32_eq (applyWord_lt7 _ hlt (wt7_lt hi₀)) (wt7_lt hi) ?_
    rw [applyWord_decode7]
    exact hw'e

theorem plane7
    {k l : Nat} (hk : k < 365211) (hl : l < 365211)
    (hkl : k ≠ l)
    (hC : ¬ ∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c))
    (hB : ¬ ∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))) :
    ∃ i < 75735, InE k i ∧ applyCols (tvCols l) (wt i) = wt i ∧ ¬ InE l i := by
  have hKL : (⟨k, hk⟩ : Fin 365211) ≠ ⟨l, hl⟩ := fun h => hkl (Fin.mk.inj h)
  have hnC : ¬ RelC (tvE ⟨k, hk⟩) (tvE ⟨l, hl⟩) := fun h => hC (comm_code_of_relC hk hl h)
  have hnB : ¬ RelB (tvE ⟨k, hk⟩) (tvE ⟨l, hl⟩) := fun h => hB (braid_code_of_relB hk hl h)
  obtain ⟨c, hc6, -, p, hp, hp0, hr, hpL⟩ := exists_rep_map ⟨k, hk⟩ ⟨l, hl⟩ hKL
  have hnC0 : ¬ RelC (tvE 0) (tvE ⟨mf7Reps[c]!, hr⟩) := by
    intro h
    apply hnC
    have h' := relC_tvE ⟨p, hp⟩ h
    have e0 : ((⟨p, hp⟩ : TD6) : Equiv.Perm (Fin 365211)) 0 = ⟨k, hk⟩ := hp0
    have e1 : ((⟨p, hp⟩ : TD6) : Equiv.Perm (Fin 365211)) ⟨mf7Reps[c]!, hr⟩ = ⟨l, hl⟩ := hpL
    rw [e0, e1] at h'
    exact h'
  have hnB0 : ¬ RelB (tvE 0) (tvE ⟨mf7Reps[c]!, hr⟩) := by
    intro h
    apply hnB
    have h' := relB_tvE ⟨p, hp⟩ h
    have e0 : ((⟨p, hp⟩ : TD6) : Equiv.Perm (Fin 365211)) 0 = ⟨k, hk⟩ := hp0
    have e1 : ((⟨p, hp⟩ : TD6) : Equiv.Perm (Fin 365211)) ⟨mf7Reps[c]!, hr⟩ = ⟨l, hl⟩ := hpL
    rw [e0, e1] at h'
    exact h'
  have hc4 : c = 4 := class_four_of_not hc6 hr hnC0 hnB0
  subst hc4
  obtain ⟨G, hG⟩ : ∃ G : TD6, (G : Equiv.Perm (Fin 365211)) = p := ⟨⟨p, hp⟩, rfl⟩
  have hG0 : (G : Equiv.Perm (Fin 365211)) 0 = ⟨k, hk⟩ := by
    rw [hG]
    exact hp0
  have hGL : (G : Equiv.Perm (Fin 365211)) ⟨mf7Reps[4]!, hr⟩ = ⟨l, hl⟩ := by
    rw [hG]
    exact hpL
  have hP := Certificates.certificate38772.2
  simp only [e4f7ChkPlane, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hP
  obtain ⟨⟨⟨⟨hfi, hfp⟩, e0⟩, e1⟩, hne⟩ := hP
  have hI0 : InE 0 e4f7FixIdx := by
    refine ⟨wt e4f7FixPre, wt7_lt hfp, ?_⟩
    simpa only [mf7Ap_eq] using e0
  have e1' : applyCols (tvCols mf7Reps[4]!) (wt e4f7FixIdx) = wt e4f7FixIdx := by
    simpa only [mf7Ap_eq] using e1
  have hsp : mf7SpanOK (tvCols mf7Reps[4]!) (mf7SpanData (tvCols mf7Reps[4]!)) = true :=
    (reps_int (c := 4) (by norm_num) (by norm_num)).1
  have hnotI : ¬ InEV (tvE ⟨mf7Reps[4]!, hr⟩) (wtV e4f7FixIdx) := by
    intro hI
    have hE := inE_of_inEV7 hr hfi hI
    exact hne (by rw [mf7Ap_eq]; exact syn_of_inE_span7 hsp hE)
  have hfixI : tvE ⟨mf7Reps[4]!, hr⟩ (wtV e4f7FixIdx) = wtV e4f7FixIdx := by
    show tvEquiv mf7Reps[4]! (decode32 (wt e4f7FixIdx)) = decode32 (wt e4f7FixIdx)
    rw [tvEquiv_decode hr, e1']
  obtain ⟨j, hj⟩ : ∃ j : Fin 75735, j = G • (⟨e4f7FixIdx, hfi⟩ : Fin 75735) := ⟨_, rfl⟩
  have e : rhoMod G (wtV e4f7FixIdx) = wtV j.val := by
    rw [hj]
    exact rhoMod_wtV G ⟨e4f7FixIdx, hfi⟩
  have hV : InEV (tvE 0) (wtV e4f7FixIdx) := inEV_of_inE7 (k := 0) (by norm_num) hI0
  have hV' : InEV (tvE ⟨k, hk⟩) (rhoMod G (wtV e4f7FixIdx)) := by
    rw [← hG0]
    exact (inEV_tvE_smul G 0 _).mpr hV
  rw [e] at hV'
  have hEk : InE k j.val := inE_of_inEV7 hk j.isLt hV'
  have hfixV : tvE ⟨l, hl⟩ (wtV j.val) = wtV j.val := by
    have h := (tvE_fix_smul G ⟨mf7Reps[4]!, hr⟩ (wtV e4f7FixIdx)).mpr hfixI
    rw [hGL, e] at h
    exact h
  refine ⟨j.val, j.isLt, hEk, ?_, ?_⟩
  · refine eq_of_decode32_eq (applyCols_tv_lt hl (wt j.val)) (wt7_lt j.isLt) ?_
    rw [← tvEquiv_decode hl]
    exact hfixV
  · intro hEl
    have hL := inEV_of_inE7 hl hEl
    have h2 : InEV (tvE ((G : Equiv.Perm (Fin 365211)) ⟨mf7Reps[4]!, hr⟩))
        (rhoMod G (wtV e4f7FixIdx)) := by
      rw [hGL, e]
      exact hL
    exact hnotI ((inEV_tvE_smul G ⟨mf7Reps[4]!, hr⟩ (wtV e4f7FixIdx)).mp h2)

theorem e23FourFacts7 :
    E23FourFacts7 :=
  ⟨fun hr _ hc => tv_invol_code hr hc, fun hk hi₀ hi h₀ h => word7 hk hi₀ hi h₀ h,
    fun hk hl hkl hC hB => plane7 hk hl hkl hC hB⟩

theorem smithE7E23Four_of_model
    (hM : SmithE7Model) (h33 : SmithE7E33)
    (h34a : SmithE7E34a) (h34b : SmithE7E34b) (h24 : SmithE7E24) : SmithE7E23Four :=
  smithE7E23Four_of e23FourFacts7 hM h33 h34a h34b h24

end CFSG.GF2Type.SmithTypeE.E7
