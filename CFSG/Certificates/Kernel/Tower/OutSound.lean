module

public import Certificates.Data.Kernel.Tower.Out
public import CFSG.Certificates.Kernel.Tower.ChiSound
public import CFSG.Certificates.Kernel.Tower.L1Sound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower Subgroup

theorem bitS_true_iff {S k : Nat} : bitS S k = true ↔ S.testBit k = true := by
  unfold bitS
  rw [Nat.blt_eq]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.1 h)
    have hi' : (S &&& (1 <<< k)).testBit i = true := hi
    rw [Nat.testBit_and, Bool.and_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at hi'
    obtain ⟨h1, h2⟩ := hi'
    have e : k = i := of_decide_eq_true h2
    rw [e]
    exact h1
  · intro h
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 : (S &&& (1 <<< k)).testBit k = true := by
      rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_self, h, Bool.and_self]
    have h0' : S &&& (1 <<< k) = 0 := h0
    rw [h0', Nat.zero_testBit] at h1
    exact absurd h1 Bool.false_ne_true

theorem bitS_lor {a b k : Nat} :
    bitS (Nat.lor a b) k = true ↔ bitS a k = true ∨ bitS b k = true := by
  rw [bitS_true_iff, bitS_true_iff, bitS_true_iff]
  change (a ||| b).testBit k = true ↔ _
  rw [Nat.testBit_or, Bool.or_eq_true]

theorem bitS_zero' (k : Nat) : bitS 0 k = false := by
  cases h : bitS 0 k
  · rfl
  · rw [bitS_true_iff, Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true

theorem bitS_one_shl {a k : Nat} (h : bitS (Nat.shiftLeft 1 a) k = true) : a = k := by
  rw [bitS_true_iff] at h
  change (1 <<< a).testBit k = true at h
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h
  exact of_decide_eq_true h

theorem bitS_one_shl_self (a : Nat) : bitS (Nat.shiftLeft 1 a) a = true := by
  rw [bitS_true_iff]
  change (1 <<< a).testBit a = true
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self]

variable {IL HD : Nat}

theorem oMask_mem {a k : Nat} : ∀ n, bitS (oMask IL a n) k = true → ∃ q < n, l16 IL (a + q) = k := by
  intro n
  induction n with
  | zero =>
    intro h
    rw [show oMask IL a 0 = 0 from rfl, bitS_zero'] at h
    exact absurd h Bool.false_ne_true
  | succ n ih =>
    intro h
    have e : oMask IL a (n + 1) = Nat.lor (Nat.shiftLeft 1 (l16 IL (a + n))) (oMask IL a n) := rfl
    rw [e, bitS_lor] at h
    rcases h with h | h
    · exact ⟨n, Nat.lt_succ_self n, bitS_one_shl h⟩
    · obtain ⟨q, hq, e⟩ := ih h
      exact ⟨q, by omega, e⟩

theorem oMask_bit {a : Nat} : ∀ n, ∀ q < n, bitS (oMask IL a n) (l16 IL (a + q)) = true := by
  intro n
  induction n with
  | zero => exact fun q hq => absurd hq (Nat.not_lt_zero q)
  | succ n ih =>
    intro q hq
    have e : oMask IL a (n + 1) = Nat.lor (Nat.shiftLeft 1 (l16 IL (a + n))) (oMask IL a n) := rfl
    rw [e, bitS_lor]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
    · exact Or.inr (ih q hq)
    · exact Or.inl (bitS_one_shl_self _)

theorem oMaskAll_mem {k : Nat} : ∀ nl, bitS (oMaskAll HD IL nl) k = true →
    ∃ l < nl, ∃ q < oLen HD l, l16 IL (oSt HD l + q) = k := by
  intro nl
  induction nl with
  | zero =>
    intro h
    rw [show oMaskAll HD IL 0 = 0 from rfl, bitS_zero'] at h
    exact absurd h Bool.false_ne_true
  | succ n ih =>
    intro h
    have e : oMaskAll HD IL (n + 1) =
        Nat.lor (oMask IL (oSt HD n) (oLen HD n)) (oMaskAll HD IL n) := rfl
    rw [e, bitS_lor] at h
    rcases h with h | h
    · exact ⟨n, Nat.lt_succ_self n, oMask_mem _ h⟩
    · obtain ⟨l, hl, e⟩ := ih h
      exact ⟨l, by omega, e⟩

theorem oMaskAll_bit : ∀ nl, ∀ l < nl, ∀ q < oLen HD l,
    bitS (oMaskAll HD IL nl) (l16 IL (oSt HD l + q)) = true := by
  intro nl
  induction nl with
  | zero => exact fun l hl => absurd hl (Nat.not_lt_zero l)
  | succ n ih =>
    intro l hl q hq
    have e : oMaskAll HD IL (n + 1) =
        Nat.lor (oMask IL (oSt HD n) (oLen HD n)) (oMaskAll HD IL n) := rfl
    rw [e, bitS_lor]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · exact Or.inr (ih l hl q hq)
    · exact Or.inl (oMask_bit _ q hq)

variable {mul2 : Nat → Nat → Nat} {bc : Nat → Nat} {G U S LB : Nat} {HL : Nat → Nat}

theorem outB_parts (h : outB mul2 bc G U S HD LB IL HL = true) :
    (∀ i < 4, l16 HD i < 16384 ∧ mul2 (l16 U i) (l16 HD i) = 0) ∧
      oMaskAll HD IL (l16 HD 4) = S ∧ (∀ l < l16 HD 4, oLab mul2 G HD LB IL l = true) ∧
      ∀ m < 3, l16 HD (5 + m) < l16 HD 4 →
        oRep mul2 bc S (l16 IL (oSt HD (l16 HD (5 + m)))) (HL m) = true := by
  simp only [outB, Bool.and_eq_true, allB_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun i hi => ⟨Nat.le_of_ble_eq_true (h1 i hi).1, Nat.eq_of_beq_eq_true (h1 i hi).2⟩,
    Nat.eq_of_beq_eq_true h2, h3, fun m hm hlt => ?_⟩
  have h4' := h4 m hm
  have hb : Nat.blt (l16 HD (Nat.add 5 m)) (l16 HD 4) = true := Nat.blt_eq.mpr hlt
  rw [hb] at h4'
  simpa using h4'

theorem oLab_parts {l : Nat} (h : oLab mul2 G HD LB IL l = true) :
    oLen HD l ≤ 128 ∧ (oLen HD l = 128 → ∃ m < 3, l16 HD (5 + m) = l) ∧
      ∀ q < oLen HD l, oEnt mul2 G HD LB l (l16 IL (oSt HD l + q)) = true := by
  simp only [oLab, Bool.and_eq_true, allB_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨Nat.le_of_ble_eq_true h1, fun he => ?_, h3⟩
  rcases h2 with h2 | h2
  · rw [he] at h2
    exact absurd (Nat.le_of_ble_eq_true h2) (by omega)
  · obtain ⟨m, hm, e⟩ := anyB_eq_true.1 h2
    exact ⟨m, hm, Nat.eq_of_beq_eq_true e⟩

theorem oEnt_parts {l c : Nat} (h : oEnt mul2 G HD LB l c = true) :
    c < 16384 ∧ l8 LB c = l ∧ ∀ i < 4, l8 LB (oConj mul2 G HD c i) = l := by
  simp only [oEnt, Bool.and_eq_true, allB_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2,
    fun i hi => Nat.eq_of_beq_eq_true (h.2 i hi)⟩

theorem l16_strict {H : Nat} (h : ∀ q < 127, l16 H q < l16 H (q + 1)) :
    ∀ q < 128, ∀ q' < 128, q < q' → l16 H q < l16 H q' := by
  intro q _ q' hq' hlt
  induction q' with
  | zero => exact absurd hlt (Nat.not_lt_zero q)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hn | rfl
    · exact lt_trans (ih (by omega) hn) (h n (by omega))
    · exact h q (by omega)

theorem cntB_eq_card (n : Nat) (f : Nat → Bool) :
    cntB n f = ((Finset.range n).filter fun q => f q = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : cntB (n + 1) f = cond (f n) 1 0 + cntB n f := rfl
    rw [e, ih, Finset.range_add_one, Finset.filter_insert]
    cases hf : f n
    · simp
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      simp only [cond_true]
      omega

variable {Y : Type*} [Group Y] {dec : Nat → Y}

theorem conj_out (D' : ExtData Y) (h k : Y) :
    (⟨h, false⟩ : CycExt D') * ⟨k, true⟩ * (⟨h, false⟩ : CycExt D')⁻¹ =
      ⟨h * k * (D'.α h)⁻¹, true⟩ := by
  rw [CycExt.inv_mk_false, CycExt.mk_mul_mk, CycExt.mk_mul_mk]
  simp [CycExt.pw, CycExt.sq]

theorem card_ext (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec) (D' : ExtData Y) :
    Finite (CycExt D') ∧ Nat.card (CycExt D') = 32768 := by
  have hb : Function.Bijective (fun i : Fin 16384 => dec i) :=
    ⟨fun a b h => Fin.ext (M.inj a a.2 b b.2 h), fun y => by
      obtain ⟨c, hc, e⟩ := M.surj y (Subgroup.mem_top y)
      exact ⟨⟨c, hc⟩, e⟩⟩
  have hY : Nat.card Y = 16384 := by
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]
  have : Finite Y := Finite.of_surjective _ hb.2
  let e : CycExt D' ≃ Y × Bool :=
    { toFun := fun x => (x.k, x.d), invFun := fun p => ⟨p.1, p.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_prod, hY, Nat.card_eq_fintype_card, Fintype.card_bool]

theorem card_cent_mul {X : Type*} [Group X] [Finite X] (x : X) :
    Nat.card (MulAction.orbit (ConjAct X) x) * Nat.card (centralizer {x} : Subgroup X) =
      Nat.card X := by
  have e : MulAction.stabilizer (ConjAct X) x ≃ (centralizer {x} : Subgroup X) :=
    { toFun := fun c => ⟨ConjAct.ofConjAct c.1, by
        have h := MulAction.mem_stabilizer_iff.1 c.2
        rw [ConjAct.smul_def] at h
        rw [mem_centralizer_singleton_iff]
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h⟩,
      invFun := fun c => ⟨ConjAct.toConjAct c.1, by
        rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct,
          mul_inv_eq_iff_eq_mul]
        exact mem_centralizer_singleton_iff.1 c.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm,
    Subgroup.card_mul_index, Nat.card_congr ConjAct.ofConjAct.toEquiv]

theorem sq_ext_false (D' : ExtData Y) (h : Y) :
    (⟨h, false⟩ : CycExt D') ^ 2 = 1 ↔ h * h = 1 := by
  rw [pow_two, CycExt.mk_mul_mk, CycExt.one_def]
  simp [CycExt.pw, CycExt.sq]

theorem oRep_sound (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec) (D' : ExtData Y)
    (hS : ∀ k < 16384, (bitS S k = true ↔ (⟨dec k, true⟩ : CycExt D') ^ 2 = 1))
    (hbc : ∀ k < 16384, D'.α (dec k) = dec (bc k)) {r H : Nat} (hr : r < 16384)
    (hR : oRep mul2 bc S r H = true) :
    ¬ PInv (centralizer {(⟨dec r, true⟩ : CycExt D')} : Subgroup (CycExt D')) := by
  classical
  obtain ⟨hfin, hcard⟩ := card_ext M D'
  simp only [oRep, Bool.and_eq_true, allB_eq_true, Bool.not_eq_true'] at hR
  obtain ⟨⟨hH, hinc⟩, hn⟩ := hR
  have hlt : ∀ q < 128, l16 H q < 16384 := fun q hq => Nat.le_of_ble_eq_true (hH q hq).1.1
  have hcm : ∀ q < 128, dec (l16 H q) * dec r = dec r * D'.α (dec (l16 H q)) := by
    intro q hq
    have h1 := Nat.eq_of_beq_eq_true (hH q hq).1.2
    have h2 := Nat.le_of_ble_eq_true (hH q hq).2
    rw [hbc _ (hlt q hq), ← M.dec_mul _ (hlt q hq) _ hr, ← M.dec_mul _ hr _ h2, h1]
  have hst := l16_strict (fun q hq => Nat.le_of_ble_eq_true (hinc q hq))
  set xr : CycExt D' := ⟨dec r, true⟩
  let e : Nat × Bool → CycExt D' := fun p =>
    if p.2 then ⟨dec (l16 H p.1) * dec r, true⟩ else ⟨dec (l16 H p.1), false⟩
  let s : Finset (Nat × Bool) := Finset.range 128 ×ˢ Finset.univ
  have hsm : ∀ p : Nat × Bool, p ∈ s ↔ p.1 < 128 := fun p => by
    simp only [s, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
  have hscard : s.card = 256 := by
    simp only [s]
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool]
  clear_value s
  have hmem : ∀ p ∈ s, e p ∈ (centralizer {xr} : Subgroup (CycExt D')) := by
    intro p hp
    have hq : p.1 < 128 := (hsm p).1 hp
    have h0 : (⟨dec (l16 H p.1), false⟩ : CycExt D') ∈ (centralizer {xr} : Subgroup _) := by
      rw [mem_centralizer_singleton_iff, CycExt.mk_mul_mk, CycExt.mk_mul_mk]
      simp [CycExt.pw, CycExt.sq, hcm _ hq]
    have hx : xr ∈ (centralizer {xr} : Subgroup (CycExt D')) := mem_centralizer_singleton_iff.2 rfl
    by_cases hb : p.2 = true
    · have e1 : e p = ⟨dec (l16 H p.1), false⟩ * xr := by
        simp only [e, hb, if_true, xr, CycExt.mk_mul_mk]
        simp [CycExt.pw, CycExt.sq]
      rw [e1]
      exact Subgroup.mul_mem _ h0 hx
    · have e1 : e p = ⟨dec (l16 H p.1), false⟩ := by simp [e, hb]
      rw [e1]
      exact h0
  have hinj : Set.InjOn e s := by
    intro p hp p' hp' he
    have hq : p.1 < 128 := (hsm p).1 hp
    have hq' : p'.1 < 128 := (hsm p').1 hp'
    have hcode : ∀ {a b : Nat}, a < 128 → b < 128 → dec (l16 H a) = dec (l16 H b) → a = b := by
      intro a b ha hb h
      have h' := M.inj _ (hlt a ha) _ (hlt b hb) h
      rcases Nat.lt_trichotomy a b with h1 | h1 | h1
      · exact absurd h' (Nat.ne_of_lt (hst a ha b hb h1))
      · exact h1
      · exact absurd h' (Nat.ne_of_gt (hst b hb a ha h1))
    obtain ⟨q, b⟩ := p
    obtain ⟨q', b'⟩ := p'
    cases b <;> cases b' <;> simp only [e, CycExt.mk.injEq, Bool.false_eq_true,
      Bool.true_eq_false, if_false, if_true, and_false, and_true, mul_left_inj,
      Prod.mk.injEq] at he ⊢ <;> exact hcode hq hq' he
  have hcardE : (s.image e).card = 256 := by
    rw [Finset.card_image_of_injOn hinj, hscard]
  rintro ⟨hC, hN⟩
  have hsub : (↑(s.image e) : Set (CycExt D')) ⊆ (centralizer {xr} : Subgroup (CycExt D')) := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
    exact hmem p hp
  have hfinC : ((centralizer {xr} : Subgroup (CycExt D')) : Set (CycExt D')).Finite :=
    Set.toFinite _
  have heq : (↑(s.image e) : Set (CycExt D')) = (centralizer {xr} : Subgroup (CycExt D')) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfinC
    have h256 : Nat.card (centralizer {xr} : Subgroup (CycExt D')) = 256 := by
      rw [hC]
      norm_num
    rw [Set.ncard_coe_finset, hcardE, ← Nat.card_coe_set_eq]
    exact h256.le
  have hcount : Nat.card {y : (centralizer {xr} : Subgroup (CycExt D')) // y ^ 2 = 1 ∧ y ≠ 1} =
      ((s.image e).filter fun y => y ^ 2 = 1 ∧ y ≠ 1).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, ?_⟩, invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    · rw [Finset.mem_filter]
      have hm : (y.1.1 : CycExt D') ∈
          ((centralizer {xr} : Subgroup (CycExt D')) : Set (CycExt D')) := y.1.2
      rw [← heq, Finset.mem_coe] at hm
      refine ⟨hm, ?_, ?_⟩
      · have := congrArg Subtype.val y.2.1
        simpa using this
      · intro h1
        exact y.2.2 (Subtype.ext h1)
    · have h := (Finset.mem_filter.1 y.2).1
      have h' : y.1 ∈ ((s.image e : Finset (CycExt D')) : Set (CycExt D')) := Finset.mem_coe.2 h
      rw [heq] at h'
      exact h'
    · have h := (Finset.mem_filter.1 y.2).2
      refine ⟨Subtype.ext (by simpa using h.1), fun h1 => h.2 (congrArg Subtype.val h1)⟩
  rw [hcount, Finset.filter_image, Finset.card_image_of_injOn
    (hinj.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))] at hN
  have hsplit : (s.filter fun p => e p ^ 2 = 1 ∧ e p ≠ 1).card = oNinv mul2 S r H := by
    let A := (Finset.range 128).filter fun q => (!Nat.beq (l16 H q) 0 &&
      Nat.beq (mul2 (l16 H q) (l16 H q)) 0) = true
    let B := (Finset.range 128).filter fun q => bitS S (mul2 (l16 H q) r) = true
    have e1 : s.filter (fun p => e p ^ 2 = 1 ∧ e p ≠ 1) =
        A.image (fun q => (q, false)) ∪ B.image (fun q => (q, true)) := by
      ext ⟨q, b⟩
      rw [Finset.mem_filter, hsm, Finset.mem_union, Finset.mem_image, Finset.mem_image]
      cases b
      · have ee : e (q, false) = ⟨dec (l16 H q), false⟩ := rfl
        rw [ee]
        constructor
        · rintro ⟨hq, h2, h1⟩
          left
          refine ⟨q, Finset.mem_filter.2 ⟨Finset.mem_range.2 hq, ?_⟩, rfl⟩
          change (q, false).1 < 128 at hq
          rw [sq_ext_false, ← M.dec_mul _ (hlt q hq) _ (hlt q hq),
            M.dec_eq_one_iff (M.mul_lt _ (hlt q hq) _ (hlt q hq))] at h2
          have h1' : l16 H q ≠ 0 := by
            intro h0
            apply h1
            rw [h0, M.dec_zero]
            rfl
          have hb0 : Nat.beq (l16 H q) 0 = false := by
            cases h : Nat.beq (l16 H q) 0
            · rfl
            · exact absurd (Nat.eq_of_beq_eq_true h) h1'
          rw [hb0, h2]
          rfl
        · rintro (⟨a, ha, hae⟩ | ⟨a, -, hae⟩)
          · obtain rfl : a = q := (Prod.mk.inj hae).1
            obtain ⟨hq', h⟩ := Finset.mem_filter.1 ha
            have hq := Finset.mem_range.1 hq'
            rw [Bool.and_eq_true, Bool.not_eq_true'] at h
            refine ⟨hq, ?_, ?_⟩
            · rw [sq_ext_false, ← M.dec_mul _ (hlt a hq) _ (hlt a hq),
                Nat.eq_of_beq_eq_true h.2, M.dec_zero]
            · intro h1
              rw [CycExt.one_def, CycExt.mk.injEq] at h1
              have h0 := (M.dec_eq_one_iff (hlt a hq)).1 h1.1
              rw [h0] at h
              exact absurd h.1 (by decide)
          · exact absurd (Prod.mk.inj hae).2 (by decide)
      · have ee : e (q, true) = ⟨dec (l16 H q) * dec r, true⟩ := rfl
        rw [ee]
        constructor
        · rintro ⟨hq, h2, -⟩
          right
          change (q, true).1 < 128 at hq
          refine ⟨q, Finset.mem_filter.2 ⟨Finset.mem_range.2 hq, ?_⟩, rfl⟩
          rw [hS _ (M.mul_lt _ (hlt q hq) _ hr), M.dec_mul _ (hlt q hq) _ hr]
          exact h2
        · rintro (⟨a, -, hae⟩ | ⟨a, ha, hae⟩)
          · exact absurd (Prod.mk.inj hae).2 (by decide)
          · obtain rfl : a = q := (Prod.mk.inj hae).1
            obtain ⟨hq', h⟩ := Finset.mem_filter.1 ha
            have hq := Finset.mem_range.1 hq'
            rw [hS _ (M.mul_lt _ (hlt a hq) _ hr), M.dec_mul _ (hlt a hq) _ hr] at h
            refine ⟨hq, h, fun h1 => ?_⟩
            rw [CycExt.one_def, CycExt.mk.injEq] at h1
            exact absurd h1.2 (by decide)
    have hdis : Disjoint (A.image (fun q => (q, false))) (B.image (fun q => (q, true))) := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨b, -, hb⟩ := Finset.mem_image.1 h2
      exact absurd (Prod.mk.inj hb).2 (by decide)
    rw [e1, Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
      Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), oNinv,
      cntB_eq_card, cntB_eq_card]
    rfl
  rw [hsplit] at hN
  rw [hN] at hn
  exact absurd hn (by decide)

theorem outB_sound (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec) (D' : ExtData Y)
    (hgen : ∀ y : Y, y ∈ Subgroup.closure {z | ∃ i < 4, z = dec (l16 G i)})
    (hG : ∀ i < 4, l16 G i < 16384)
    (hU : ∀ i < 4, l16 U i < 16384 ∧ D'.α (dec (l16 G i)) = dec (l16 U i))
    (hS : ∀ k < 16384, (bitS S k = true ↔ (⟨dec k, true⟩ : CycExt D') ^ 2 = 1))
    (hbc : ∀ k < 16384, D'.α (dec k) = dec (bc k))
    (hC : outB mul2 bc G U S HD LB IL HL = true) :
    ∀ x : CycExt D', x.d = true → ¬ IsPInv x := by
  classical
  obtain ⟨hfin, hcard⟩ := card_ext M D'
  obtain ⟨hUI, hmask, hlab, hrep⟩ := outB_parts hC
  have hinv : ∀ i < 4, dec (l16 HD i) = (D'.α (dec (l16 G i)))⁻¹ := by
    intro i hi
    rw [(hU i hi).2]
    exact M.dec_inv (hU i hi).1 (hUI i hi).1 (hUI i hi).2
  let P : Nat → Nat → Prop := fun l k => k < 16384 ∧ bitS S k = true ∧ l8 LB k = l
  have hentry : ∀ l k, P l k → l < l16 HD 4 ∧ ∃ q < oLen HD l, l16 IL (oSt HD l + q) = k := by
    rintro l k ⟨-, hb, hl⟩
    rw [← hmask] at hb
    obtain ⟨l', hl', q, hq, e⟩ := oMaskAll_mem _ hb
    have h := (oEnt_parts ((oLab_parts (hlab l' hl')).2.2 q hq)).2.1
    rw [e, hl] at h
    subst h
    exact ⟨hl', q, hq, e⟩
  have hPc : ∀ l k, P l k → ∀ i < 4, P l (oConj mul2 G HD k i) ∧
      dec (oConj mul2 G HD k i) = dec (l16 G i) * dec k * (D'.α (dec (l16 G i)))⁻¹ := by
    intro l k hP i hi
    obtain ⟨hl, q, hq, e⟩ := hentry l k hP
    have hE := oEnt_parts ((oLab_parts (hlab l hl)).2.2 q hq)
    rw [e] at hE
    have h1 := M.mul_lt _ (hG i hi) _ hP.1
    have hlt : oConj mul2 G HD k i < 16384 := M.mul_lt _ h1 _ (hUI i hi).1
    have hdec : dec (oConj mul2 G HD k i) =
        dec (l16 G i) * dec k * (D'.α (dec (l16 G i)))⁻¹ := by
      rw [oConj, M.dec_mul _ h1 _ (hUI i hi).1, M.dec_mul _ (hG i hi) _ hP.1, hinv i hi]
    refine ⟨⟨hlt, ?_, hE.2.2 i hi⟩, hdec⟩
    rw [hS _ hlt, hdec, ← conj_out, conj_pow, (hS _ hP.1).1 hP.2.1, mul_one, mul_inv_cancel]
  let E : Nat → Set (CycExt D') := fun l => {y | ∃ k, P l k ∧ y = ⟨dec k, true⟩}
  have hEfin : ∀ l, (E l).Finite := fun l => Set.toFinite _
  have hcl : ∀ l, ∀ h : Y, ∀ y ∈ E l,
      (⟨h, false⟩ : CycExt D') * y * (⟨h, false⟩ : CycExt D')⁻¹ ∈ E l := by
    intro l h
    have hh := hgen h
    induction hh using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      rintro y ⟨k, hP, rfl⟩
      exact ⟨_, (hPc l k hP i hi).1, by rw [conj_out, (hPc l k hP i hi).2]⟩
    | one =>
      intro y hy
      rw [← CycExt.one_def, one_mul, inv_one, mul_one]
      exact hy
    | mul a b _ _ ha hb =>
      intro y hy
      have e : (⟨a * b, false⟩ : CycExt D') = ⟨a, false⟩ * ⟨b, false⟩ := by
        rw [CycExt.mk_mul_mk]
        simp [CycExt.pw, CycExt.sq]
      rw [e, mul_inv_rev]
      have h := ha _ (hb y hy)
      simpa only [mul_assoc] using h
    | inv a _ ha =>
      intro y hy
      have hmaps : Set.MapsTo
          (fun z => (⟨a, false⟩ : CycExt D') * z * (⟨a, false⟩ : CycExt D')⁻¹) (E l) (E l) :=
        fun z hz => ha z hz
      have hinj : Set.InjOn
          (fun z => (⟨a, false⟩ : CycExt D') * z * (⟨a, false⟩ : CycExt D')⁻¹) (E l) :=
        fun z _ w _ h => by simpa using h
      obtain ⟨z, hz, hzy⟩ := (((hEfin l).injOn_iff_bijOn_of_mapsTo hmaps).1 hinj).surjOn hy
      have e : (⟨a⁻¹, false⟩ : CycExt D') = (⟨a, false⟩ : CycExt D')⁻¹ :=
        (CycExt.inv_mk_false D' a).symm
      rw [e, inv_inv, ← hzy]
      simpa [mul_assoc] using hz
  rintro x hxd ⟨hx2, -, hPC⟩
  have ex : x = ⟨x.k, true⟩ := by
    obtain ⟨k, d⟩ := x
    simp only at hxd
    rw [hxd]
  obtain ⟨c, hc, hcx⟩ := M.surj x.k (Subgroup.mem_top _)
  have hx : x = ⟨dec c, true⟩ := by rw [hcx]; exact ex
  have hPc0 : P (l8 LB c) c := ⟨hc, (hS c hc).2 (by rw [← hx]; exact hx2), rfl⟩
  have hcls : MulAction.orbit (ConjAct (CycExt D')) x ⊆ E (l8 LB c) := by
    rintro _ ⟨g, rfl⟩
    change ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹ ∈ E (l8 LB c)
    generalize ConjAct.ofConjAct g = a
    have hxE : x ∈ E (l8 LB c) := ⟨c, hPc0, hx⟩
    obtain ⟨ak, ad⟩ := a
    cases ad
    · exact hcl _ ak x hxE
    · have hb : (⟨ak, true⟩ : CycExt D') * x⁻¹ = ⟨(⟨ak, true⟩ * x⁻¹ : CycExt D').k, false⟩ := by
        rw [hx, CycExt.inv_mk_true, CycExt.mk_mul_mk]
        rfl
      have e : (⟨ak, true⟩ : CycExt D') * x * (⟨ak, true⟩ : CycExt D')⁻¹ =
          ((⟨ak, true⟩ : CycExt D') * x⁻¹) * x * ((⟨ak, true⟩ : CycExt D') * x⁻¹)⁻¹ := by
        group
      rw [e, hb]
      exact hcl _ _ x hxE
  have hO := card_cent_mul x
  rw [hPC.1, hcard] at hO
  have hO128 : Nat.card (MulAction.orbit (ConjAct (CycExt D')) x) = 128 := by
    have h256 : (2 : Nat) ^ 8 = 256 := by norm_num
    rw [h256] at hO
    omega
  obtain ⟨hl, -⟩ := hentry _ c hPc0
  obtain ⟨hlen, hslot, hents⟩ := oLab_parts (hlab _ hl)
  let F : Finset (CycExt D') := (Finset.range (oLen HD (l8 LB c))).image
    fun q => ⟨dec (l16 IL (oSt HD (l8 LB c) + q)), true⟩
  have hEF : E (l8 LB c) ⊆ ↑F := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨-, q, hq, e⟩ := hentry _ k hk
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨q, Finset.mem_range.2 hq, by rw [e]⟩)
  have hOF := hcls.trans hEF
  have hFc : F.card ≤ oLen HD (l8 LB c) := Finset.card_image_le.trans (by simp)
  have hOn : (MulAction.orbit (ConjAct (CycExt D')) x).ncard = 128 := by
    rw [← Nat.card_coe_set_eq]
    exact hO128
  have hle : 128 ≤ oLen HD (l8 LB c) := by
    have h := Set.ncard_le_ncard hOF (Finset.finite_toSet F)
    rw [Set.ncard_coe_finset, hOn] at h
    exact h.trans hFc
  have h128 : oLen HD (l8 LB c) = 128 := le_antisymm hlen hle
  obtain ⟨m, hm, hml⟩ := hslot h128
  have hR := hrep m hm (by rw [hml]; exact hl)
  rw [hml] at hR
  have hr : l16 IL (oSt HD (l8 LB c) + 0) < 16384 :=
    (oEnt_parts (hents 0 (by omega))).1
  have hOeq : MulAction.orbit (ConjAct (CycExt D')) x = ↑F := by
    refine Set.eq_of_subset_of_ncard_le hOF ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hOn]
    exact hFc.trans h128.le
  have hrO : (⟨dec (l16 IL (oSt HD (l8 LB c) + 0)), true⟩ : CycExt D') ∈
      MulAction.orbit (ConjAct (CycExt D')) x := by
    rw [hOeq]
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), rfl⟩)
  obtain ⟨g, hg⟩ := hrO
  have hg' : ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹ =
      ⟨dec (l16 IL (oSt HD (l8 LB c) + 0)), true⟩ := by
    rw [← ConjAct.smul_def]
    exact hg
  have hP' := pinv_of_mulEquiv (centConj (ConjAct.ofConjAct g) x) hPC
  rw [hg'] at hP'
  exact oRep_sound M D' hS hbc hr hR hP'

end Certificates.KernelTower
