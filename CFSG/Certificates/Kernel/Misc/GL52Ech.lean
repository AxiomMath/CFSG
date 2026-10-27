module

public import Certificates.Data.Kernel.Misc.GL52Mat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.KC.Misc.GLM.Ech

open CFSG.KC.Misc.GLM Module

theorem bitK_testBit (x i : Nat) : bitK x i = x.testBit i := by
  have e : Nat.land (Nat.shiftRight x i) 1 = x / 2 ^ i % 2 := by
    change (x >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold bitK
  change Nat.beq (Nat.land (Nat.shiftRight x i) 1) 1 = _
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> rw [h] <;> rfl

@[expose] def bvo (n o r : ℕ) : Fin n → ZMod 2 := fun p => if r.testBit (p + o) then 1 else 0

theorem xor_testBit (r s u : ℕ) : (Nat.xor r s).testBit u = (r.testBit u ^^ s.testBit u) :=
  Nat.testBit_xor r s u

theorem bvo_xor (n o r s : ℕ) : bvo n o (Nat.xor r s) = bvo n o r + bvo n o s := by
  funext p
  change (if (Nat.xor r s).testBit (p + o) then (1 : ZMod 2) else 0) =
    (if r.testBit (p + o) then 1 else 0) + (if s.testBit (p + o) then 1 else 0)
  rw [xor_testBit]
  cases r.testBit (p + o) <;> cases s.testBit (p + o) <;> decide

theorem bvo_eq_zero {n o r : ℕ} (h : ∀ v, o ≤ v → r.testBit v = false) : bvo n o r = 0 := by
  funext p
  change (if r.testBit (p + o) then (1 : ZMod 2) else 0) = 0
  rw [h _ (by omega)]
  rfl

theorem bvo_zero (n o : ℕ) : bvo n o 0 = 0 := bvo_eq_zero fun v _ => Nat.zero_testBit v

@[expose] def XC (Q : ℕ → Prop) : Prop := ∀ r s, Q r → Q s → Q (Nat.xor r s)

@[expose] noncomputable def sp (n o : ℕ) (L : List ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ x ∈ L, bvo n o x = v}

theorem sp_nil (n o : ℕ) : sp n o [] = ⊥ := by
  simp [sp]

theorem sp_cons (n o x : ℕ) (L : List ℕ) :
    sp n o (x :: L) = Submodule.span (ZMod 2) {bvo n o x} ⊔ sp n o L := by
  unfold sp
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp only [List.mem_cons, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | hy, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨y, hy, rfl⟩
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact ⟨x, Or.inl rfl, rfl⟩
    · exact ⟨y, Or.inr hy, rfl⟩

theorem span_zero_bvo {n o r : ℕ} (h : bvo n o r = 0) : Submodule.span (ZMod 2) {bvo n o r} = ⊥ := by
  rw [h, Submodule.span_singleton_eq_bot]

theorem sup_span_add {n : ℕ} (X : Submodule (ZMod 2) (Fin n → ZMod 2)) (a b : Fin n → ZMod 2) :
    Submodule.span (ZMod 2) {a} ⊔ X ⊔ Submodule.span (ZMod 2) {b + a} =
      Submodule.span (ZMod 2) {a} ⊔ X ⊔ Submodule.span (ZMod 2) {b} := by
  have ha : ∀ Y : Submodule (ZMod 2) (Fin n → ZMod 2), a ∈ Submodule.span (ZMod 2) {a} ⊔ X ⊔ Y :=
    fun Y => Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self a))
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b))
      (ha _)
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    intro x hx
    rw [Set.mem_singleton_iff.1 hx, SetLike.mem_coe]
    have key : (b + a) - a ∈ Submodule.span (ZMod 2) {a} ⊔ X ⊔ Submodule.span (ZMod 2) {b + a} :=
      Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self (b + a)))
        (ha _)
    rwa [add_sub_cancel_right] at key

theorem add_self' {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  funext p
  change v p + v p = 0
  generalize v p = x
  revert x
  decide

@[expose] def Low (u r : ℕ) : Prop := ∀ v, u < v → r.testBit v = false

@[expose] def SlotOK (o t s : ℕ) : Prop := s = 0 ∨ (s.testBit (t + o) = true ∧ Low (t + o) s)

@[expose] def Ech (o : ℕ) : List ℕ → ℕ → Prop
  | [], _ => True
  | s :: S, t => SlotOK o t s ∧ Ech o S (t - 1)

@[expose] def Red (o r : ℕ) : List ℕ → ℕ → Prop
  | [], _ => True
  | s :: S, t => (s ≠ 0 → r.testBit (t + o) = false) ∧ Red o r S (t - 1)

theorem low_xor {u r s : ℕ} (hr : Low u r) (hs : Low u s) : Low u (Nat.xor r s) := by
  intro v hv
  rw [xor_testBit, hr v hv, hs v hv]
  rfl

theorem low_pred {t o r : ℕ} (ht : 1 ≤ t) (h : Low (t + o) r) (hb : r.testBit (t + o) = false) :
    Low (t - 1 + o) r := by
  intro v hv
  rcases Nat.lt_or_ge (t + o) v with h' | h'
  · exact h v h'
  · have e : v = t + o := by omega
    rw [e]
    exact hb

theorem low_top {o r : ℕ} (h : Low (0 + o) r) (hb : r.testBit (0 + o) = false) :
    ∀ v, o ≤ v → r.testBit v = false := by
  intro v hv
  rcases Nat.lt_or_ge o v with h' | h'
  · exact h v (by omega)
  · have e : v = 0 + o := by omega
    rw [e]
    exact hb

theorem beq_false_of_ne' {s : ℕ} (h : s ≠ 0) : Nat.beq s 0 = false := by
  rw [Bool.eq_false_iff]
  exact fun e => h (Nat.eq_of_beq_eq_true e)

theorem insK_cons (o s t r : ℕ) (rest : List ℕ) :
    insK o (s :: rest) t r = Bool.rec (motive := fun _ => List ℕ) (s :: insK o rest (t - 1) r)
      (Bool.rec (motive := fun _ => List ℕ) (s :: insK o rest (t - 1) (Nat.xor r s)) (r :: rest)
        (Nat.beq s 0)) (r.testBit (t + o)) := by
  rw [← bitK_testBit]
  rfl

theorem redK_cons (o s t r : ℕ) (rest : List ℕ) :
    redK o (s :: rest) t r = redK o rest (t - 1) (Bool.rec (motive := fun _ => ℕ) r
      (Bool.rec (motive := fun _ => ℕ) (Nat.xor r s) r (Nat.beq s 0)) (r.testBit (t + o))) := by
  rw [← bitK_testBit]
  rfl

theorem cntNZ_cons (s : ℕ) (L : List ℕ) :
    cntNZ (s :: L) = cntNZ L + if s = 0 then 0 else 1 := by
  change Nat.add (cntNZ L) (Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq s 0)) = _
  by_cases h : s = 0
  · subst h
    rfl
  · rw [beq_false_of_ne' h, if_neg h]
    rfl

theorem ech_below {o t : ℕ} : ∀ (S : List ℕ) (u : ℕ), u < t → Ech o S u →
    ∀ y ∈ S, ∀ v, t + o ≤ v → y.testBit v = false
  | [], _, _, _, y, hy => by simp at hy
  | s :: S, u, hu, hE, y, hy => by
    obtain ⟨hs, hS⟩ := hE
    rcases List.mem_cons.1 hy with rfl | hy
    · intro v hv
      rcases hs with rfl | ⟨-, hl⟩
      · exact Nat.zero_testBit v
      · exact hl v (by omega)
    · exact ech_below S (u - 1) (by omega) hS y hy

theorem insK_spec (n o : ℕ) : ∀ (S : List ℕ) (t r : ℕ), S.length = t + 1 → Ech o S t →
    Low (t + o) r →
    (insK o S t r).length = S.length ∧ Ech o (insK o S t r) t ∧
      sp n o (insK o S t r) = sp n o S ⊔ Submodule.span (ZMod 2) {bvo n o r} ∧
      ∀ Q : ℕ → Prop, XC Q → (∀ s ∈ S, Q s) → Q r → ∀ s ∈ insK o S t r, Q s
  | [], _, _, h, _, _ => by simp at h
  | s :: rest, t, r, hl, hE, hr => by
    obtain ⟨hs, hrest⟩ := hE
    have hlr : rest.length = t := by simpa using hl
    rw [insK_cons]
    cases hb : r.testBit (t + o)
    ·
      change (s :: insK o rest (t - 1) r).length = _ ∧ Ech o (s :: insK o rest (t - 1) r) t ∧
        sp n o (s :: insK o rest (t - 1) r) = _ ∧
        ∀ Q : ℕ → Prop, XC Q → _ → _ → ∀ x ∈ s :: insK o rest (t - 1) r, Q x
      rcases Nat.eq_zero_or_pos t with h0 | ht
      · subst h0
        have hn : rest = [] := List.eq_nil_of_length_eq_zero hlr
        subst hn
        refine ⟨rfl, ⟨hs, trivial⟩, ?_, fun Q _ hS _ x hx => hS x hx⟩
        rw [span_zero_bvo (bvo_eq_zero (low_top hr hb)), sup_bot_eq]
        rfl
      · obtain ⟨h1, h2, h3, h4⟩ :=
          insK_spec n o rest (t - 1) r (by omega) hrest (low_pred ht hr hb)
        refine ⟨by rw [List.length_cons, List.length_cons, h1], ⟨hs, h2⟩, ?_, fun Q hQ hS hQr x hx => ?_⟩
        · rw [sp_cons, h3, sp_cons, sup_assoc]
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hS x (List.mem_cons_self ..)
          · exact h4 Q hQ (fun y hy => hS y (List.mem_cons_of_mem _ hy)) hQr x hx
    · by_cases hs0 : s = 0
      · subst hs0
        change (r :: rest).length = _ ∧ Ech o (r :: rest) t ∧ sp n o (r :: rest) = _ ∧
          ∀ Q : ℕ → Prop, XC Q → _ → _ → ∀ x ∈ r :: rest, Q x
        refine ⟨rfl, ⟨Or.inr ⟨hb, hr⟩, hrest⟩, ?_, fun Q _ hS hQr x hx => ?_⟩
        · rw [sp_cons, sp_cons, span_zero_bvo (bvo_zero n o), bot_sup_eq, sup_comm]
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hQr
          · exact hS x (List.mem_cons_of_mem _ hx)
      · rw [beq_false_of_ne' hs0]
        change (s :: insK o rest (t - 1) (Nat.xor r s)).length = _ ∧
          Ech o (s :: insK o rest (t - 1) (Nat.xor r s)) t ∧
          sp n o (s :: insK o rest (t - 1) (Nat.xor r s)) = _ ∧
          ∀ Q : ℕ → Prop, XC Q → _ → _ → ∀ x ∈ s :: insK o rest (t - 1) (Nat.xor r s), Q x
        obtain ⟨hst, hsl⟩ := hs.resolve_left hs0
        have hxb : (Nat.xor r s).testBit (t + o) = false := by
          rw [xor_testBit, hb, hst]
          rfl
        have hxl : Low (t + o) (Nat.xor r s) := low_xor hr hsl
        rcases Nat.eq_zero_or_pos t with h0 | ht
        · subst h0
          have hn : rest = [] := List.eq_nil_of_length_eq_zero hlr
          subst hn
          have hz : bvo n o (Nat.xor r s) = 0 := bvo_eq_zero (low_top hxl hxb)
          rw [bvo_xor] at hz
          have hrs : bvo n o r = bvo n o s := by
            have e : bvo n o r = bvo n o r + (bvo n o r + bvo n o s) := by rw [hz, add_zero]
            rw [e, ← add_assoc, add_self', zero_add]
          refine ⟨rfl, ⟨hs, trivial⟩, ?_, fun Q _ hS _ x hx => hS x hx⟩
          change sp n o [s] = sp n o [s] ⊔ _
          rw [sp_cons, sp_nil, sup_bot_eq, hrs, sup_idem]
        · obtain ⟨h1, h2, h3, h4⟩ :=
            insK_spec n o rest (t - 1) (Nat.xor r s) (by omega) hrest (low_pred ht hxl hxb)
          refine ⟨by rw [List.length_cons, List.length_cons, h1], ⟨hs, h2⟩, ?_, fun Q hQ hS hQr x hx => ?_⟩
          · rw [sp_cons, h3, sp_cons, bvo_xor, ← sup_assoc, sup_span_add, sup_assoc]
          · have hS' : ∀ y ∈ rest, Q y := fun y hy => hS y (List.mem_cons_of_mem _ hy)
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hS x (List.mem_cons_self ..)
            · exact h4 Q hQ hS' (hQ _ _ hQr (hS s (List.mem_cons_self ..))) x hx

theorem redK_spec (n w o : ℕ) : ∀ (S : List ℕ) (t r : ℕ), S.length = t + 1 → Ech o S t →
    (∀ v, t + o < v → (redK o S t r).testBit v = r.testBit v) ∧ Red o (redK o S t r) S t ∧
      bvo n w (redK o S t r) + bvo n w r ∈ sp n w S ∧
      ∀ Q : ℕ → Prop, XC Q → (∀ s ∈ S, Q s) → Q r → Q (redK o S t r)
  | [], _, _, h, _ => by simp at h
  | s :: rest, t, r, hl, hE => by
    obtain ⟨hs, hrest⟩ := hE
    have hlr : rest.length = t := by simpa using hl
    rw [redK_cons]
    set r1 := Bool.rec (motive := fun _ => ℕ) r
      (Bool.rec (motive := fun _ => ℕ) (Nat.xor r s) r (Nat.beq s 0)) (r.testBit (t + o)) with hr1
    have k1 : (∀ v, t + o < v → r1.testBit v = r.testBit v) ∧
        (s ≠ 0 → r1.testBit (t + o) = false) ∧ (r1 = r ∨ r1 = Nat.xor r s) := by
      cases hb : r.testBit (t + o)
      · have e : r1 = r := by rw [hr1, hb]
        exact ⟨fun v _ => by rw [e], fun _ => by rw [e, hb], Or.inl e⟩
      · by_cases hs0 : s = 0
        · have e : r1 = r := by rw [hr1, hb, hs0]; rfl
          exact ⟨fun v _ => by rw [e], fun h => absurd hs0 h, Or.inl e⟩
        · have e : r1 = Nat.xor r s := by rw [hr1, hb, beq_false_of_ne' hs0]
          obtain ⟨hst, hsl⟩ := hs.resolve_left hs0
          refine ⟨fun v hv => ?_, fun _ => ?_, Or.inr e⟩
          · rw [e, xor_testBit, hsl v hv, Bool.xor_false]
          · rw [e, xor_testBit, hb, hst]
            rfl
    obtain ⟨l1, b1, v1⟩ := k1
    have hv1 : bvo n w r1 + bvo n w r ∈ Submodule.span (ZMod 2) {bvo n w s} := by
      rcases v1 with e | e
      · rw [e, add_self']
        exact Submodule.zero_mem _
      · rw [e, bvo_xor, add_comm (bvo n w r), add_assoc, add_self', add_zero]
        exact Submodule.mem_span_singleton_self _
    have hQ1 : ∀ Q : ℕ → Prop, XC Q → (∀ x ∈ s :: rest, Q x) → Q r → Q r1 := by
      intro Q hQ hS hQr
      rcases v1 with e | e
      · rw [e]
        exact hQr
      · rw [e]
        exact hQ _ _ hQr (hS s (List.mem_cons_self ..))
    rcases Nat.eq_zero_or_pos t with h0 | ht
    · subst h0
      have hn : rest = [] := List.eq_nil_of_length_eq_zero hlr
      subst hn
      change (∀ v, 0 + o < v → r1.testBit v = r.testBit v) ∧ Red o r1 [s] 0 ∧
        bvo n w r1 + bvo n w r ∈ sp n w [s] ∧ _
      refine ⟨l1, ⟨b1, trivial⟩, ?_, hQ1⟩
      rw [sp_cons, sp_nil, sup_bot_eq]
      exact hv1
    · obtain ⟨h1, h2, h3, h4⟩ := redK_spec n w o rest (t - 1) r1 (by omega) hrest
      refine ⟨fun v hv => (h1 v (by omega)).trans (l1 v hv), ⟨fun hs0 => ?_, h2⟩, ?_,
        fun Q hQ hS hQr => h4 Q hQ (fun y hy => hS y (List.mem_cons_of_mem _ hy)) (hQ1 Q hQ hS hQr)⟩
      · rw [h1 (t + o) (by omega)]
        exact b1 hs0
      · have e : bvo n w (redK o rest (t - 1) r1) + bvo n w r =
            (bvo n w (redK o rest (t - 1) r1) + bvo n w r1) + (bvo n w r1 + bvo n w r) := by
          rw [add_assoc, ← add_assoc (bvo n w r1), add_self', zero_add]
        rw [e, sp_cons]
        exact Submodule.add_mem _ (Submodule.mem_sup_right h3) (Submodule.mem_sup_left hv1)

theorem insK_place (o : ℕ) : ∀ (S : List ℕ) (t r : ℕ), S.length = t + 1 → Red o r S t →
    Low (t + o) r → (∃ v, o ≤ v ∧ r.testBit v = true) →
    cntNZ (insK o S t r) = cntNZ S + 1
  | [], _, _, h, _, _, _ => by simp at h
  | s :: rest, t, r, hl, hR, hr, ⟨v, hov, hv⟩ => by
    obtain ⟨hRs, hRrest⟩ := hR
    have hlr : rest.length = t := by simpa using hl
    rw [insK_cons]
    cases hb : r.testBit (t + o)
    · change cntNZ (s :: insK o rest (t - 1) r) = cntNZ (s :: rest) + 1
      have hvt : v < t + o := by
        rcases Nat.lt_or_ge v (t + o) with h | h
        · exact h
        · rcases Nat.lt_or_ge (t + o) v with h' | h'
          · rw [hr v h'] at hv
            exact absurd hv (by decide)
          · have e : v = t + o := by omega
            rw [e, hb] at hv
            exact absurd hv (by decide)
      have ht : 1 ≤ t := by omega
      rw [cntNZ_cons, cntNZ_cons, insK_place o rest (t - 1) r (by omega) hRrest (low_pred ht hr hb)
        ⟨v, hov, hv⟩]
      omega
    · have hs0 : s = 0 := by
        by_contra hs0
        rw [hRs hs0] at hb
        exact absurd hb (by decide)
      subst hs0
      change cntNZ (r :: rest) = cntNZ (0 :: rest) + 1
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [Nat.zero_testBit] at hb
        exact absurd hb (by decide)
      rw [cntNZ_cons, cntNZ_cons, if_neg hr0, if_pos rfl]

theorem finrank_span_sup {n : ℕ} (X : Submodule (ZMod 2) (Fin n → ZMod 2)) {v : Fin n → ZMod 2}
    (hv : v ∉ X) :
    finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {v} ⊔ X) = finrank (ZMod 2) X + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ X.zero_mem)
  have hi : Submodule.span (ZMod 2) {v} ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw1
    rw [Submodule.mem_bot]
    by_contra hc
    have hc0 : c ≠ 0 := fun e => hc (by rw [e, zero_smul])
    apply hv
    have e : v = c⁻¹ • (c • v) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [e]
    exact X.smul_mem _ hw2
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod 2) {v}) X
  have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) = 1 := finrank_span_singleton hv0
  have h2 : finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {v} ⊓ X) = 0 := by
    rw [hi]
    exact finrank_bot _ _
  omega

theorem finrank_ech (n o : ℕ) : ∀ (S : List ℕ) (t : ℕ), t < n → S.length = t + 1 → Ech o S t →
    finrank (ZMod 2) (sp n o S) = cntNZ S
  | [], _, _, h, _ => by simp at h
  | s :: rest, t, htn, hl, hE => by
    obtain ⟨hs, hrest⟩ := hE
    have hlr : rest.length = t := by simpa using hl
    have hrk : finrank (ZMod 2) (sp n o rest) = cntNZ rest := by
      rcases Nat.eq_zero_or_pos t with h0 | ht
      · rw [h0] at hlr
        rw [List.eq_nil_of_length_eq_zero hlr, sp_nil]
        exact (finrank_bot _ _).trans rfl
      · exact finrank_ech n o rest (t - 1) (by omega) (by omega) hrest
    rw [sp_cons, cntNZ_cons, ← hrk]
    by_cases hs0 : s = 0
    · subst hs0
      rw [span_zero_bvo (bvo_zero n o), bot_sup_eq, if_pos rfl, Nat.add_zero]
    · rw [if_neg hs0]
      obtain ⟨hst, -⟩ := hs.resolve_left hs0
      refine finrank_span_sup _ fun hmem => ?_
      have hvan : ∀ w ∈ sp n o rest, w ⟨t, htn⟩ = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨y, hy, rfl⟩ := hx
          have hy0 : y.testBit (t + o) = false := by
            rcases Nat.eq_zero_or_pos t with h0 | ht
            · rw [h0] at hlr
              rw [List.eq_nil_of_length_eq_zero hlr] at hy
              simp at hy
            · exact ech_below (t := t) rest (t - 1) (by omega) hrest y hy (t + o) le_rfl
          change (if y.testBit (t + o) then (1 : ZMod 2) else 0) = 0
          rw [hy0]
          rfl
        | zero => rfl
        | add x y _ _ hx hy => rw [Pi.add_apply, hx, hy, add_zero]
        | smul c x _ hx => rw [Pi.smul_apply, hx, smul_zero]
      have h1 := hvan _ hmem
      change (if s.testBit (t + o) then (1 : ZMod 2) else 0) = 0 at h1
      rw [hst] at h1
      exact absurd h1 (by decide)

noncomputable def rkGo (c k : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) (zerosK 5) (fun i acc => insK 0 acc 4 (rowK c i)) k

theorem rowK_low (c i : ℕ) : Low (4 + 0) (rowK c i) := by
  intro u hu
  apply Nat.testBit_lt_two_pow
  have h1 : rowK c i ≤ 31 := Nat.and_le_right
  have h2 : 2 ^ 5 ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ 5 = 32 := by norm_num
  omega

theorem rkGo_spec (c : ℕ) : ∀ k, (rkGo c k).length = 5 ∧ Ech 0 (rkGo c k) 4 ∧
    sp 5 0 (rkGo c k) = Submodule.span (ZMod 2) {v | ∃ i < k, bvo 5 0 (rowK c i) = v}
  | 0 => by
    refine ⟨rfl, ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, trivial⟩, ?_⟩
    change sp 5 0 [0, 0, 0, 0, 0] = _
    rw [sp_cons, sp_cons, sp_cons, sp_cons, sp_cons, sp_nil, span_zero_bvo (bvo_zero 5 0)]
    simp
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := rkGo_spec c k
    obtain ⟨g1, g2, g3, -⟩ := insK_spec 5 0 (rkGo c k) 4 (rowK c k) h1 h2 (rowK_low c k)
    change (insK 0 (rkGo c k) 4 (rowK c k)).length = 5 ∧ Ech 0 (insK 0 (rkGo c k) 4 (rowK c k)) 4 ∧
      sp 5 0 (insK 0 (rkGo c k) 4 (rowK c k)) = _
    refine ⟨g1.trans h1, g2, ?_⟩
    rw [g3, h3, ← Submodule.span_union]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨k, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr rfl

theorem rankK_rows (c : ℕ) (A : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (h : ∀ i : Fin 5, bvo 5 0 (rowK c i) = A i) : rankK c = A.rank := by
  obtain ⟨h1, h2, h3⟩ := rkGo_spec c 5
  have e : rankK c = cntNZ (rkGo c 5) := rfl
  have hset : {v | ∃ i < 5, bvo 5 0 (rowK c i) = v} = Set.range A := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, (h ⟨i, hi⟩).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.isLt, h i⟩
  rw [e, ← finrank_ech 5 0 _ 4 (by norm_num) h1 h2, h3, hset, Matrix.rank_eq_finrank_span_row]
  rfl

end CFSG.KC.Misc.GLM.Ech

end
