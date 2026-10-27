module

public import CFSG.GF2Type.SmithTypeE.L6.TrCode
public import CFSG.GF2Type.SmithTypeE.LMod.Tv
public import CFSG.GF2Type.SmithTypeE.LMod.Points

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Module CFSG.SmithL6 Matrix CFSG.GF2Type.SmithTypeE.LMod
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor decode_zero)

@[expose] def SelIndep (vs : List ℕ) : Prop := ∀ m, 0 < m → m < 2 ^ vs.length → trXorSel vs m ≠ 0

theorem div_two_xor (m m' : ℕ) : (m ^^^ m') / 2 = m / 2 ^^^ m' / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, ← Nat.testBit_succ, ← Nat.testBit_succ, ← Nat.testBit_succ, Nat.testBit_xor]

theorem mod_two_xor (m m' : ℕ) :
    decide ((m ^^^ m') % 2 = 1) = (decide (m % 2 = 1) ^^ decide (m' % 2 = 1)) := by
  rw [← Nat.testBit_zero, ← Nat.testBit_zero, ← Nat.testBit_zero, Nat.testBit_xor]

theorem ite_xor_mod (m m' b : ℕ) : (if (m ^^^ m') % 2 = 1 then b else 0) =
    (if m % 2 = 1 then b else 0) ^^^ (if m' % 2 = 1 then b else 0) := by
  have h' := mod_two_xor m m'
  by_cases ha : m % 2 = 1 <;> by_cases hb : m' % 2 = 1
  · rw [decide_eq_true ha, decide_eq_true hb] at h'
    rw [if_neg (of_decide_eq_false h'), if_pos ha, if_pos hb, Nat.xor_self]
  · rw [decide_eq_true ha, decide_eq_false hb] at h'
    rw [if_pos (of_decide_eq_true h'), if_pos ha, if_neg hb, Nat.xor_zero]
  · rw [decide_eq_false ha, decide_eq_true hb] at h'
    rw [if_pos (of_decide_eq_true h'), if_neg ha, if_pos hb, Nat.zero_xor]
  · rw [decide_eq_false ha, decide_eq_false hb] at h'
    rw [if_neg (of_decide_eq_false h'), if_neg ha, if_neg hb, Nat.xor_zero]

theorem xor_four (a b c d : ℕ) : a ^^^ b ^^^ (c ^^^ d) = a ^^^ c ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

theorem trXorSel_xor : ∀ (vs : List ℕ) (m m' : ℕ),
    trXorSel vs (m ^^^ m') = trXorSel vs m ^^^ trXorSel vs m'
  | [], _, _ => by
    change (0 : ℕ) = 0 ^^^ 0
    exact (Nat.xor_self 0).symm
  | b :: bs, m, m' => by
    rw [trXorSel_cons, trXorSel_cons, trXorSel_cons, div_two_xor, trXorSel_xor bs, ite_xor_mod,
      xor_four]

theorem trXorSel_lt {vs : List ℕ} {n : ℕ} (h : ∀ v ∈ vs, v < 2 ^ n) : ∀ m, trXorSel vs m < 2 ^ n := by
  induction vs with
  | nil => intro m; exact Nat.two_pow_pos n
  | cons b bs ih =>
    intro m
    rw [trXorSel_cons]
    refine Nat.xor_lt_two_pow ?_ (ih (fun v hv => h v (List.mem_cons_of_mem _ hv)) _)
    split
    · exact h b (List.mem_cons_self ..)
    · exact Nat.two_pow_pos n

theorem eq_of_xor_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e := congrArg (fun n => n.testBit i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at e
  revert e
  cases a.testBit i <;> cases b.testBit i <;> simp

theorem trXorSel_inj {vs : List ℕ} (h : SelIndep vs) {m m' : ℕ} (hm : m < 2 ^ vs.length)
    (hm' : m' < 2 ^ vs.length) (he : trXorSel vs m = trXorSel vs m') : m = m' := by
  by_contra hne
  have hx : 0 < m ^^^ m' := Nat.pos_of_ne_zero fun h0 => hne (eq_of_xor_zero h0)
  refine h _ hx (Nat.xor_lt_two_pow hm hm') ?_
  rw [trXorSel_xor, he, Nat.xor_self]

theorem le_finrank_of_selIndep {U : Submodule (ZMod 2) V} {vs : List ℕ}
    (hbs : ∀ b ∈ vs, decode b ∈ U) (hlt : ∀ b ∈ vs, b < 2 ^ 20) (h : SelIndep vs) :
    vs.length ≤ finrank (ZMod 2) U := by
  classical
  let f : Fin (2 ^ vs.length) → U := fun m => ⟨decode (trXorSel vs m.val),
    decode_trXorSel_mem vs hbs _⟩
  have hf : Function.Injective f := by
    intro m m' hmm
    have e : decode (trXorSel vs m.val) = decode (trXorSel vs m'.val) := congrArg Subtype.val hmm
    have e' := mod_eq_of_decode_eq e
    rw [Nat.mod_eq_of_lt (trXorSel_lt hlt _), Nat.mod_eq_of_lt (trXorSel_lt hlt _)] at e'
    exact Fin.ext (trXorSel_inj h m.2 m'.2 e')
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, Nat.card_eq_fintype_card (α := U), Module.card_eq_pow_finrank (K := ZMod 2),
    ZMod.card] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hc

theorem dec6_trXorSel (vs : List ℕ) : ∀ m, dec6 (trXorSel vs m) ∈
    Submodule.span (ZMod 2) {u | ∃ b ∈ vs, u = dec6 b} := by
  induction vs with
  | nil => intro m; rw [show trXorSel [] m = 0 from rfl, dec6_zero]; exact Submodule.zero_mem _
  | cons b bs ih =>
    intro m
    rw [trXorSel_cons, dec6_xor]
    refine Submodule.add_mem _ ?_ (Submodule.span_mono (fun u hu => by
      obtain ⟨c, hc, rfl⟩ := hu
      exact ⟨c, List.mem_cons_of_mem _ hc, rfl⟩) (ih _))
    split
    · exact Submodule.subset_span ⟨b, List.mem_cons_self .., rfl⟩
    · rw [dec6_zero]
      exact Submodule.zero_mem _

theorem span_dec6_eq_top {vs : List ℕ} (hl : vs.length = 6) (hlt : ∀ b ∈ vs, b < 64)
    (h : SelIndep vs) : Submodule.span (ZMod 2) {u | ∃ b ∈ vs, u = dec6 b} = ⊤ := by
  classical
  let S := Submodule.span (ZMod 2) {u : Fin 6 → ZMod 2 | ∃ b ∈ vs, u = dec6 b}
  let f : Fin 64 → S := fun m => ⟨dec6 (trXorSel vs m.val), dec6_trXorSel vs _⟩
  have hlt' : ∀ b ∈ vs, b < 2 ^ 6 := hlt
  have hf : Function.Injective f := by
    intro m m' hmm
    have e : dec6 (trXorSel vs m.val) = dec6 (trXorSel vs m'.val) := congrArg Subtype.val hmm
    have e' := dec6_inj (trXorSel_lt hlt' _) (trXorSel_lt hlt' _) e
    exact Fin.ext (trXorSel_inj h (by rw [hl]; exact m.2) (by rw [hl]; exact m'.2) e')
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, Nat.card_eq_fintype_card (α := S), Module.card_eq_pow_finrank (K := ZMod 2),
    ZMod.card] at hc
  have h2 : 6 ≤ finrank (ZMod 2) S := by
    have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [h64] at hc
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hc
  have h1 : finrank (ZMod 2) S ≤ 6 := by
    have := Submodule.finrank_le S
    simpa using this
  apply Submodule.eq_top_of_finrank_eq
  change finrank (ZMod 2) S = _
  simp only [Module.finrank_fin_fun]
  omega

theorem eq_one_of_selIndep {B : Matrix (Fin 6) (Fin 6) (ZMod 2)} {vs : List ℕ}
    (hl : vs.length = 6) (hlt : ∀ b ∈ vs, b < 64) (h : SelIndep vs)
    (hfix : ∀ b ∈ vs, B *ᵥ dec6 b = dec6 b) : B = 1 := by
  have key : ∀ u ∈ Submodule.span (ZMod 2) {u | ∃ b ∈ vs, u = dec6 b}, B *ᵥ u = u := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      exact hfix b hb
    | zero => exact mulVec_zero B
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
    | smul a x _ hx => rw [mulVec_smul, hx]
  rw [span_dec6_eq_top hl hlt h] at key
  ext i j
  have e := congrFun (key (Pi.single j 1) Submodule.mem_top) i
  rw [mulVec_single_one] at e
  rw [col_apply, Pi.single_apply] at e
  rw [e, one_apply]

end CFSG.GF2Type.SmithTypeE.L6
