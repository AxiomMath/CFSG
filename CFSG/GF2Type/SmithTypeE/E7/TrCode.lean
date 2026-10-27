module

public import Certificates.Data.SmithD6Tr7
public import CFSG.GF2Type.SmithTypeE.DMod.V12

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 Module

section Generic

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {dec : ℕ → W}
  (hxor : ∀ a b, dec (a ^^^ b) = dec a + dec b)

include hxor in
theorem dec_zero : dec 0 = 0 := by
  have h := hxor 0 0
  rw [Nat.xor_self] at h
  exact left_eq_add.mp h

theorem tr7XorSel_cons (b : ℕ) (bs : List ℕ) (m : ℕ) :
    tr7XorSel (b :: bs) m = (if m % 2 = 1 then b else 0) ^^^ tr7XorSel bs (m / 2) := by
  simp [tr7XorSel]

theorem tr7XorSel_nil (m : ℕ) : tr7XorSel [] m = 0 := rfl

include hxor in
theorem dec_xorSel_mem {U : Submodule (ZMod 2) W} :
    ∀ (bs : List ℕ), (∀ b ∈ bs, dec b ∈ U) → ∀ m, dec (tr7XorSel bs m) ∈ U
  | [], _, _ => by
    rw [tr7XorSel_nil, dec_zero hxor]
    exact U.zero_mem
  | b :: bs, h, m => by
    rw [tr7XorSel_cons, hxor]
    refine U.add_mem ?_ (dec_xorSel_mem bs (fun x hx => h x (List.mem_cons_of_mem _ hx)) _)
    split
    · exact h b (List.mem_cons_self ..)
    · rw [dec_zero hxor]
      exact U.zero_mem

include hxor in
theorem exists_xorSel_of_mem_span :
    ∀ (bs : List ℕ) {v : W}, v ∈ Submodule.span (ZMod 2) {u | ∃ b ∈ bs, u = dec b} →
      ∃ m < 2 ^ bs.length, v = dec (tr7XorSel bs m)
  | [], v, hv => by
    have : {u : W | ∃ b ∈ ([] : List ℕ), u = dec b} = ∅ := by
      ext u
      simp
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hv
    exact ⟨0, by norm_num, by rw [hv, tr7XorSel_nil, dec_zero hxor]⟩
  | b :: bs, v, hv => by
    have e : {u : W | ∃ c ∈ b :: bs, u = dec c} =
        insert (dec b) {u | ∃ c ∈ bs, u = dec c} := by
      ext u
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨c, rfl | hc, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨c, hc, rfl⟩
      · rintro (rfl | ⟨c, hc, rfl⟩)
        · exact ⟨b, Or.inl rfl, rfl⟩
        · exact ⟨c, Or.inr hc, rfl⟩
    rw [e, Submodule.mem_span_insert] at hv
    obtain ⟨a, w, hw, rfl⟩ := hv
    obtain ⟨m, hm, rfl⟩ := exists_xorSel_of_mem_span bs hw
    have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases key a with rfl | rfl
    · refine ⟨2 * m, by rw [List.length_cons, pow_succ]; omega, ?_⟩
      rw [tr7XorSel_cons, hxor, show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega]
      simp [dec_zero hxor]
    · refine ⟨2 * m + 1, by rw [List.length_cons, pow_succ]; omega, ?_⟩
      rw [tr7XorSel_cons, hxor, show (2 * m + 1) / 2 = m by omega,
        show (2 * m + 1) % 2 = 1 by omega]
      simp

theorem finrank_span_le (bs : List ℕ) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {u : W | ∃ b ∈ bs, u = dec b}) ≤ bs.length := by
  have e : {u : W | ∃ b ∈ bs, u = dec b} = Set.range fun j : Fin bs.length => dec bs[j] := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, List.getElem_mem _, rfl⟩
  rw [e]
  exact (finrank_range_le_card _).trans (by simp)

include hxor in
theorem le_finrank_of_indep [Finite W] {w : ℕ}
    (hinj : ∀ a b : ℕ, a < 2 ^ w → b < 2 ^ w → dec a = dec b → a = b)
    {U : Submodule (ZMod 2) W} {bs : List ℕ} (hlt : ∀ b ∈ bs, b < 2 ^ w)
    (hbs : ∀ b ∈ bs, dec b ∈ U) (h : tr7IndepOK bs = true) :
    bs.length ≤ finrank (ZMod 2) U := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  have hsel : ∀ (bs : List ℕ), (∀ b ∈ bs, b < 2 ^ w) → ∀ m, tr7XorSel bs m < 2 ^ w := by
    intro bs
    induction bs with
    | nil => intro _ m; rw [tr7XorSel_nil]; exact Nat.two_pow_pos w
    | cons b bs ih =>
      intro hb m
      rw [tr7XorSel_cons]
      refine Nat.xor_lt_two_pow ?_ (ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)) _)
      split
      · exact hb b (List.mem_cons_self ..)
      · exact Nat.two_pow_pos w
  let f : Fin (2 ^ bs.length) → U := fun m => ⟨dec (tr7XorSel bs m.val),
    dec_xorSel_mem hxor bs hbs _⟩
  have hf : Function.Injective f := by
    intro m m' hmm
    have e : dec (tr7XorSel bs m.val) = dec (tr7XorSel bs m'.val) := congrArg Subtype.val hmm
    have e' := hinj _ _ (hsel bs hlt m.val) (hsel bs hlt m'.val) e
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 h m.val (List.mem_range.2 m.2)) m'.val
      (List.mem_range.2 m'.2)
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
    rcases h1 with h1 | h1
    · exact Fin.ext h1
    · exact absurd e' h1
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, Nat.card_eq_fintype_card (α := U), Module.card_eq_pow_finrank (K := ZMod 2),
    ZMod.card] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hc

include hxor in
theorem dec_red_mem {U : Submodule (ZMod 2) W} :
    ∀ (E : List (ℕ × ℕ)) (x : ℕ), (∀ e ∈ E, dec e.2 ∈ U) → dec (tr7Red E x) ∈ U → dec x ∈ U
  | [], x, _, h => by simpa [tr7Red] using h
  | e :: E, x, hE, h => by
    have hE' : ∀ e' ∈ E, dec e'.2 ∈ U := fun e' he' => hE e' (List.mem_cons_of_mem _ he')
    have h' : dec (tr7Red E (if x.testBit e.1 then x ^^^ e.2 else x)) ∈ U := by
      simpa [tr7Red] using h
    have h2 := dec_red_mem E _ hE' h'
    by_cases hb : x.testBit e.1
    · rw [if_pos hb] at h2
      have : dec x = dec (x ^^^ e.2) + dec e.2 := by
        rw [hxor x e.2, add_assoc, ← hxor e.2 e.2, Nat.xor_self, dec_zero hxor, add_zero]
      rw [this]
      exact U.add_mem h2 (hE e (List.mem_cons_self ..))
    · rw [if_neg hb] at h2
      exact h2

include hxor in
theorem dec_red_mem' {U : Submodule (ZMod 2) W} :
    ∀ (E : List (ℕ × ℕ)) (x : ℕ), (∀ e ∈ E, dec e.2 ∈ U) → dec x ∈ U → dec (tr7Red E x) ∈ U
  | [], x, _, h => by simpa [tr7Red] using h
  | e :: E, x, hE, h => by
    have hE' : ∀ e' ∈ E, dec e'.2 ∈ U := fun e' he' => hE e' (List.mem_cons_of_mem _ he')
    have h1 : dec (if x.testBit e.1 then x ^^^ e.2 else x) ∈ U := by
      split
      · rw [hxor]
        exact U.add_mem h (hE e (List.mem_cons_self ..))
      · exact h
    have h2 := dec_red_mem' E _ hE' h1
    simpa [tr7Red] using h2

include hxor in
theorem dec_ech_mem {U : Submodule (ZMod 2) W} (vs : List ℕ) (hvs : ∀ v ∈ vs, dec v ∈ U) :
    ∀ e ∈ tr7Ech vs, dec e.2 ∈ U := by
  have key : ∀ (vs : List ℕ) (acc : List (ℕ × ℕ)), (∀ e ∈ acc, dec e.2 ∈ U) →
      (∀ v ∈ vs, dec v ∈ U) → ∀ e ∈ vs.foldl (fun E v =>
        let r := tr7Red E v; if r == 0 then E else E ++ [(r.log2, r)]) acc, dec e.2 ∈ U := by
    intro vs
    induction vs with
    | nil => intro acc hacc _ e he; exact hacc e he
    | cons v vs ih =>
      intro acc hacc hvs e he
      simp only [List.foldl_cons] at he
      refine ih _ ?_ (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) e he
      intro e' he'
      split at he'
      · exact hacc e' he'
      · rw [List.mem_append, List.mem_singleton] at he'
        rcases he' with he' | rfl
        · exact hacc e' he'
        · exact dec_red_mem' hxor acc v hacc (hvs v (List.mem_cons_self ..))
  exact key vs [] (by simp) hvs

end Generic

theorem dec12_inj : ∀ a b : ℕ, a < 2 ^ 12 → b < 2 ^ 12 →
    CFSG.GF2Type.SmithTypeE.DMod.dec12 a = CFSG.GF2Type.SmithTypeE.DMod.dec12 b → a = b :=
  fun _ _ ha hb h => CFSG.GF2Type.SmithTypeE.DMod.eq_of_dec12_eq (by simpa using ha)
    (by simpa using hb) h

theorem decode32_inj : ∀ a b : ℕ, a < 2 ^ 32 → b < 2 ^ 32 →
    CFSG.GF2Type.SmithTypeE.DMod.decode32 a = CFSG.GF2Type.SmithTypeE.DMod.decode32 b → a = b :=
  fun _ _ ha hb h => CFSG.GF2Type.SmithTypeE.DMod.eq_of_decode32_eq ha hb h

end CFSG.GF2Type.SmithTypeE.E7
