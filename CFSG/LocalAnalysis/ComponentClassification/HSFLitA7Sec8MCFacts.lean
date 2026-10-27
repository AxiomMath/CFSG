module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MC

public section

namespace CFSG.ComponentClassification.HSFLit.Sec8

namespace MC

@[expose] def bit (x : MC) (i : ℕ) : Bool := (tget nfTab 8 (16 * x.g.val + x.a.val)).testBit i

@[expose] def cj (h x : MC) : MC := h * x * h⁻¹

@[expose] def ccount (x : MC) : ℕ := (Finset.univ.filter fun g : MC => g * x = x * g).card

@[expose] def inQ0 (x : MC) : Bool := !bit x 1 && !bit x 3 && !bit x 6

@[expose] def inF1 (x : MC) : Bool := !bit x 0 && !bit x 1 && !bit x 2 && !bit x 6

@[expose] def inF2 (x : MC) : Bool := !bit x 0 && !bit x 3 && !bit x 5 && (bit x 1 == bit x 6)

@[expose] def inE2 (x : MC) : Bool := !bit x 0 && !bit x 2 && !bit x 3 && !bit x 5

@[expose] def inE4 (x : MC) : Bool := !bit x 0 && !bit x 5 && !bit x 6 && (bit x 1 == bit x 3)

@[expose] def inM (x : MC) : Bool := bit x 1 == bit x 6

@[expose] def ofPred (p : MC → Bool) (h1 : p 1 = true)
    (hmul : ∀ x, p x = true → ∀ y, p y = true → p (x * y) = true)
    (hinv : ∀ x, p x = true → p x⁻¹ = true) : Subgroup MC where
  carrier := {x | p x = true}
  mul_mem' {a b} ha hb := hmul a ha b hb
  one_mem' := h1
  inv_mem' {a} ha := hinv a ha

theorem card_ofPred (p : MC → Bool) (h1 : p 1 = true)
    (hmul : ∀ x, p x = true → ∀ y, p y = true → p (x * y) = true)
    (hinv : ∀ x, p x = true → p x⁻¹ = true) :
    Nat.card (ofPred p h1 hmul hinv) = (Finset.univ.filter fun x => p x = true).card := by
  rw [show Nat.card (ofPred p h1 hmul hinv) = Nat.card {x : MC // p x = true} from rfl,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

@[expose] def E4 : Subgroup MC := ofPred inE4 (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem card_E4 : Nat.card E4 = 16 := by
  rw [E4, card_ofPred]; decide +kernel

@[expose] def M : Subgroup MC := ofPred inM (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem card_M : Nat.card M = 128 := by
  rw [M, card_ofPred]; decide +kernel

theorem Q0_span : ∀ x : MC, inQ0 x = true → InSpan [w₂, w₁, z, y, k] x := by decide +kernel

theorem F1_span : ∀ x : MC, inF1 x = true → InSpan [v, z, y, k] x := by decide +kernel

theorem F2_span : ∀ x : MC, inF2 x = true → InSpan [w₁, z, k, t * u] x := by decide +kernel

theorem E2_span : ∀ x : MC, inE2 x = true → InSpan [u, z, t, k] x := by decide +kernel

theorem E4_span : ∀ x : MC, inE4 x = true → InSpan [z, k, w₁, u * v] x := by decide +kernel

theorem M_fact : ∀ x : MC, inM x = true → x * x = 1 → x ≠ 1 →
    inQ0 x = true ∨ inF1 x = true ∨ inF2 x = true ∨ 32 < ccount x := by decide +kernel

@[expose] def sylCands : List MC :=
  [⟨4, 0⟩, ⟨12, 0⟩, ⟨6, 0⟩, ⟨14, 0⟩, ⟨5, 0⟩, ⟨13, 0⟩, ⟨7, 0⟩, ⟨15, 0⟩, ⟨0, 2⟩, ⟨8, 2⟩, ⟨1, 2⟩,
    ⟨9, 2⟩, ⟨0, 10⟩, ⟨8, 10⟩, ⟨1, 10⟩, ⟨9, 10⟩, ⟨11, 6⟩, ⟨3, 6⟩, ⟨10, 6⟩, ⟨2, 6⟩, ⟨0, 14⟩,
    ⟨8, 14⟩, ⟨1, 14⟩, ⟨9, 14⟩, ⟨15, 9⟩, ⟨7, 9⟩, ⟨13, 9⟩, ⟨5, 9⟩, ⟨7, 13⟩, ⟨15, 13⟩, ⟨4, 13⟩,
    ⟨12, 13⟩]

theorem syl_cands : ∀ x : MC, x * x = 1 → x ≠ 1 → inQ0 x = false → inF1 x = false →
    inF2 x = false → ccount x ≤ 32 → x ∈ sylCands := by decide +kernel

theorem syl_cert (x : MC) (hx : x ∈ sylCands) :
    (∃ h₀ h₁ : MC, cj h₀ x * cj h₁ x ≠ cj h₁ x * cj h₀ x) ∨
      (∃ h₀ h₁ h₂ h₃ : MC, ∀ e ∈ [z, y, t, k],
        InSpan [cj h₀ x, cj h₁ x, cj h₂ x, cj h₃ x] e) ∨
      (∃ h₀ h₁ h₂ h₃ : MC, ∀ e ∈ [z, k, w₁, u * v],
        InSpan [cj h₀ x, cj h₁ x, cj h₂ x, cj h₃ x] e) := by
  simp only [sylCands, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨⟨0, 0⟩, ⟨0, 8⟩, ⟨0, 9⟩, ⟨0, 12⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inl ⟨⟨0, 8⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 4⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inl ⟨⟨0, 9⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 5⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inl ⟨⟨0, 1⟩, ⟨0, 9⟩, ⟨0, 8⟩, ⟨0, 13⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inl ⟨⟨0, 12⟩, ⟨0, 4⟩, ⟨0, 5⟩, ⟨0, 0⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inl ⟨⟨0, 4⟩, ⟨0, 12⟩, ⟨0, 13⟩, ⟨0, 8⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inl ⟨⟨0, 13⟩, ⟨0, 5⟩, ⟨0, 4⟩, ⟨0, 1⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inl ⟨⟨0, 5⟩, ⟨0, 13⟩, ⟨0, 12⟩, ⟨0, 9⟩,
      by decide +kernel⟩)
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 1⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 1⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 1⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 1⟩, by decide +kernel⟩
  · exact Or.inr (Or.inr ⟨⟨0, 0⟩, ⟨4, 0⟩, ⟨2, 0⟩, ⟨14, 1⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inr ⟨⟨4, 0⟩, ⟨0, 0⟩, ⟨6, 0⟩, ⟨0, 1⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inr ⟨⟨2, 0⟩, ⟨6, 0⟩, ⟨0, 0⟩, ⟨12, 1⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inr ⟨⟨6, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨2, 1⟩,
      by decide +kernel⟩)
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 1⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 1⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 1⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 1⟩, by decide +kernel⟩
  · exact Or.inr (Or.inr ⟨⟨12, 1⟩, ⟨0, 1⟩, ⟨14, 1⟩, ⟨0, 0⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inr ⟨⟨0, 1⟩, ⟨12, 1⟩, ⟨2, 1⟩, ⟨6, 0⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inr ⟨⟨2, 1⟩, ⟨14, 1⟩, ⟨0, 1⟩, ⟨4, 0⟩,
      by decide +kernel⟩)
  · exact Or.inr (Or.inr ⟨⟨14, 1⟩, ⟨2, 1⟩, ⟨12, 1⟩, ⟨2, 0⟩,
      by decide +kernel⟩)
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 2⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 2⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 2⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 2⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 2⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 2⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 2⟩, by decide +kernel⟩
  · exact Or.inl ⟨⟨0, 0⟩, ⟨0, 2⟩, by decide +kernel⟩

@[expose] def xh : MC := t * u * y

@[expose] def u₂ : MC := t * (xh * (xh * y))

@[expose] def CondA (a : MC) : Prop :=
  a * z * a⁻¹ = z ∧ a * (xh * y) * a⁻¹ = xh * y ∧ a * (z * k) * a⁻¹ = z * k ∧
    a * t * a⁻¹ = t * (z * k) ∧ a * xh * a⁻¹ = z * k * xh ∧ a * a = 1 ∧ u₂ * a = a * u₂

instance (a : MC) : Decidable (CondA a) := by unfold CondA; infer_instance

@[expose] def CondB (b : MC) : Prop :=
  b * t * b⁻¹ = z * (t * (z * k)) ∧ b * z * b⁻¹ = z ∧ b * (z * k) * b⁻¹ = z * k ∧
    b * (xh * y) * b⁻¹ = xh * y * (z * k) ∧ b * xh * b⁻¹ = xh * (z * k) ∧ b * b = 1 ∧
      u₂ * b * u₂⁻¹ = b * (z * (z * k))

instance (b : MC) : Decidable (CondB b) := by unfold CondB; infer_instance

@[expose] def Alist : List MC := [⟨13, 6⟩, ⟨5, 6⟩, ⟨12, 6⟩, ⟨4, 6⟩]

@[expose] def Blist : List MC := [⟨2, 8⟩, ⟨10, 8⟩, ⟨3, 8⟩, ⟨11, 8⟩]

theorem A_cands : ∀ a : MC, CondA a → a ∈ Alist := by decide +kernel

theorem B_cands : ∀ b : MC, CondB b → b ∈ Blist := by decide +kernel

@[expose] def E4gens : List MC := [z, k, w₁, u * v]

@[expose] def thL (a b : MC) : List MC := [u₂, b, a, z, xh * y, t, z * k]

@[expose] def L7 : List MC := [u, w₁, v, z, y, t, k]

@[expose] def crossTab : ℕ :=
  87328431702526430706575805803515488807529939710077934423084858312899282740232 + 2 ^ 256 *
  (3850500833654497462934289878384704154147507949669757016065753252274924375137 + 2 ^ 256 *
  (15041294265347222202821887418796673967840062790146293770769397330078307783204 + 2 ^ 256 *
  (3064129621497321876784960483441021550)))

@[expose] def bitsN (n : ℕ) : List Bool := (List.range 7).map n.testBit

theorem cross_cert : ∀ i j l : Fin 4,
    E4gens.getD l 1 = nfProd (thL (Alist.getD i 1) (Blist.getD j 1))
        (bitsN (tget crossTab 14 (16 * i.val + 4 * j.val + l.val) % 128)) ∧
      w₂ * nfProd L7 (bitsN (tget crossTab 14 (16 * i.val + 4 * j.val + l.val) % 128)) * w₂⁻¹ =
        nfProd L7 (bitsN (tget crossTab 14 (16 * i.val + 4 * j.val + l.val) / 128)) ∧
      inE2 (w₂ * nfProd (thL (Alist.getD i 1) (Blist.getD j 1))
        (bitsN (tget crossTab 14 (16 * i.val + 4 * j.val + l.val) / 128)) * w₂⁻¹) = true := by
  decide +kernel

end MC

end CFSG.ComponentClassification.HSFLit.Sec8
