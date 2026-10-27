module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MA

public section

namespace CFSG.ComponentClassification.HSFLit.Sec8

namespace MA

@[expose] def bit (x : MA) (i : ℕ) : Bool := (tget nfTabMA 8 (16 * x.g.val + x.a.val)).testBit i

@[expose] def ccount (x : MA) : ℕ := (Finset.univ.filter fun g : MA => g * x = x * g).card

@[expose] def inT1 (x : MA) : Bool := !bit x 0

@[expose] def inM (x : MA) : Bool := !bit x 6

@[expose] def inM1 (x : MA) : Bool := !bit x 0 && !bit x 6

@[expose] def inW (x : MA) : Bool := !bit x 0 && !bit x 1 && !bit x 5 && !bit x 6

@[expose] def inQC (x : MA) : Bool := !bit x 1 && !bit x 6

@[expose] def ofPred (p : MA → Bool) (h1 : p 1 = true)
    (hmul : ∀ x, p x = true → ∀ y, p y = true → p (x * y) = true)
    (hinv : ∀ x, p x = true → p x⁻¹ = true) : Subgroup MA where
  carrier := {x | p x = true}
  mul_mem' {a b} ha hb := hmul a ha b hb
  one_mem' := h1
  inv_mem' {a} ha := hinv a ha

theorem card_ofPred (p : MA → Bool) (h1 : p 1 = true)
    (hmul : ∀ x, p x = true → ∀ y, p y = true → p (x * y) = true)
    (hinv : ∀ x, p x = true → p x⁻¹ = true) :
    Nat.card (ofPred p h1 hmul hinv) = (Finset.univ.filter fun x => p x = true).card := by
  rw [show Nat.card (ofPred p h1 hmul hinv) = Nat.card {x : MA // p x = true} from rfl,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

@[expose] def M : Subgroup MA := ofPred inM (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem card_M : Nat.card M = 128 := by
  rw [M, card_ofPred]; decide +kernel

@[expose] def W : Subgroup MA := ofPred inW (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem card_W : Nat.card W = 16 := by
  rw [W, card_ofPred]; decide +kernel

theorem W_comm : ∀ a : MA, inW a = true → ∀ b : MA, inW b = true → a * b = b * a := by
  decide +kernel

theorem W_sq : ∀ a : MA, inW a = true → a * a = 1 := by decide +kernel

theorem T1_span : ∀ x : MA, inT1 x = true → InSpan [u, w₁, v, z, y, t, k] x := by decide +kernel

theorem M_span : ∀ x : MA, inM x = true → InSpan [w₂, u, w₁, v, z, y, k] x := by decide +kernel

theorem W_span : ∀ x : MA, inW x = true → InSpan [w₁, v, z, k] x := by decide +kernel

theorem QC_span : ∀ x : MA, inQC x = true → InSpan [w₂, w₁, v, z, y, k] x := by decide +kernel

@[expose] def KcList : List MA :=
  [⟨4, 0⟩, ⟨12, 0⟩, ⟨6, 0⟩, ⟨14, 0⟩, ⟨5, 0⟩, ⟨13, 0⟩, ⟨7, 0⟩, ⟨15, 0⟩, ⟨4, 2⟩, ⟨12, 2⟩, ⟨5, 2⟩,
    ⟨13, 2⟩, ⟨6, 6⟩, ⟨14, 6⟩, ⟨7, 6⟩, ⟨15, 6⟩]

theorem L_fact : ∀ x : MA, x * x = 1 → x ≠ 1 → inQC x = false → ccount x ≤ 32 →
    x ∈ KcList ∨ ∃ s : MA, s * x * s⁻¹ = u * v := by decide +kernel

theorem Kc_conj : ∀ x ∈ KcList, (∃ s : MA, s * t * s⁻¹ = x) ∨
    ∃ s : MA, s * (t * u) * s⁻¹ = x := by decide +kernel

theorem Kc_not_M : ∀ x ∈ KcList, inM x = false := by decide +kernel

theorem cent_T1 : ∀ x : MA, (∀ g ∈ [u, w₁, v, z, y, t, k], g * x = x * g) →
    x = 1 ∨ x = z ∨ x = k ∨ x = z * k := by decide +kernel

theorem M1_comm_W : ∀ x : MA, inM1 x = true → ∀ c : MA, inW c = true → x * c = c * x := by
  decide +kernel

theorem decomp : ∀ x : MA, inM1 x = true ∨ inM1 (t * x) = true ∨ inM1 (w₂ * x) = true ∨
    inM1 (t * (w₂ * x)) = true := by decide +kernel

theorem M1_decomp : ∀ m : MA, inM1 m = true → ∃ c : MA, inW c = true ∧
    (m = c ∨ m = u * c ∨ m = y * c ∨ m = u * y * c) := by decide +kernel

theorem cert1 : ∀ m : MA, inM1 m = true → ∀ c : MA, inW c = true →
    inW (t * u * m * c * t * m) = false := by decide +kernel

theorem cert2 : ∀ m : MA, inM1 m = true → ∀ c : MA, inW c = true →
    inW (w₂ * t * u * m * c * w₂ * t * m) = false := by decide +kernel

@[expose] def T1 : Subgroup MA := ofPred inT1 (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem card_T1 : Nat.card T1 = 128 := by
  rw [T1, card_ofPred]; decide +kernel

theorem T1_normal : ∀ s x : MA, inT1 x = true → inT1 (s * x * s⁻¹) = true := by decide +kernel

theorem W_normal : ∀ s x : MA, inW x = true → inW (s * x * s⁻¹) = true := by decide +kernel

theorem W_le_M1 : ∀ x : MA, inW x = true → inM1 x = true := by decide +kernel

@[expose] def ZList : List MA := [1, z, k, z * k]

@[expose] def CondW (c s : MA) : Prop :=
  s * (t * u) * s⁻¹ = y * w₁ * c * (t * u) ∧ s * u * s⁻¹ = u * w₁ ∧
    s * (y * w₁ * c) * s⁻¹ = y * w₁ * c ∧ s * z * s⁻¹ = z ∧ s * k * s⁻¹ = k ∧
      s * w₁ * s⁻¹ = w₁ ∧ s * v * s⁻¹ = v

instance (c s : MA) : Decidable (CondW c s) := by unfold CondW; infer_instance

@[expose] def AlphaLike (c s : MA) : Prop :=
  s * t * s⁻¹ = t * u ∧ s * u * s⁻¹ = u ∧ s * y * s⁻¹ = y * w₁ * c ∧ s * z * s⁻¹ = z ∧
    s * k * s⁻¹ = k ∧ s * w₁ * s⁻¹ = w₁ ∧ s * v * s⁻¹ = v

instance (c s : MA) : Decidable (AlphaLike c s) := by unfold AlphaLike; infer_instance

@[expose] def condWit (c : MA) : MA :=
  if c = 1 then w₂ * w₁ else if c = z then w₂ else if c = k then w₂ * w₁ * v else w₂ * v

theorem condW_wit : ∀ c ∈ ZList, CondW c (condWit c) := by decide +kernel

theorem condW_wit_W : ∀ c ∈ ZList, ∀ ζ ∈ ZList, inW (w₂ * (condWit c * ζ)) = true := by
  decide +kernel

theorem not_conj_t_tu : ∀ s : MA, s * t * s⁻¹ ≠ t * u := by decide +kernel

theorem w₂_comm_W' : ∀ c : MA, inW c = true → w₂ * c = c * w₂ := by decide +kernel

theorem w₂_sq : w₂ * w₂ = 1 := by decide +kernel

theorem ZList_W : ∀ c ∈ ZList, inW c = true := by decide +kernel

theorem ZList_mul_W : ∀ c ∈ ZList, ∀ d : MA, inW d = true → inW (d * c) = true := by
  decide +kernel

theorem inM_mul_t : ∀ x : MA, inM (x * t) = !inM x := by decide +kernel

theorem inM_w₂W : ∀ c : MA, inW c = true → inM (w₂ * c) = true := by decide +kernel

theorem W_mul : ∀ a : MA, inW a = true → ∀ b : MA, inW b = true → inW (a * b) = true := by
  decide +kernel

theorem ZList_M : ∀ c ∈ ZList, inM c = true := by decide +kernel

theorem one_W : inW 1 = true := by decide +kernel

end MA

end CFSG.ComponentClassification.HSFLit.Sec8
