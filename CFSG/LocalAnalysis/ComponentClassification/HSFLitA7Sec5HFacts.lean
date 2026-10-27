module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5HModel

public section

namespace CFSG.ComponentClassification.HSFLit.Sec5H

open Sec8 Subgroup

namespace RH

@[expose] def inMask (m : ℕ) (c : RH) : Bool := m.testBit (16 * c.g.val + c.a.val)

@[expose] def u : RH := x * y

@[expose] def w₁ : RH := w * t

@[expose] def wp : RH := x * t * w

@[expose] def Ggens : Fin 8 → List RH
  | 0 => [z, k, t, y]
  | 1 => [z, k, t, u]
  | 2 => [z, k, w, y]
  | 3 => [z, k, w, u]
  | 4 => [z, k, wp, t * y]
  | 5 => [z, k, wp, t * u]
  | 6 => [z, k, y, w₂ * t]
  | 7 => [z, k, y, w₁ * w₂ * t]

@[expose] def Gmask : Fin 8 → ℕ
  | 0 => 65535
  | 1 => 967125898296444372136755
  | 2 => 16557098929935
  | 3 => 244339653250880975865121219805955
  | 4 => 1221698265969956085692447714231235
  | 5 => 977358613686201008140327965426435
  | 6 => 4042264335
  | 7 => 1085086035219582735

@[expose] def pG (i : Fin 8) (c : RH) : Bool := inMask (Gmask i) c

@[expose] def pT2 (c : RH) : Bool := c.g.val % 2 == 0

@[expose] def pQ (c : RH) : Bool := c.g.val / 4 == 0

@[expose] def pE0 (c : RH) : Bool := inMask 3855 c

@[expose] def pZ (c : RH) : Bool := inMask 771 c

@[expose] def pZY (c : RH) : Bool := inMask 15 c

@[expose] def T2gens : List RH := [w, x, z, y, t, k]

@[expose] def Qgens : List RH := [z, y, t, k, w₁, w₂]

@[expose] def span (gs : List RH) : Subgroup RH := closure {c | c ∈ gs}

theorem mem_span_iff_of {gs : List RH} {p : RH → Bool} (h1 : p 1 = true)
    (hmul : ∀ g ∈ gs, ∀ c, p c = true → p (g * c) = true)
    (hinv : ∀ g ∈ gs, ∀ c, p c = true → p (g⁻¹ * c) = true)
    (hspan : ∀ c, p c = true → InSpan gs c) (c : RH) : c ∈ span gs ↔ p c = true := by
  constructor
  · intro hc
    induction hc using Subgroup.closure_induction_left with
    | one => exact h1
    | mul_left x hx y _ ih => exact hmul x hx y ih
    | inv_mul_cancel x hx y _ ih => exact hinv x hx y ih
  · intro hc
    obtain ⟨bs, -, rfl⟩ := hspan c hc
    exact nfProd_mem_closure gs (fun g hg => hg) bs

theorem card_of_mem_iff {H : Subgroup RH} {p : RH → Bool} (h : ∀ c, c ∈ H ↔ p c = true) :
    Nat.card H = (Finset.univ.filter fun c => p c = true).card := by
  classical
  rw [show Nat.card H = Nat.card {c // c ∈ H} from rfl,
    Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card, Fintype.card_subtype]

@[expose] def G (i : Fin 8) : Subgroup RH := span (Ggens i)

theorem mem_G (i : Fin 8) (c : RH) : c ∈ G i ↔ pG i c = true := by
  have h1 : ∀ i : Fin 8, pG i 1 = true := by decide +kernel
  have hmul : ∀ i : Fin 8, ∀ g ∈ Ggens i, ∀ c, pG i c = true → pG i (g * c) = true := by
    decide +kernel
  have hinv : ∀ i : Fin 8, ∀ g ∈ Ggens i, ∀ c, pG i c = true → pG i (g⁻¹ * c) = true := by
    decide +kernel
  have hspan : ∀ i : Fin 8, ∀ c, pG i c = true → InSpan (Ggens i) c := by decide +kernel
  exact mem_span_iff_of (h1 i) (hmul i) (hinv i) (hspan i) c

theorem card_G (i : Fin 8) : Nat.card (G i) = 16 := by
  rw [card_of_mem_iff (mem_G i)]
  revert i
  decide +kernel

@[expose] def T2 : Subgroup RH := span T2gens

theorem mem_T2 (c : RH) : c ∈ T2 ↔ pT2 c = true :=
  mem_span_iff_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) c

theorem card_T2 : Nat.card T2 = 64 := by
  rw [card_of_mem_iff mem_T2]; decide +kernel

@[expose] def Q : Subgroup RH := span Qgens

theorem mem_Q (c : RH) : c ∈ Q ↔ pQ c = true :=
  mem_span_iff_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) c

theorem Q_comm_y : ∀ c : RH, pQ c = true → c * y = y * c := by decide +kernel

theorem card_Q : Nat.card Q = 64 := by
  rw [card_of_mem_iff mem_Q]; decide +kernel

@[expose] def E0 : Subgroup RH := span [z, y, k]

theorem mem_E0 (c : RH) : c ∈ E0 ↔ pE0 c = true :=
  mem_span_iff_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) c

theorem card_E0 : Nat.card E0 = 8 := by
  rw [card_of_mem_iff mem_E0]; decide +kernel

@[expose] def Zs : Subgroup RH := span [z, k]

theorem mem_Zs (c : RH) : c ∈ Zs ↔ pZ c = true :=
  mem_span_iff_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) c

theorem pZ_iff : ∀ c : RH, pZ c = true ↔ (c = 1 ∨ c = z ∨ c = k ∨ c = z * k) := by
  decide +kernel

@[expose] def ZY : Subgroup RH := span [z, y]

theorem mem_ZY (c : RH) : c ∈ ZY ↔ pZY c = true :=
  mem_span_iff_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) c

theorem pZY_cases : ∀ c : RH, pZY c = true → c = 1 ∨ c = z ∨ c = y ∨ c = z * y := by
  decide +kernel

theorem pG_sq : ∀ i : Fin 8, ∀ c, pG i c = true → c * c = 1 := by decide +kernel

theorem card_Z_union : ∀ a : RH,
    (Finset.univ.filter fun c => pZ c = true ∨ pZ (a⁻¹ * c) = true).card ≤ 8 := by
  decide +kernel

theorem card_Z : (Finset.univ.filter fun c => pZ c = true).card = 4 := by decide +kernel

theorem pair_cover : ∀ a b : RH, a * a = 1 → b * b = 1 → a * b = b * a → pZ a = false →
    pZ b = false → pZ (a⁻¹ * b) = false → ∃ i : Fin 8, pG i a = true ∧ pG i b = true := by
  decide +kernel

theorem cent_cover : ∀ i : Fin 8, ∀ a, pG i a = true → pZ a = false → ∀ b, pG i b = true →
    pZ b = false → pZ (a⁻¹ * b) = false → ∀ c, c * a = a * c → c * b = b * c →
      pG i c = true := by
  decide +kernel

theorem le_G_of_elem (A : Subgroup RH) (hA : ∀ a ∈ A, a * a = 1) (hcard : 16 ≤ Nat.card A) :
    ∃ i : Fin 8, A ≤ G i := by
  classical
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h1 := hA _ (mul_mem ha hb)
    have h2 := hA a ha
    have h3 := hA b hb
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
      _ = (a * a) * (b * a) * (b * b) := by group
      _ = b * a := by rw [h2, h3, one_mul, mul_one]
  have hcardA : 16 ≤ (Finset.univ.filter fun c => c ∈ A).card := by
    rwa [show Nat.card A = (Finset.univ.filter fun c => c ∈ A).card by
      rw [show Nat.card A = Nat.card {c // c ∈ A} from rfl, Nat.card_eq_fintype_card,
        Fintype.card_subtype]] at hcard
  obtain ⟨a, haA, haZ⟩ : ∃ a, a ∈ A ∧ pZ a = false := by
    by_contra hno
    push Not at hno
    have hle : (Finset.univ.filter fun c => c ∈ A) ⊆ Finset.univ.filter fun c => pZ c = true := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      simpa using hno c hc
    have := Finset.card_le_card hle
    rw [card_Z] at this
    omega
  obtain ⟨b, hbA, hbZ⟩ : ∃ b, b ∈ A ∧ ¬ (pZ b = true ∨ pZ (a⁻¹ * b) = true) := by
    by_contra hno
    push Not at hno
    have hle : (Finset.univ.filter fun c => c ∈ A) ⊆
        Finset.univ.filter fun c => pZ c = true ∨ pZ (a⁻¹ * c) = true := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hno c hc
    have := Finset.card_le_card hle
    have := card_Z_union a
    omega
  push Not at hbZ
  obtain ⟨i, hai, hbi⟩ := pair_cover a b (hA a haA) (hA b hbA) (hcomm a haA b hbA) haZ
    (by simpa using hbZ.1) (by simpa using hbZ.2)
  refine ⟨i, fun c hc => (mem_G i c).mpr ?_⟩
  exact cent_cover i a hai haZ b hbi (by simpa using hbZ.1) (by simpa using hbZ.2) c
    (hcomm c hc a haA) (hcomm c hc b hbA)

theorem G_distinct : ∀ i j : Fin 8, i ≠ j → ∃ c : RH, pG i c ≠ pG j c := by decide +kernel

theorem normal_cases : ∀ i : Fin 8,
    (∀ g ∈ gens, ∀ c, pG i c = true → pG i (g * c * g⁻¹) = true) → i = 0 ∨ i = 2 := by
  decide +kernel

@[expose] def wtau : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 4
  | 2 => 2
  | 3 => 5
  | 4 => 1
  | 5 => 3
  | 6 => 6
  | 7 => 7

theorem w2_conj : ∀ i : Fin 8, ∀ c, pG i c = true → pG (wtau i) (w₂ * c * w₂⁻¹) = true := by
  decide +kernel

theorem T2_norm : ∀ i : Fin 8, i.val < 6 → ∀ τ, pT2 τ = true → ∀ c, pG i c = true →
    pG i (τ * c * τ⁻¹) = true := by
  decide +kernel

theorem G_T2 : ∀ i : Fin 8, i.val < 6 → ∀ c, pG i c = true → pT2 c = true := by
  decide +kernel

theorem G_inf_T2 : ∀ i : Fin 8, 6 ≤ i.val → ∀ c, pG i c = true → pT2 c = true →
    pE0 c = true := by
  decide +kernel

theorem G_inf_Q : ∀ i : Fin 8, (i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 5) →
    (Finset.univ.filter fun c => pG i c = true ∧ pQ c = true).card ≤ 8 := by
  decide +kernel

theorem G_Q : ∀ i : Fin 8, (i = 0 ∨ i = 2 ∨ i = 6 ∨ i = 7) → ∀ c, pG i c = true →
    pQ c = true := by
  decide +kernel

theorem inter_Z : ∀ c : RH, (pG 1 c = true ∧ pG 2 c = true → pZ c = true) ∧
    (pG 1 c = true ∧ pG 4 c = true → pZ c = true) ∧
    (pG 0 c = true ∧ pG 3 c = true → pZ c = true) ∧
    (pG 0 c = true ∧ pG 5 c = true → pZ c = true) := by
  decide +kernel

theorem inter_big : (pG 0 y = true ∧ pG 2 y = true ∧ pZ y = false) ∧
    (pG 0 (t * y) = true ∧ pG 4 (t * y) = true ∧ pZ (t * y) = false) ∧
    (pG 1 u = true ∧ pG 3 u = true ∧ pZ u = false) ∧
    (pG 1 (t * u) = true ∧ pG 5 (t * u) = true ∧ pZ (t * u) = false) := by
  decide +kernel

theorem T2_orbit : ∀ τ : RH, pT2 τ = true →
    (τ * t * τ⁻¹ = t ∨ τ * t * τ⁻¹ = z * t) ∧ (τ * y * τ⁻¹ = y ∨ τ * y * τ⁻¹ = z * y) := by
  decide +kernel

theorem T2_orbit_O : ∀ τ : RH, pT2 τ = true → ∀ e ∈ [t, t * z, t * y, t * z * y],
    τ * e * τ⁻¹ = e ∨ τ * e * τ⁻¹ = z * e := by
  decide +kernel

theorem O_facts : ∀ e ∈ [t, t * z, t * y, t * z * y], e * e = 1 ∧ e * z = z * e := by
  decide +kernel

theorem y_ne : y ≠ 1 ∧ y ≠ z := by decide +kernel

theorem cent_y : ∀ c : RH, c * y = y * c → pQ c = true := by decide +kernel

theorem inter_E0 : ∀ c : RH, pG 0 c = true → pG 2 c = true → pE0 c = true := by decide +kernel

theorem z_k_comm : ∀ c : RH, c * z = z * c ∧ c * k = k * c := by decide +kernel

theorem T2_cases : ∀ c : RH, pT2 c = true ∨ pT2 (w₂⁻¹ * c) = true := by decide +kernel

theorem r_action : ∀ e ∈ [t, t * z, t * y, t * z * y], ∀ f ∈ [y, z * y], ∃ r : RH,
    r * t * r⁻¹ = e ∧ r * y * r⁻¹ = f ∧ r * z * r⁻¹ = z ∧ r * k * r⁻¹ = k ∧
      (pT2 r = true ↔ (e = t ∨ e = t * z)) := by
  decide +kernel

theorem d_images : pG 6 (z * y) = true ∧ pG 7 (z * y) = true ∧ pG 7 ((w₂ * w₁)⁻¹ * t) = true := by
  decide +kernel

end RH

end CFSG.ComponentClassification.HSFLit.Sec5H
