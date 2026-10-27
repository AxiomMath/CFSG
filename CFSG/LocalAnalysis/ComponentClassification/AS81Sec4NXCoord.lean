module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStab
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Kernel

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open Hexa

variable {G : Type} [Group G]

section Bits

@[expose] def bitE (c : Bool) (x : G) : G := if c then x else 1

@[expose] def pairE (x y : G) (a b : Bool) : G := bitE a x * bitE b y

@[expose] def coordE (r₀ r₁ s₀ s₁ t₀ t₁ : G) (v : ℕ) : G :=
  pairE r₀ r₁ (v.testBit 0) (v.testBit 1) * pairE s₀ s₁ (v.testBit 2) (v.testBit 3) *
    pairE t₀ t₁ (v.testBit 4) (v.testBit 5)

theorem pairE_mem {P : Subgroup G} {x y : G} (hx : x ∈ P) (hy : y ∈ P) (a b : Bool) :
    pairE x y a b ∈ P := by
  unfold pairE bitE
  exact mul_mem (by split_ifs <;> simp [hx]) (by split_ifs <;> simp [hy])

theorem pairE_xor {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (a b a' b' : Bool) : pairE x y (a ^^ a') (b ^^ b') = pairE x y a b * pairE x y a' b' := by
  have hx' : ∀ z, x * (x * z) = z := fun z => by rw [← mul_assoc, hx, one_mul]
  have hyx : y * x = x * y := hxy.symm
  have hyx' : ∀ z, y * (x * z) = x * (y * z) := fun z => by rw [← mul_assoc, hyx, mul_assoc]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp only [pairE, bitE, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_true, ite_false, mul_one, one_mul, mul_assoc, hx, hy, hx', hyx,
      hyx']

theorem pairE_eq_one_iff {x y : G} (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) (hx : x * x = 1)
    {a b : Bool} : pairE x y a b = 1 ↔ a = false ∧ b = false := by
  constructor
  · intro h
    cases a <;> cases b
    · exact ⟨rfl, rfl⟩
    · exact absurd (by simpa [pairE, bitE] using h) hy1
    · exact absurd (by simpa [pairE, bitE] using h) hx1
    · exfalso
      simp only [pairE, bitE, ite_true] at h
      exact hxy ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hx)).symm
  · rintro ⟨rfl, rfl⟩
    simp [pairE, bitE]

theorem mul_mul_mul_six {a₀ b₀ a₁ b₁ a₂ b₂ : G} (h₁ : b₀ * a₁ = a₁ * b₀) (h₂ : b₀ * a₂ = a₂ * b₀)
    (h₃ : b₁ * a₂ = a₂ * b₁) :
    a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) = a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) :=
  calc a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) = a₀ * (b₀ * a₁) * b₁ * a₂ * b₂ := by
        simp only [mul_assoc]
    _ = a₀ * (a₁ * b₀) * b₁ * a₂ * b₂ := by rw [h₁]
    _ = a₀ * a₁ * b₀ * (b₁ * a₂) * b₂ := by simp only [mul_assoc]
    _ = a₀ * a₁ * b₀ * (a₂ * b₁) * b₂ := by rw [h₃]
    _ = a₀ * a₁ * (b₀ * a₂) * b₁ * b₂ := by simp only [mul_assoc]
    _ = a₀ * a₁ * (a₂ * b₀) * b₁ * b₂ := by rw [h₂]
    _ = a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) := by simp only [mul_assoc]

end Bits

section Vectors

theorem eq_zero_of_bits : ∀ u : Fin 64, u.val.testBit 0 = false → u.val.testBit 1 = false →
    u.val.testBit 2 = false → u.val.testBit 3 = false → u.val.testBit 4 = false →
    u.val.testBit 5 = false → u = 0 := by
  decide

theorem mem_oval_iff : ∀ k ∈ List.range 6, ∀ a : Fin 64, a.val ∈ hexaOval[k]! → ∀ b : Fin 64,
    b.val ∈ hexaOval[k]! → a ≠ 0 → b ≠ 0 → a ≠ b → ∀ v : Fin 64,
      (v.val ∈ hexaOval[k]! ↔ v = 0 ∨ v = a ∨ v = b ∨ v = xorF a b) := by
  decide +kernel

theorem lt_of_mem_oval : ∀ j < 6, ∀ x ∈ hexaOval[j]!, x < 64 := by decide

end Vectors

structure HexaCoord (X R : Subgroup G) (pts : Set (Subgroup G)) (rep : Fin 64 → G) : Prop where
  add : ∀ v w, rep (xorF v w) = rep v * rep w
  mem : ∀ v, rep v ∈ X
  inj : Function.Injective rep
  surj : ∀ x ∈ X, ∃ v, rep v = x
  R_iff : ∀ v, rep v ∈ R ↔ v.val ∈ hexaOval[0]!
  pt : ∀ P ∈ pts, ∃ j < 6, ∀ v, rep v ∈ P ↔ v.val ∈ hexaOval[j]!
  line : ∀ j < 6, ∃ P ∈ pts, ∀ v, rep v ∈ P ↔ v.val ∈ hexaOval[j]!

section Coord

variable [Finite G]

theorem eq_of_mem_card_four {P : Subgroup G} (h4 : Nat.card P = 4) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hsq : a * a = 1) {x : G}
    (hx : x ∈ P) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hx1, hxa, hxb, hxab⟩ := hne
  have h12a : a * b ≠ 1 := fun h => hab (by
    have h' := eq_inv_of_mul_eq_one_right h
    rwa [inv_eq_of_mul_eq_one_right hsq, eq_comm] at h')
  have h12b : a * b ≠ a := fun h => hb1 (by simpa using h)
  have h12c : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hsub : (({1, a, b, a * b, x} : Finset G) : Set G) ⊆ (P : Set G) := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact P.one_mem
    · exact ha
    · exact hb
    · exact P.mul_mem ha hb
    · exact hx
  have hcard : ({1, a, b, a * b, x} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (Ne.symm hxab)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm h12c, Ne.symm hxb⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, Ne.symm h12b, Ne.symm hxa⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm h12a, Ne.symm hx1⟩
  have hle := Nat.card_mono (Set.toFinite _) hsub
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hcard] at hle
  have : Nat.card (P : Set G) = 4 := h4
  omega

omit [Finite G] in
theorem exists_two_of_card_four {P : Subgroup G} (h4 : Nat.card P = 4) :
    ∃ a ∈ P, ∃ b ∈ P, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  obtain ⟨a, ha, ha1⟩ := exists_mem_not_mem_finset (V := (P : Set G)) {1}
    (by rw [Finset.card_singleton]; exact lt_of_lt_of_eq (by norm_num) h4.symm)
  obtain ⟨b, hb, hb1⟩ := exists_mem_not_mem_finset (V := (P : Set G)) {1, a}
    (lt_of_le_of_lt Finset.card_le_two (lt_of_lt_of_eq (by norm_num) h4.symm))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 hb1
  exact ⟨a, ha, b, hb, ha1, hb1.1, Ne.symm hb1.2⟩

omit [Finite G] in
theorem eq_one_of_mul_mul {R P Q : Subgroup G} (hRPQ : R ⊓ (P ⊔ Q) = ⊥) (hPQ : P ⊓ Q = ⊥)
    {a b c : G} (ha : a ∈ R) (hb : b ∈ P) (hc : c ∈ Q) (h : a * b * c = 1) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  have ha1 : a = 1 := by
    have e : a = (b * c)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← mul_assoc, h])
    have hm : a ∈ R ⊓ (P ⊔ Q) :=
      mem_inf.mpr ⟨ha, e ▸ inv_mem (mul_mem (mem_sup_left hb) (mem_sup_right hc))⟩
    rwa [hRPQ, mem_bot] at hm
  subst ha1
  rw [one_mul] at h
  have hb1 : b = 1 := by
    have e : b = c⁻¹ := eq_inv_of_mul_eq_one_left h
    have hm : b ∈ P ⊓ Q := mem_inf.mpr ⟨hb, e ▸ inv_mem hc⟩
    rwa [hPQ, mem_bot] at hm
  subst hb1
  exact ⟨rfl, rfl, by simpa using h⟩

omit [Finite G] in
theorem eq_one_of_mul {P Q : Subgroup G} (hPQ : P ⊓ Q = ⊥) {a b : G} (ha : a ∈ P) (hb : b ∈ Q)
    (h : a * b = 1) : a = 1 ∧ b = 1 := by
  have ha1 : a = 1 := by
    have e : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    have hm : a ∈ P ⊓ Q := mem_inf.mpr ⟨ha, e ▸ inv_mem hb⟩
    rwa [hPQ, mem_bot] at hm
  subst ha1
  exact ⟨rfl, by simpa using h⟩

omit [Finite G] in
theorem mul_three_comm {a b c a' b' c' : G} (h₁ : c * a' = a' * c) (h₂ : b * a' = a' * b)
    (h₃ : c * b' = b' * c) : a * b * c * (a' * b' * c') = a * a' * (b * b') * (c * c') :=
  calc a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by simp only [mul_assoc]
    _ = a * b * (a' * c) * b' * c' := by rw [h₁]
    _ = a * (b * a') * (c * b') * c' := by simp only [mul_assoc]
    _ = a * (a' * b) * (b' * c) * c' := by rw [h₂, h₃]
    _ = a * a' * (b * b') * (c * c') := by simp only [mul_assoc]

theorem exists_hexaCoord_two (hS : hexaStabCheck = true) {X : Subgroup G}
    (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hsq : ∀ x ∈ X, x * x = 1) (h64 : Nat.card X = 64)
    {pts : Set (Subgroup G)} (hle : ∀ P ∈ pts, P ≤ X) (h4 : ∀ P ∈ pts, Nat.card P = 4)
    (hgp : ∀ P ∈ pts, ∀ P' ∈ pts, ∀ P'' ∈ pts, P ≠ P' → P ≠ P'' → P' ≠ P'' →
      P'' ⊓ (P ⊔ P') = ⊥)
    (h6 : Nat.card pts = 6) {R P₁ : Subgroup G} (hR : R ∈ pts) (hP₁ : P₁ ∈ pts) (h1 : P₁ ≠ R) :
    ∃ rep : Fin 64 → G, HexaCoord X R pts rep ∧ ∀ v, rep v ∈ P₁ ↔ v.val ∈ hexaOval[1]! := by
  classical
  have hnew : ∀ S : Finset (Subgroup G), S.card < 6 → ∃ P ∈ pts, P ∉ S := fun S hS =>
    exists_mem_not_mem_finset (V := pts) S (h6.symm ▸ hS)
  obtain ⟨P₂, hP₂, h2⟩ := hnew {R, P₁} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  obtain ⟨P₃, hP₃, h3⟩ := hnew {R, P₁, P₂} (lt_of_le_of_lt Finset.card_le_three (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2 h3
  obtain ⟨h2R, h21⟩ := h2
  obtain ⟨h3R, h31, h32⟩ := h3
  have hRX := hle R hR
  have hP₁X := hle P₁ hP₁
  have hP₂X := hle P₂ hP₂
  have hP₃X := hle P₃ hP₃
  have g₂ : P₁ ⊓ (R ⊔ P₂) = ⊥ := hgp R hR P₂ hP₂ P₁ hP₁ (Ne.symm h2R) (Ne.symm h1) h21
  have g₃ : R ⊓ (P₁ ⊔ P₂) = ⊥ := hgp P₁ hP₁ P₂ hP₂ R hR (Ne.symm h21) h1 h2R
  have g₄ : P₃ ⊓ (P₁ ⊔ P₂) = ⊥ :=
    hgp P₁ hP₁ P₂ hP₂ P₃ hP₃ (Ne.symm h21) (Ne.symm h31) (Ne.symm h32)
  have g₅ : P₃ ⊓ (R ⊔ P₂) = ⊥ :=
    hgp R hR P₂ hP₂ P₃ hP₃ (Ne.symm h2R) (Ne.symm h3R) (Ne.symm h32)
  have g₆ : P₃ ⊓ (R ⊔ P₁) = ⊥ := hgp R hR P₁ hP₁ P₃ hP₃ (Ne.symm h1) (Ne.symm h3R) (Ne.symm h31)
  have g₀₁ : R ⊓ P₁ = ⊥ := by
    rw [eq_bot_iff, ← g₃]
    exact inf_le_inf_left R le_sup_left
  have g₀₂ : R ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff, ← g₃]
    exact inf_le_inf_left R le_sup_right
  have g₁₂ : P₁ ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff, ← g₂]
    exact inf_le_inf_left P₁ le_sup_right
  obtain ⟨r₀, hr₀, r₁, hr₁, hr₀1, hr₁1, hr₀₁⟩ := exists_two_of_card_four (h4 R hR)
  have hcard12 : Nat.card ↥(P₁ ⊔ P₂) = 16 := by
    rw [card_sup_of_inf_eq_bot hc hP₁X hP₂X g₁₂, h4 P₁ hP₁, h4 P₂ hP₂]
  have hX3 : P₃ ⊔ (P₁ ⊔ P₂) = X :=
    sup_eq_of_inf_eq_bot hc hP₃X (sup_le hP₁X hP₂X) g₄ (by rw [h64, h4 P₃ hP₃, hcard12])
  have hlift : ∀ x ∈ X, ∃ s ∈ P₁, ∃ t ∈ P₂, x * s * t ∈ P₃ := by
    intro x hx
    rw [← hX3] at hx
    obtain ⟨y, hy, u, hu, rfl⟩ := exists_mul_of_mem_sup hc hP₃X (sup_le hP₁X hP₂X) hx
    obtain ⟨s, hs, t, ht, rfl⟩ := exists_mul_of_mem_sup hc hP₁X hP₂X hu
    refine ⟨s, hs, t, ht, ?_⟩
    have hst : s * t * (s * t) = 1 := hsq _ (mul_mem (hP₁X hs) (hP₂X ht))
    rw [show y * (s * t) * s * t = y * (s * t * (s * t)) by simp only [mul_assoc], hst, mul_one]
    exact hy
  obtain ⟨s₀, hs₀, t₀, ht₀, hy₀⟩ := hlift r₀ (hRX hr₀)
  obtain ⟨s₁, hs₁, t₁, ht₁, hy₁⟩ := hlift r₁ (hRX hr₁)
  have hnd : ∀ a ∈ R, ∀ b ∈ P₁, ∀ c ∈ P₂, a * b * c ∈ P₃ → a ≠ 1 → b ≠ 1 ∧ c ≠ 1 := by
    intro a ha b hb c hc' habc ha1
    constructor
    · rintro rfl
      rw [mul_one] at habc
      have hm : a * c ∈ P₃ ⊓ (R ⊔ P₂) :=
        mem_inf.mpr ⟨habc, mul_mem (mem_sup_left ha) (mem_sup_right hc')⟩
      rw [g₅, mem_bot] at hm
      exact ha1 (eq_one_of_mul g₀₂ ha hc' hm).1
    · rintro rfl
      rw [mul_one] at habc
      have hm : a * b ∈ P₃ ⊓ (R ⊔ P₁) :=
        mem_inf.mpr ⟨habc, mul_mem (mem_sup_left ha) (mem_sup_right hb)⟩
      rw [g₆, mem_bot] at hm
      exact ha1 (eq_one_of_mul g₀₁ ha hb hm).1
  obtain ⟨hs₀1, ht₀1⟩ := hnd r₀ hr₀ s₀ hs₀ t₀ ht₀ hy₀ hr₀1
  obtain ⟨hs₁1, ht₁1⟩ := hnd r₁ hr₁ s₁ hs₁ t₁ ht₁ hy₁ hr₁1
  have hr01 : r₀ * r₁ ≠ 1 := fun h => hr₀₁
    ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right (hsq r₁ (hRX hr₁))))
  have hy₀₁ : r₀ * r₁ * (s₀ * s₁) * (t₀ * t₁) ∈ P₃ := by
    have h := mul_mem hy₀ hy₁
    rwa [mul_three_comm (hc _ (hP₂X ht₀) _ (hRX hr₁)) (hc _ (hP₁X hs₀) _ (hRX hr₁))
      (hc _ (hP₂X ht₀) _ (hP₁X hs₁))] at h
  obtain ⟨hs01, ht01⟩ :=
    hnd _ (mul_mem hr₀ hr₁) _ (mul_mem hs₀ hs₁) _ (mul_mem ht₀ ht₁) hy₀₁ hr01
  have hs₀₁ : s₀ ≠ s₁ := fun h => hs01 (by rw [h]; exact hsq s₁ (hP₁X hs₁))
  have ht₀₁ : t₀ ≠ t₁ := fun h => ht01 (by rw [h]; exact hsq t₁ (hP₂X ht₁))
  set rep : Fin 64 → G := fun v => coordE r₀ r₁ s₀ s₁ t₀ t₁ v.val with hrep
  have hmem : ∀ v, rep v ∈ X := fun v =>
    mul_mem (mul_mem (pairE_mem (hRX hr₀) (hRX hr₁) _ _) (pairE_mem (hP₁X hs₀) (hP₁X hs₁) _ _))
      (pairE_mem (hP₂X ht₀) (hP₂X ht₁) _ _)
  have hadd : ∀ v w, rep (xorF v w) = rep v * rep w := by
    intro v w
    simp only [hrep, coordE, val_xorF, Nat.testBit_xor]
    rw [pairE_xor (hsq r₀ (hRX hr₀)) (hsq r₁ (hRX hr₁)) (hc _ (hRX hr₀) _ (hRX hr₁)),
      pairE_xor (hsq s₀ (hP₁X hs₀)) (hsq s₁ (hP₁X hs₁)) (hc _ (hP₁X hs₀) _ (hP₁X hs₁)),
      pairE_xor (hsq t₀ (hP₂X ht₀)) (hsq t₁ (hP₂X ht₁)) (hc _ (hP₂X ht₀) _ (hP₂X ht₁))]
    exact mul_mul_mul_six
      (hc _ (pairE_mem (hRX hr₀) (hRX hr₁) _ _) _ (pairE_mem (hP₁X hs₀) (hP₁X hs₁) _ _))
      (hc _ (pairE_mem (hRX hr₀) (hRX hr₁) _ _) _ (pairE_mem (hP₂X ht₀) (hP₂X ht₁) _ _))
      (hc _ (pairE_mem (hP₁X hs₀) (hP₁X hs₁) _ _) _ (pairE_mem (hP₂X ht₀) (hP₂X ht₁) _ _))
  have hrep0 : rep 0 = 1 := by simp [hrep, coordE, pairE, bitE]
  have hone : ∀ u, rep u = 1 → u = 0 := by
    intro u hu
    simp only [hrep, coordE] at hu
    obtain ⟨e₀, e₁, e₂⟩ := eq_one_of_mul_mul g₃ g₁₂ (pairE_mem hr₀ hr₁ _ _)
      (pairE_mem hs₀ hs₁ _ _) (pairE_mem ht₀ ht₁ _ _) hu
    rw [pairE_eq_one_iff hr₀1 hr₁1 hr₀₁ (hsq r₀ (hRX hr₀))] at e₀
    rw [pairE_eq_one_iff hs₀1 hs₁1 hs₀₁ (hsq s₀ (hP₁X hs₀))] at e₁
    rw [pairE_eq_one_iff ht₀1 ht₁1 ht₀₁ (hsq t₀ (hP₂X ht₀))] at e₂
    exact eq_zero_of_bits u e₀.1 e₀.2 e₁.1 e₁.2 e₂.1 e₂.2
  have hinj : Function.Injective rep := by
    intro v w hvw
    have h1 : rep (xorF v w) = 1 := by
      rw [hadd, hvw]
      exact hsq _ (hmem w)
    calc v = xorF (xorF v w) w := by rw [xorF_assoc, xorF_self, xorF_zero]
      _ = w := by rw [hone _ h1, zero_xorF]
  have hsurj : ∀ x ∈ X, ∃ v, rep v = x := by
    intro x hx
    have hbij : Function.Bijective (fun v : Fin 64 => (⟨rep v, hmem v⟩ : ↥X)) :=
      Function.Injective.bijective_of_nat_card_le (fun v w h => hinj (congrArg Subtype.val h))
        (by rw [h64, Nat.card_eq_fintype_card, Fintype.card_fin])
    obtain ⟨v, hv⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  have hline : ∀ P ∈ pts, ∀ k < 6, ∀ a b : Fin 64, a.val ∈ hexaOval[k]! →
      b.val ∈ hexaOval[k]! → a ≠ 0 → b ≠ 0 → a ≠ b → rep a ∈ P → rep b ∈ P →
      ∀ v, rep v ∈ P ↔ v.val ∈ hexaOval[k]! := by
    intro P hP k hk a b ha hb ha0 hb0 hab hra hrb v
    rw [mem_oval_iff k (List.mem_range.2 hk) a ha b hb ha0 hb0 hab v]
    have hra1 : rep a ≠ 1 := fun h => ha0 (hone a h)
    have hrb1 : rep b ≠ 1 := fun h => hb0 (hone b h)
    have hrab : rep a ≠ rep b := fun h => hab (hinj h)
    constructor
    · intro hv
      rcases eq_of_mem_card_four (h4 P hP) hra hrb hra1 hrb1 hrab (hsq _ (hmem a)) hv with
        h | h | h | h
      · exact Or.inl (hone v h)
      · exact Or.inr (Or.inl (hinj h))
      · exact Or.inr (Or.inr (Or.inl (hinj h)))
      · exact Or.inr (Or.inr (Or.inr (hinj (h.trans (hadd a b).symm))))
    · rintro (rfl | rfl | rfl | rfl)
      · rw [hrep0]
        exact one_mem P
      · exact hra
      · exact hrb
      · rw [hadd]
        exact mul_mem hra hrb
  have hv1 : rep 1 = r₀ := by simp [hrep, coordE, pairE, bitE, Nat.testBit]
  have hv2 : rep 2 = r₁ := by simp [hrep, coordE, pairE, bitE, Nat.testBit]
  have hv4 : rep 4 = s₀ := by simp [hrep, coordE, pairE, bitE, Nat.testBit]
  have hv8 : rep 8 = s₁ := by simp [hrep, coordE, pairE, bitE, Nat.testBit]
  have hv16 : rep 16 = t₀ := by simp [hrep, coordE, pairE, bitE, Nat.testBit]
  have hv32 : rep 32 = t₁ := by simp [hrep, coordE, pairE, bitE, Nat.testBit]
  have hv21 : rep 21 = r₀ * s₀ * t₀ := by simp [hrep, coordE, pairE, bitE, Nat.testBit]
  have hv42 : rep 42 = r₁ * s₁ * t₁ := by simp [hrep, coordE, pairE, bitE, Nat.testBit]
  have L₀ : ∀ v, rep v ∈ R ↔ v.val ∈ hexaOval[0]! :=
    hline R hR 0 (by norm_num) 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (hv1 ▸ hr₀) (hv2 ▸ hr₁)
  have L₁ : ∀ v, rep v ∈ P₁ ↔ v.val ∈ hexaOval[1]! :=
    hline P₁ hP₁ 1 (by norm_num) 4 8 (by decide) (by decide) (by decide) (by decide) (by decide)
      (hv4 ▸ hs₀) (hv8 ▸ hs₁)
  have L₂ : ∀ v, rep v ∈ P₂ ↔ v.val ∈ hexaOval[2]! :=
    hline P₂ hP₂ 2 (by norm_num) 16 32 (by decide) (by decide) (by decide) (by decide)
      (by decide) (hv16 ▸ ht₀) (hv32 ▸ ht₁)
  have L₃ : ∀ v, rep v ∈ P₃ ↔ v.val ∈ hexaOval[3]! :=
    hline P₃ hP₃ 3 (by norm_num) 21 42 (by decide) (by decide) (by decide) (by decide)
      (by decide) (hv21 ▸ hy₀) (hv42 ▸ hy₁)
  have hother : ∀ P ∈ pts, P ≠ R → P ≠ P₁ → P ≠ P₂ → P ≠ P₃ →
      ∃ k < 6, ∀ v, rep v ∈ P ↔ v.val ∈ hexaOval[k]! := by
    intro P hP hPR hP1 hP2 hP3
    have hcase : ∀ {Q Q' : Subgroup G} {i j : ℕ}, Q ∈ pts → Q' ∈ pts → Q ≠ Q' → Q ≠ P →
        Q' ≠ P → i < 6 → j < 6 → (∀ v, rep v ∈ Q ↔ v.val ∈ hexaOval[i]!) →
        (∀ v, rep v ∈ Q' ↔ v.val ∈ hexaOval[j]!) → ∀ x : Fin 64, rep x ∈ P → rep x ≠ 1 →
        ∀ y ∈ hexaOval[i]!, ∀ z ∈ hexaOval[j]!, y ^^^ z ≠ x.val := by
      intro Q Q' i j hQ hQ' hQQ' hQP hQ'P hi hj hLQ hLQ' x hxP hx1 y hy z hz hyz
      have hy64 := lt_of_mem_oval i hi y hy
      have hz64 := lt_of_mem_oval j hj z hz
      have hx : x = xorF ⟨y, hy64⟩ ⟨z, hz64⟩ := Fin.ext hyz.symm
      have hm : rep x ∈ P ⊓ (Q ⊔ Q') := by
        refine mem_inf.mpr ⟨hxP, ?_⟩
        rw [hx, hadd]
        exact mul_mem (mem_sup_left ((hLQ _).2 hy)) (mem_sup_right ((hLQ' _).2 hz))
      rw [hgp Q hQ Q' hQ' P hP hQQ' hQP hQ'P, mem_bot] at hm
      exact hx1 hm
    have hoff : ∀ x : Fin 64, rep x ∈ P → rep x ≠ 1 → offFrame x.val = true := by
      intro x hxP hx1
      refine offFrame_of fun p hp => ?_
      simp only [framePairs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hcase hR hP₁ (Ne.symm h1) (Ne.symm hPR) (Ne.symm hP1) (by norm_num) (by norm_num)
          L₀ L₁ x hxP hx1
      · exact hcase hR hP₂ (Ne.symm h2R) (Ne.symm hPR) (Ne.symm hP2) (by norm_num) (by norm_num)
          L₀ L₂ x hxP hx1
      · exact hcase hR hP₃ (Ne.symm h3R) (Ne.symm hPR) (Ne.symm hP3) (by norm_num) (by norm_num)
          L₀ L₃ x hxP hx1
      · exact hcase hP₁ hP₂ (Ne.symm h21) (Ne.symm hP1) (Ne.symm hP2) (by norm_num) (by norm_num)
          L₁ L₂ x hxP hx1
      · exact hcase hP₁ hP₃ (Ne.symm h31) (Ne.symm hP1) (Ne.symm hP3) (by norm_num) (by norm_num)
          L₁ L₃ x hxP hx1
      · exact hcase hP₂ hP₃ (Ne.symm h32) (Ne.symm hP2) (Ne.symm hP3) (by norm_num) (by norm_num)
          L₂ L₃ x hxP hx1
    obtain ⟨u, hu, u', hu', hu1, hu'1, huu'⟩ := exists_two_of_card_four (h4 P hP)
    obtain ⟨a, rfl⟩ := hsurj u (hle P hP hu)
    obtain ⟨b, rfl⟩ := hsurj u' (hle P hP hu')
    have ha0 : a ≠ 0 := fun h => hu1 (by rw [h, hrep0])
    have hb0 : b ≠ 0 := fun h => hu'1 (by rw [h, hrep0])
    have hab : a ≠ b := fun h => huu' (by rw [h])
    have hab1 : rep (xorF a b) ≠ 1 := fun h => huu' (by
      rw [hadd] at h
      exact (eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right (hsq _ (hmem b))))
    have habP : rep (xorF a b) ∈ P := by
      rw [hadd]
      exact mul_mem hu hu'
    rcases oval_comp hS a.2 b.2 (fun h => ha0 (Fin.ext h)) (fun h => hb0 (Fin.ext h))
        (fun h => hab (Fin.ext h)) (hoff a hu hu1) (hoff b hu' hu'1) (hoff _ habP hab1) with
      ⟨ha4, hb4⟩ | ⟨ha5, hb5⟩
    · exact ⟨4, by norm_num, hline P hP 4 (by norm_num) a b ha4 hb4 ha0 hb0 hab hu hu'⟩
    · exact ⟨5, by norm_num, hline P hP 5 (by norm_num) a b ha5 hb5 ha0 hb0 hab hu hu'⟩
  have hpt : ∀ P ∈ pts, ∃ j < 6, ∀ v, rep v ∈ P ↔ v.val ∈ hexaOval[j]! := by
    intro P hP
    by_cases hPR : P = R
    · exact ⟨0, by norm_num, hPR ▸ L₀⟩
    by_cases hP1 : P = P₁
    · exact ⟨1, by norm_num, hP1 ▸ L₁⟩
    by_cases hP2 : P = P₂
    · exact ⟨2, by norm_num, hP2 ▸ L₂⟩
    by_cases hP3 : P = P₃
    · exact ⟨3, by norm_num, hP3 ▸ L₃⟩
    exact hother P hP hPR hP1 hP2 hP3
  have hlines : ∀ j < 6, ∃ P ∈ pts, ∀ v, rep v ∈ P ↔ v.val ∈ hexaOval[j]! := by
    choose jf hjf hjf' using hpt
    let J : ↥pts → Fin 6 := fun P => ⟨jf P.1 P.2, hjf P.1 P.2⟩
    have hJ : Function.Injective J := by
      intro P Q hPQ
      have hj : jf P.1 P.2 = jf Q.1 Q.2 := congrArg Fin.val hPQ
      apply Subtype.ext
      ext x
      constructor
      · intro hx
        obtain ⟨v, rfl⟩ := hsurj x (hle P.1 P.2 hx)
        have h' := (hjf' P.1 P.2 v).1 hx
        rw [hj] at h'
        exact (hjf' Q.1 Q.2 v).2 h'
      · intro hx
        obtain ⟨v, rfl⟩ := hsurj x (hle Q.1 Q.2 hx)
        have h' := (hjf' Q.1 Q.2 v).1 hx
        rw [← hj] at h'
        exact (hjf' P.1 P.2 v).2 h'
    have hJs : Function.Surjective J := (hJ.bijective_of_nat_card_le (by
      rw [h6, Nat.card_eq_fintype_card, Fintype.card_fin])).2
    intro j hj
    obtain ⟨P, hP⟩ := hJs ⟨j, hj⟩
    have hPj : jf P.1 P.2 = j := congrArg Fin.val hP
    refine ⟨P.1, P.2, fun v => ?_⟩
    rw [← hPj]
    exact hjf' P.1 P.2 v
  exact ⟨rep, ⟨hadd, hmem, hinj, hsurj, L₀, hpt, hlines⟩, L₁⟩

theorem exists_hexaCoord (hS : hexaStabCheck = true) {X : Subgroup G}
    (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hsq : ∀ x ∈ X, x * x = 1) (h64 : Nat.card X = 64)
    {pts : Set (Subgroup G)} (hle : ∀ P ∈ pts, P ≤ X) (h4 : ∀ P ∈ pts, Nat.card P = 4)
    (hgp : ∀ P ∈ pts, ∀ P' ∈ pts, ∀ P'' ∈ pts, P ≠ P' → P ≠ P'' → P' ≠ P'' →
      P'' ⊓ (P ⊔ P') = ⊥)
    (h6 : Nat.card pts = 6) {R : Subgroup G} (hR : R ∈ pts) :
    ∃ rep : Fin 64 → G, HexaCoord X R pts rep := by
  classical
  obtain ⟨P₁, hP₁, h1⟩ := exists_mem_not_mem_finset (V := pts) {R}
    (by rw [Finset.card_singleton, h6]; norm_num)
  rw [Finset.mem_singleton] at h1
  obtain ⟨rep, hrep, -⟩ := exists_hexaCoord_two hS hc hsq h64 hle h4 hgp h6 hR hP₁ h1
  exact ⟨rep, hrep⟩

end Coord

end CFSG.ComponentClassification.AS81
