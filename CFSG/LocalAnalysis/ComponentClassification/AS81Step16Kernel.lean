module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Kernel

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

section Products

omit [Finite G] in
theorem exists_mul_of_mem_sup {E X Y : Subgroup G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hXE : X ≤ E) (hYE : Y ≤ E) {z : G} (hz : z ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, z = x * y := by
  have hN : X ≤ normalizer (Y : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy =>
      hE y (hYE hy) x (hXE hx))
  have hz' : z ∈ ((X ⊔ Y : Subgroup G) : Set G) := hz
  rw [coe_mul_of_left_le_normalizer_right X Y hN, Set.mem_mul] at hz'
  obtain ⟨x, hx, y, hy, rfl⟩ := hz'
  exact ⟨x, hx, y, hy, rfl⟩

theorem card_sup_of_inf_eq_bot {E X Y : Subgroup G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hXE : X ≤ E) (hYE : Y ≤ E) (hXY : X ⊓ Y = ⊥) :
    Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y := by
  have hN : Y ≤ normalizer (X : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
      hE x (hXE hx) y (hYE hy))
  have h := card_sup_mul_card_inf hN
  rwa [hXY, Subgroup.card_bot, mul_one] at h

theorem sup_eq_of_inf_eq_bot {E X Y : Subgroup G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hXE : X ≤ E) (hYE : Y ≤ E) (hXY : X ⊓ Y = ⊥) (hcard : Nat.card E = Nat.card X * Nat.card Y) :
    X ⊔ Y = E :=
  Subgroup.eq_of_le_of_card_ge (sup_le hXE hYE)
    (by rw [hcard, card_sup_of_inf_eq_bot hE hXE hYE hXY])

end Products

section Five

variable {E R P Q₁ Q₂ Q₃ : Subgroup G}

theorem mem_centralizer_of_normalizes (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ x ∈ E, x * x = 1) (hE64 : Nat.card E = 64) (hRE : R ≤ E) (hPE : P ≤ E)
    (hQ₁E : Q₁ ≤ E) (hQ₂E : Q₂ ≤ E) (hQ₃E : Q₃ ≤ E) (hR4 : Nat.card R = 4)
    (hP4 : Nat.card P = 4) (hQ₁4 : Nat.card Q₁ = 4) (hQ₂4 : Nat.card Q₂ = 4)
    (hQ₃4 : Nat.card Q₃ = 4) (h₁ : R ⊓ P = ⊥) (h₂ : Q₁ ⊓ (R ⊔ P) = ⊥)
    (h₃ : Q₂ ⊓ (P ⊔ Q₁) = ⊥) (h₄ : Q₂ ⊓ (R ⊔ P) = ⊥) (h₅ : Q₃ ⊓ (P ⊔ Q₁) = ⊥)
    (h₆ : Q₃ ⊓ (R ⊔ P) = ⊥) (h₇ : Q₂ ⊓ (P ⊔ Q₃) = ⊥) (h₈ : Q₂ ⊓ (R ⊔ Q₁) = ⊥) {k : G}
    (hkR : k ∈ normalizer (R : Set G)) (hkP : k ∈ normalizer (P : Set G))
    (hkQ₁ : k ∈ normalizer (Q₁ : Set G)) (hkQ₂ : k ∈ normalizer (Q₂ : Set G))
    (hkQ₃ : k ∈ normalizer (Q₃ : Set G)) {r₀ : G} (hr₀ : r₀ ∈ R) (hr₀1 : r₀ ≠ 1)
    (hfix : k * r₀ * k⁻¹ = r₀) : k ∈ centralizer (E : Set G) := by
  have hRPE : R ⊔ P ≤ E := sup_le hRE hPE
  have hPQ₁E : P ⊔ Q₁ ≤ E := sup_le hPE hQ₁E
  have hRP16 : Nat.card ↥(R ⊔ P) = 16 := by
    rw [card_sup_of_inf_eq_bot hE hRE hPE h₁, hR4, hP4]
  have hPQ₁16 : Nat.card ↥(P ⊔ Q₁) = 16 := by
    have h : P ⊓ Q₁ = ⊥ := by
      rw [eq_bot_iff, ← h₂]
      exact fun x hx => ⟨hx.2, mem_sup_right hx.1⟩
    rw [card_sup_of_inf_eq_bot hE hPE hQ₁E h, hP4, hQ₁4]
  have hE₁ : (R ⊔ P) ⊔ Q₁ = E := by
    refine sup_eq_of_inf_eq_bot hE hRPE hQ₁E (by rw [inf_comm, h₂]) ?_
    rw [hE64, hRP16, hQ₁4]
  have hdec : ∀ e ∈ E, ∃ r ∈ R, ∃ p ∈ P, ∃ t ∈ Q₁, e = r * p * t := by
    intro e he
    rw [← hE₁] at he
    obtain ⟨x, hx, t, ht, rfl⟩ := exists_mul_of_mem_sup hE hRPE hQ₁E he
    obtain ⟨r, hr, p, hp, rfl⟩ := exists_mul_of_mem_sup hE hRE hPE hx
    exact ⟨r, hr, p, hp, t, ht, rfl⟩
  have huniq : ∀ r ∈ R, ∀ p ∈ P, ∀ t ∈ Q₁, ∀ r' ∈ R, ∀ p' ∈ P, ∀ t' ∈ Q₁,
      r * p * t = r' * p' * t' → r = r' ∧ p = p' ∧ t = t' := by
    intro r hr p hp t ht r' hr' p' hp' t' ht' h
    have ht'' : t * t'⁻¹ ∈ Q₁ ⊓ (R ⊔ P) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem ht (inv_mem ht'), ?_⟩
      have e : t * t'⁻¹ = (r * p)⁻¹ * (r' * p') := by
        calc t * t'⁻¹ = (r * p)⁻¹ * (r * p * t) * t'⁻¹ := by group
          _ = (r * p)⁻¹ * (r' * p' * t') * t'⁻¹ := by rw [h]
          _ = (r * p)⁻¹ * (r' * p') := by group
      rw [e]
      exact mul_mem (inv_mem (mul_mem (mem_sup_left hr) (mem_sup_right hp)))
        (mul_mem (mem_sup_left hr') (mem_sup_right hp'))
    rw [h₂, mem_bot, mul_inv_eq_one] at ht''
    subst ht''
    have h' : r * p = r' * p' := mul_right_cancel h
    have hr'' : r'⁻¹ * r ∈ R ⊓ P := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hr') hr, ?_⟩
      have e : r'⁻¹ * r = p' * p⁻¹ := by
        calc r'⁻¹ * r = r'⁻¹ * (r * p) * p⁻¹ := by group
          _ = r'⁻¹ * (r' * p') * p⁻¹ := by rw [h']
          _ = p' * p⁻¹ := by group
      rw [e]
      exact mul_mem hp' (inv_mem hp)
    rw [h₁, mem_bot, inv_mul_eq_one] at hr''
    subst hr''
    exact ⟨rfl, mul_left_cancel h', rfl⟩
  have hkRm : ∀ x ∈ R, k * x * k⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hkR x).mp hx
  have hkPm : ∀ x ∈ P, k * x * k⁻¹ ∈ P := fun x hx => (mem_normalizer_iff.mp hkP x).mp hx
  have hkQ₁m : ∀ x ∈ Q₁, k * x * k⁻¹ ∈ Q₁ := fun x hx => (mem_normalizer_iff.mp hkQ₁ x).mp hx
  have hconj : ∀ r p t : G, k * (r * p * t) * k⁻¹ =
      (k * r * k⁻¹) * (k * p * k⁻¹) * (k * t * k⁻¹) := fun r p t => by group
  have hdetR : ∀ {Q : Subgroup G}, Q ≤ E → Q ⊓ (P ⊔ Q₁) = ⊥ → ∀ r ∈ R, ∀ p ∈ P, ∀ t ∈ Q₁,
      ∀ p' ∈ P, ∀ t' ∈ Q₁, r * p * t ∈ Q → r * p' * t' ∈ Q → p = p' ∧ t = t' := by
    intro Q hQE hQ r hr p hp t ht p' hp' t' ht' hq hq'
    have hmem : (r * p * t)⁻¹ * (r * p' * t') ∈ Q ⊓ (P ⊔ Q₁) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hq) hq', ?_⟩
      have e : (r * p * t)⁻¹ * (r * p' * t') = (p⁻¹ * p') * (t⁻¹ * t') := by
        have h1 := hE r (hRE hr) (p' * t') (mul_mem (hPE hp') (hQ₁E ht'))
        have h2 := hE p⁻¹ (hPE (inv_mem hp)) t⁻¹ (hQ₁E (inv_mem ht))
        have h3 := hE p' (hPE hp') t⁻¹ (hQ₁E (inv_mem ht))
        calc (r * p * t)⁻¹ * (r * p' * t') = t⁻¹ * p⁻¹ * r⁻¹ * (r * (p' * t')) := by group
          _ = t⁻¹ * p⁻¹ * (p' * t') := by group
          _ = (p⁻¹ * t⁻¹) * (p' * t') := by rw [h2]
          _ = p⁻¹ * (t⁻¹ * p') * t' := by group
          _ = p⁻¹ * (p' * t⁻¹) * t' := by rw [h3]
          _ = (p⁻¹ * p') * (t⁻¹ * t') := by group
      rw [e]
      exact mul_mem (mem_sup_left (mul_mem (inv_mem hp) hp'))
        (mem_sup_right (mul_mem (inv_mem ht) ht'))
    rw [hQ, mem_bot, inv_mul_eq_one] at hmem
    have := huniq r hr p hp t ht r hr p' hp' t' ht' hmem
    exact ⟨this.2.1, this.2.2⟩
  have hexR : ∀ {Q : Subgroup G}, Q ≤ E → Nat.card Q = 4 → Q ⊓ (P ⊔ Q₁) = ⊥ →
      ∃ p ∈ P, ∃ t ∈ Q₁, r₀ * p * t ∈ Q := by
    intro Q hQE hQ4 hQ
    have hsup : Q ⊔ (P ⊔ Q₁) = E :=
      sup_eq_of_inf_eq_bot hE hQE hPQ₁E hQ (by rw [hE64, hQ4, hPQ₁16])
    have hr₀E : r₀ ∈ Q ⊔ (P ⊔ Q₁) := hsup ▸ hRE hr₀
    obtain ⟨q, hq, w, hw, hqw⟩ := exists_mul_of_mem_sup hE hQE hPQ₁E hr₀E
    obtain ⟨p, hp, t, ht, rfl⟩ := exists_mul_of_mem_sup hE hPE hQ₁E hw
    refine ⟨p⁻¹, inv_mem hp, t⁻¹, inv_mem ht, ?_⟩
    have e : r₀ * p⁻¹ * t⁻¹ = q := by
      rw [hqw]
      have h1 := hE p (hPE hp) t (hQ₁E ht)
      calc q * (p * t) * p⁻¹ * t⁻¹ = q * (p * t) * (t * p)⁻¹ := by group
        _ = q * (p * t) * (p * t)⁻¹ := by rw [h1]
        _ = q := by group
    rw [e]
    exact hq
  obtain ⟨p₂, hp₂, t₂, ht₂, hq₂⟩ := hexR hQ₂E hQ₂4 h₃
  obtain ⟨p₃, hp₃, t₃, ht₃, hq₃⟩ := hexR hQ₃E hQ₃4 h₅
  have hfixQ : ∀ {Q : Subgroup G}, Q ≤ E → Q ⊓ (P ⊔ Q₁) = ⊥ → k ∈ normalizer (Q : Set G) →
      ∀ p ∈ P, ∀ t ∈ Q₁, r₀ * p * t ∈ Q → k * t * k⁻¹ = t := by
    intro Q hQE hQ hkQ p hp t ht hq
    have hq' : r₀ * (k * p * k⁻¹) * (k * t * k⁻¹) ∈ Q := by
      have := (mem_normalizer_iff.mp hkQ _).mp hq
      rwa [hconj, hfix] at this
    exact (hdetR hQE hQ r₀ hr₀ p hp t ht _ (hkPm p hp) _ (hkQ₁m t ht) hq hq').2.symm
  have hk₂ := hfixQ hQ₂E h₃ hkQ₂ p₂ hp₂ t₂ ht₂ hq₂
  have hk₃ := hfixQ hQ₃E h₅ hkQ₃ p₃ hp₃ t₃ ht₃ hq₃
  have hRP : ∀ {Q : Subgroup G}, Q ⊓ (R ⊔ P) = ⊥ → ∀ p ∈ P, ∀ t ∈ Q₁, r₀ * p * t ∈ Q →
      t ≠ 1 := by
    intro Q hQ p hp t ht hq ht1
    subst ht1
    have hmem : r₀ * p * 1 ∈ Q ⊓ (R ⊔ P) :=
      ⟨hq, by rw [mul_one]; exact mul_mem (mem_sup_left hr₀) (mem_sup_right hp)⟩
    rw [hQ, mem_bot] at hmem
    exact hr₀1 (huniq r₀ hr₀ p hp 1 (one_mem _) 1 (one_mem _) 1 (one_mem _) 1 (one_mem _)
      (by rw [hmem]; group)).1
  have ht₂1 := hRP h₄ p₂ hp₂ t₂ ht₂ hq₂
  have ht₃1 := hRP h₆ p₃ hp₃ t₃ ht₃ hq₃
  have ht₂₃ : t₂ ≠ t₃ := by
    intro h
    subst h
    have hmem : r₀ * p₂ * t₂ ∈ Q₂ ⊓ (P ⊔ Q₃) := by
      refine ⟨hq₂, ?_⟩
      have e : r₀ * p₂ * t₂ = (p₂ * p₃⁻¹) * (r₀ * p₃ * t₂) := by
        have h1 := hE r₀ (hRE hr₀) (p₂ * p₃⁻¹) (hPE (mul_mem hp₂ (inv_mem hp₃)))
        calc r₀ * p₂ * t₂ = r₀ * (p₂ * p₃⁻¹) * p₃ * t₂ := by group
          _ = (p₂ * p₃⁻¹) * r₀ * p₃ * t₂ := by rw [h1]
          _ = (p₂ * p₃⁻¹) * (r₀ * p₃ * t₂) := by group
      rw [e]
      exact mul_mem (mem_sup_left (mul_mem hp₂ (inv_mem hp₃))) (mem_sup_right hq₃)
    rw [h₇, mem_bot] at hmem
    exact hr₀1 (huniq r₀ hr₀ p₂ hp₂ t₂ ht₂ 1 (one_mem _) 1 (one_mem _) 1 (one_mem _)
      (by rw [hmem]; group)).1
  have hkQ₁' : ∀ t ∈ Q₁, k * t * k⁻¹ = t := by
    intro t ht
    rcases eq_or_of_card_four hQ₁4 ht₂ ht₃ ht₂1 ht₃1 ht₂₃ (hE2 t₃ (hQ₁E ht₃)) ht with
      h | h | h | h
    · rw [h, mul_one, mul_inv_cancel]
    · rw [h, hk₂]
    · rw [h, hk₃]
    · rw [h]
      calc k * (t₂ * t₃) * k⁻¹ = (k * t₂ * k⁻¹) * (k * t₃ * k⁻¹) := by group
        _ = t₂ * t₃ := by rw [hk₂, hk₃]
  have hkQ₂' : ∀ q ∈ Q₂, k * q * k⁻¹ = q := by
    intro q hq
    obtain ⟨r, hr, p, hp, t, ht, rfl⟩ := hdec q (hQ₂E hq)
    have hq' : (k * r * k⁻¹) * (k * p * k⁻¹) * t ∈ Q₂ := by
      have := (mem_normalizer_iff.mp hkQ₂ _).mp hq
      rwa [hconj, hkQ₁' t ht] at this
    have hmem : (r * p * t)⁻¹ * ((k * r * k⁻¹) * (k * p * k⁻¹) * t) ∈ Q₂ ⊓ (R ⊔ P) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hq) hq', ?_⟩
      have e : (r * p * t)⁻¹ * ((k * r * k⁻¹) * (k * p * k⁻¹) * t) =
          (r * p)⁻¹ * ((k * r * k⁻¹) * (k * p * k⁻¹)) := by
        have h1 := hE t (hQ₁E ht) ((r * p)⁻¹ * ((k * r * k⁻¹) * (k * p * k⁻¹)))
          (mul_mem (inv_mem (hRPE (mul_mem (mem_sup_left hr) (mem_sup_right hp))))
            (hRPE (mul_mem (mem_sup_left (hkRm r hr)) (mem_sup_right (hkPm p hp)))))
        calc (r * p * t)⁻¹ * ((k * r * k⁻¹) * (k * p * k⁻¹) * t)
            = t⁻¹ * ((r * p)⁻¹ * ((k * r * k⁻¹) * (k * p * k⁻¹)) * t) := by group
          _ = t⁻¹ * (t * ((r * p)⁻¹ * ((k * r * k⁻¹) * (k * p * k⁻¹)))) := by rw [h1]
          _ = (r * p)⁻¹ * ((k * r * k⁻¹) * (k * p * k⁻¹)) := by group
      rw [e]
      exact mul_mem (inv_mem (mul_mem (mem_sup_left hr) (mem_sup_right hp)))
        (mul_mem (mem_sup_left (hkRm r hr)) (mem_sup_right (hkPm p hp)))
    rw [h₄, mem_bot, inv_mul_eq_one] at hmem
    rw [hconj, hkQ₁' t ht]
    exact hmem.symm
  have hkR' : ∀ r ∈ R, k * r * k⁻¹ = r := by
    intro r hr
    have hsup : Q₂ ⊔ (P ⊔ Q₁) = E :=
      sup_eq_of_inf_eq_bot hE hQ₂E hPQ₁E h₃ (by rw [hE64, hQ₂4, hPQ₁16])
    have hrE : r ∈ Q₂ ⊔ (P ⊔ Q₁) := hsup ▸ hRE hr
    obtain ⟨q, hq, w, hw, hqw⟩ := exists_mul_of_mem_sup hE hQ₂E hPQ₁E hrE
    obtain ⟨p, hp, t, ht, rfl⟩ := exists_mul_of_mem_sup hE hPE hQ₁E hw
    have hq' : q = r * p⁻¹ * t⁻¹ := by
      rw [hqw]
      have h1 := hE p (hPE hp) t (hQ₁E ht)
      calc q = q * (p * t) * (t * p)⁻¹ := by rw [← h1]; group
        _ = q * (p * t) * p⁻¹ * t⁻¹ := by group
    have hkq := hkQ₂' q hq
    rw [hq', hconj] at hkq
    exact (huniq _ (hkRm r hr) _ (hkPm _ (inv_mem hp)) _ (hkQ₁m _ (inv_mem ht)) r hr _
      (inv_mem hp) _ (inv_mem ht) hkq).1
  have hRQ₁ : R ⊓ Q₁ = ⊥ := by
    rw [eq_bot_iff, ← h₂]
    exact fun x hx => ⟨hx.2, mem_sup_left hx.1⟩
  have hRQ₁E : R ⊔ Q₁ ≤ E := sup_le hRE hQ₁E
  have hE₂ : (R ⊔ Q₁) ⊔ Q₂ = E := by
    refine sup_eq_of_inf_eq_bot hE hRQ₁E hQ₂E (by rw [inf_comm, h₈]) ?_
    rw [card_sup_of_inf_eq_bot hE hRE hQ₁E hRQ₁, hE64, hR4, hQ₁4, hQ₂4]
  have hle : E ≤ centralizer ({k} : Set G) := by
    rw [← hE₂]
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx <;> rw [mem_centralizer_singleton_iff]
    · have := hkR' x hx
      calc x * k = k * x * k⁻¹ * k := by rw [this]
        _ = k * x := by group
    · have := hkQ₁' x hx
      calc x * k = k * x * k⁻¹ * k := by rw [this]
        _ = k * x := by group
    · have := hkQ₂' x hx
      calc x * k = k * x * k⁻¹ * k := by rw [this]
        _ = k * x := by group
  exact mem_centralizer_iff.mpr fun e he => mem_centralizer_singleton_iff.mp (hle he)

end Five

section Index

theorem relIndex_eq_one_or_three {R C H : Subgroup G} (hRe : IsElemAbelian 2 R)
    (hR4 : Nat.card R = 4) (hHR : H ≤ normalizer (R : Set G))
    (hCR : C ⊓ H ≤ centralizer (R : Set G))
    (hfix : ∀ h ∈ H, ∀ r ∈ R, r ≠ 1 → h * r * h⁻¹ = r → h ∈ C) :
    C.relIndex H = 1 ∨ C.relIndex H = 3 := by
  classical
  have hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hRe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨r₀, hr₀, hr₀1⟩ : ∃ r ∈ R, r ≠ 1 := by
    by_contra h
    push Not at h
    have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).mpr h
    rw [this, Subgroup.card_bot] at hR4
    omega
  have hconjR : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R := fun h hh r hr =>
    (mem_normalizer_iff.mp (hHR hh) r).mp hr
  have hCfix : ∀ c ∈ C, c ∈ H → ∀ r ∈ R, c * r * c⁻¹ = r := fun c hc hcH r hr => by
    rw [← mem_centralizer_iff.mp (hCR ⟨hc, hcH⟩) r hr, mul_inv_cancel_right]
  have hle : C.relIndex H ≤ 3 := by
    let f : ↥H → ↥((R : Set G) \ {1}) := fun h => ⟨h * r₀ * h⁻¹, hconjR h h.2 r₀ hr₀,
      fun h1 => hr₀1 (conj_eq_one_iff.mp h1)⟩
    let φ : ↥H ⧸ C.subgroupOf H → ↥((R : Set G) \ {1}) := Quotient.lift f (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ C.subgroupOf H := QuotientGroup.leftRel_apply.mp hab
      rw [mem_subgroupOf] at hab'
      apply Subtype.ext
      change (a : G) * r₀ * (a : G)⁻¹ = (b : G) * r₀ * (b : G)⁻¹
      have h := hCfix _ hab' (a⁻¹ * b).2 r₀ hr₀
      simp only [coe_mul, coe_inv] at h
      calc (a : G) * r₀ * (a : G)⁻¹
          = (a : G) * ((a : G)⁻¹ * b * r₀ * ((a : G)⁻¹ * b)⁻¹) * (a : G)⁻¹ := by rw [h]
        _ = (b : G) * r₀ * (b : G)⁻¹ := by group)
    have hφ : Function.Injective φ := by
      intro x y hxy
      induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      have h : (a : G) * r₀ * (a : G)⁻¹ = (b : G) * r₀ * (b : G)⁻¹ := congrArg Subtype.val hxy
      apply QuotientGroup.eq.mpr
      rw [mem_subgroupOf]
      refine hfix _ (a⁻¹ * b).2 r₀ hr₀ hr₀1 ?_
      simp only [coe_mul, coe_inv]
      calc (a : G)⁻¹ * b * r₀ * ((a : G)⁻¹ * b)⁻¹
          = (a : G)⁻¹ * ((b : G) * r₀ * (b : G)⁻¹) * a := by group
        _ = (a : G)⁻¹ * ((a : G) * r₀ * (a : G)⁻¹) * a := by rw [h]
        _ = r₀ := by group
    have h1 := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (one_mem R), ← Nat.card_coe_set_eq]
      at h1
    change Nat.card ↥R - 1 ≥ _ at h1
    rw [hR4] at h1
    exact h1
  have hne2 : C.relIndex H ≠ 2 := by
    intro h2
    have h2' : (C.subgroupOf H).index = 2 := h2
    obtain ⟨⟨h, hh⟩, hhC⟩ : ∃ h : ↥H, h ∉ C.subgroupOf H := by
      by_contra hall
      push Not at hall
      have : C.subgroupOf H = ⊤ := eq_top_iff.mpr fun x _ => hall x
      rw [this, Subgroup.index_top] at h2'
      omega
    rw [mem_subgroupOf] at hhC
    have hsq : h * h ∈ C := by
      have := Subgroup.mul_self_mem_of_index_two h2' ⟨h, hh⟩
      rwa [mem_subgroupOf] at this
    set r₁ := h * r₀ * h⁻¹ with hr₁
    have hr₁R : r₁ ∈ R := hconjR h hh r₀ hr₀
    have hr₁r₀ : r₁ ≠ r₀ := fun e => hhC (hfix h hh r₀ hr₀ hr₀1 e)
    have hhr₁ : h * r₁ * h⁻¹ = r₀ := by
      have := hCfix _ hsq (mul_mem hh hh) r₀ hr₀
      calc h * r₁ * h⁻¹ = h * h * r₀ * (h * h)⁻¹ := by rw [hr₁]; group
        _ = r₀ := this
    have hr₀₁ : r₀ * r₁ ≠ 1 := by
      intro e
      apply hr₁r₀
      have h2 : r₀ * r₀ = 1 := by rw [← sq]; exact hRe.2 r₀ hr₀
      calc r₁ = r₀ * r₀ * r₁ := by rw [h2, one_mul]
        _ = r₀ * (r₀ * r₁) := by group
        _ = r₀ := by rw [e, mul_one]
    apply hhC
    refine hfix h hh (r₀ * r₁) (mul_mem hr₀ hr₁R) hr₀₁ ?_
    calc h * (r₀ * r₁) * h⁻¹ = (h * r₀ * h⁻¹) * (h * r₁ * h⁻¹) := by group
      _ = r₁ * r₀ := by rw [← hr₁, hhr₁]
      _ = r₀ * r₁ := hRc r₁ hr₁R r₀ hr₀
  have hpos : C.relIndex H ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card C H
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  omega

end Index

end CFSG.ComponentClassification.AS81
