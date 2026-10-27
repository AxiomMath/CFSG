module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Tools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem eq_of_centralizer_le {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : IsPGroup 2 A) {t z z₁ : G}
    (ht2 : t * t = 1) (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hC : ∀ a ∈ A, a * t = t * a → a = 1 ∨ a = z) (hz₁2 : z₁ * z₁ = 1)
    (hz : z = z₁ * (t * z₁ * t⁻¹)) (hz1 : z ≠ 1)
    (hZA : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ≤ A)
    (hZ4 : Nat.card ↥(zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹)) = 4) :
    A = zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hz₁A : z₁ ∈ A := hZA (mem_sup_left (mem_zpowers z₁))
  have hz₂A : t * z₁ * t⁻¹ ∈ A := hZA (mem_sup_right (mem_zpowers _))
  have hzA : z ∈ A := hz ▸ mul_mem hz₁A hz₂A
  have hz2 : z * z = 1 := by
    rcases hC (z * z) (mul_mem hzA hzA) (by
        have h1 : t * z * t⁻¹ = z := by
          rw [hz]
          have h2 := hAc _ hz₁A _ hz₂A
          calc t * (z₁ * (t * z₁ * t⁻¹)) * t⁻¹ = (t * z₁ * t⁻¹) * (t * (t * z₁ * t⁻¹) * t⁻¹) := by
                group
            _ = (t * z₁ * t⁻¹) * z₁ := by rw [show t * (t * z₁ * t⁻¹) * t⁻¹ = (t * t) * z₁ *
                (t * t)⁻¹ by group, ht2]; group
            _ = z₁ * (t * z₁ * t⁻¹) := h2.symm
        calc z * z * t = z * (z * t) := by group
          _ = z * (t * z) := by rw [show z * t = t * z by
              calc z * t = (t * z * t⁻¹) * t := by rw [h1]
                _ = t * z := by group]
          _ = (z * t) * z := by group
          _ = (t * z) * z := by rw [show z * t = t * z by
              calc z * t = (t * z * t⁻¹) * t := by rw [h1]
                _ = t * z := by group]
          _ = t * (z * z) := by group) with h1 | h1
    · exact h1
    · exfalso
      apply hz1
      calc z = z * z * z⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
  have hφ : ∀ a ∈ A, a * (t * a * t⁻¹) * t = t * (a * (t * a * t⁻¹)) := by
    intro a ha
    have h1 := hAc _ ha _ (htA a ha)
    calc a * (t * a * t⁻¹) * t = a * t * a := by group
      _ = t * (t⁻¹ * a * t) * a := by group
      _ = t * (t * a * t⁻¹) * a := by rw [hti]
      _ = t * ((t * a * t⁻¹) * a) := by group
      _ = t * (a * (t * a * t⁻¹)) := by rw [← h1]
  have hφz : ∀ a ∈ A, a * (t * a * t⁻¹) = 1 ∨ a * (t * a * t⁻¹) = z := fun a ha =>
    hC _ (mul_mem ha (htA a ha)) (hφ a ha)
  have hexp : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    by_contra ha2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hAp) ⟨a, ha⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      apply ha2
      have h1 : a ^ 2 = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        rw [hk]
        interval_cases k <;> norm_num
      rw [← sq]
      exact h1
    set b := a ^ (2 ^ (k - 2)) with hb
    have hbA : b ∈ A := pow_mem ha _
    have hbo : orderOf b = 4 := by
      rw [hb, orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk,
        Nat.pow_div (by omega) (by norm_num), show k - (k - 2) = 2 by omega]
    have hb4 : b ^ 4 = 1 := by rw [← hbo, pow_orderOf_eq_one]
    have hb21 : b ^ 2 ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hbo] at this
      norm_num at this
    have htb : ∀ c ∈ A, t * c * t⁻¹ = c⁻¹ * (c * (t * c * t⁻¹)) := fun c _ => by group
    have hb2z : b ^ 2 = z := by
      have h1 : (b ^ 2) * t = t * (b ^ 2) := by
        have h2 : t * b ^ 2 * t⁻¹ = b ^ 2 := by
          have h3 : t * b ^ 2 * t⁻¹ = (t * b * t⁻¹) ^ 2 := by rw [sq, sq]; group
          rw [h3, htb b hbA]
          rcases hφz b hbA with h4 | h4 <;> rw [h4]
          · rw [mul_one, inv_pow]
            calc (b ^ 2)⁻¹ = (b ^ 2)⁻¹ * b ^ 4 := by rw [hb4, mul_one]
              _ = b ^ 2 := by group
          · have h5 := hAc _ (inv_mem hbA) _ hzA
            calc (b⁻¹ * z) ^ 2 = b⁻¹ * (z * b⁻¹) * z := by rw [sq]; group
              _ = b⁻¹ * (b⁻¹ * z) * z := by rw [← h5]
              _ = b⁻¹ * b⁻¹ * (z * z) := by group
              _ = b⁻¹ * b⁻¹ * b ^ 4 := by rw [hz2, hb4]
              _ = b ^ 2 := by group
        calc b ^ 2 * t = (t * b ^ 2 * t⁻¹) * t := by rw [h2]
          _ = t * b ^ 2 := by group
      rcases hC _ (pow_mem hbA 2) h1 with h2 | h2
      · exact absurd h2 hb21
      · exact h2
    have hφz₁ : z₁ * (t * z₁ * t⁻¹) = z := hz.symm
    obtain ⟨b', hb'A, hb'2, hb'φ⟩ : ∃ b' ∈ A, b' ^ 2 = z ∧ b' * (t * b' * t⁻¹) = 1 := by
      rcases hφz b hbA with h1 | h1
      · exact ⟨b, hbA, hb2z, h1⟩
      · refine ⟨b * z₁, mul_mem hbA hz₁A, ?_, ?_⟩
        · have h2 := hAc _ hbA _ hz₁A
          calc (b * z₁) ^ 2 = b * (z₁ * b) * z₁ := by rw [sq]; group
            _ = b * (b * z₁) * z₁ := by rw [← h2]
            _ = b ^ 2 * (z₁ * z₁) := by rw [sq]; group
            _ = z := by rw [hz₁2, mul_one, hb2z]
        · have h2 := hAc _ (htA b hbA) _ hz₁A
          calc b * z₁ * (t * (b * z₁) * t⁻¹) = b * (z₁ * (t * b * t⁻¹)) * (t * z₁ * t⁻¹) := by
                group
            _ = b * ((t * b * t⁻¹) * z₁) * (t * z₁ * t⁻¹) := by rw [← h2]
            _ = (b * (t * b * t⁻¹)) * (z₁ * (t * z₁ * t⁻¹)) := by group
            _ = z * z := by rw [h1, hφz₁]
            _ = 1 := hz2
    have hb'z₁ : b' * z₁ * t = t * (b' * z₁) := by
      have hb'i : t * b' * t⁻¹ = b'⁻¹ := eq_inv_of_mul_eq_one_right hb'φ
      have hz₂ : t * z₁ * t⁻¹ = z₁ * z := by
        rw [hz]
        calc t * z₁ * t⁻¹ = (z₁ * z₁) * (t * z₁ * t⁻¹) := by rw [hz₁2, one_mul]
          _ = z₁ * (z₁ * (t * z₁ * t⁻¹)) := by group
      have h1 : t * (b' * z₁) * t⁻¹ = b' * z₁ := by
        have h2 := hAc _ (inv_mem hb'A) _ (mul_mem hz₁A hzA)
        calc t * (b' * z₁) * t⁻¹ = (t * b' * t⁻¹) * (t * z₁ * t⁻¹) := by group
          _ = b'⁻¹ * (z₁ * z) := by rw [hb'i, hz₂]
          _ = (z₁ * z) * b'⁻¹ := h2
          _ = z₁ * b' ^ 2 * b'⁻¹ := by rw [hb'2]
          _ = z₁ * b' := by group
          _ = b' * z₁ := (hAc _ hz₁A _ hb'A)
      calc b' * z₁ * t = (t * (b' * z₁) * t⁻¹) * t := by rw [h1]
        _ = t * (b' * z₁) := by group
    have hb'21 : b' ^ 2 ≠ 1 := by rw [hb'2]; exact hz1
    rcases hC _ (mul_mem hb'A hz₁A) hb'z₁ with h1 | h1
    · apply hb'21
      have h2 : b' = z₁⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2, inv_pow, sq, hz₁2, inv_one]
    · apply hb'21
      have h2 : b' = z * z₁⁻¹ := by
        calc b' = b' * z₁ * z₁⁻¹ := by group
          _ = z * z₁⁻¹ := by rw [h1]
      have h3 := hAc _ hzA _ (inv_mem hz₁A)
      calc b' ^ 2 = z * z₁⁻¹ * (z * z₁⁻¹) := by rw [h2, sq]
        _ = z * (z₁⁻¹ * z) * z₁⁻¹ := by group
        _ = z * (z * z₁⁻¹) * z₁⁻¹ := by rw [← h3]
        _ = (z * z) * (z₁ * z₁)⁻¹ := by group
        _ = 1 := by rw [hz2, hz₁2, inv_one, one_mul]
  have h1 := card_le_of_commutator hAc htA (fun a ha => by
    have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hexp a ha)
    rw [h2]
    exact hφz a ha)
  have h2 : Nat.card ↥(A ⊓ centralizer {t}) ≤ 2 := by
    have h3 : A ⊓ centralizer {t} ≤ zpowers z := by
      intro a ha
      rcases hC a (mem_inf.mp ha).1 (mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2)
        with h4 | h4 <;> rw [h4]
      · exact one_mem _
      · exact mem_zpowers z
    have h4 := Subgroup.card_le_of_le h3
    rwa [card_zpowers_two hz2 hz1] at h4
  exact (eq_of_le_of_card_ge hZA (by rw [hZ4]; omega)).symm

end L415

end CFSG.ComponentClassification.HarrisLit
