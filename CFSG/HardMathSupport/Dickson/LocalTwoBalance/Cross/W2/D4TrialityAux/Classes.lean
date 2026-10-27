module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Transport
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4FieldInner

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section Classes


@[expose] def D4GraphCoreFree : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ), (ε = 1 ∨ ε = 2) →
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) ^ 3 = 1 →
        CoreFreeAt 3 (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε))

@[expose] def D4GraphFieldStdCoreFree : Prop :=
  ∀ (ℓ e : ℕ) [Fact ℓ.Prime], ℓ ≠ 3 → 1 ≤ e → ∀ (K : Type) [Field K] [Finite K] [CharP K ℓ],
    Nat.card K = ℓ ^ (e * 3) → ∀ T : K ≃+* K, (∀ c, T c = c ^ (ℓ ^ e)) →
      ∀ j : ℤ, (j % 3 = 1 ∨ j % 3 = 2) → CoreFreeAt 3 (twistedEntrywiseAut TwistTag.D4 j T)

@[expose] def D4FieldStdCoreFree : Prop :=
  ∀ (ℓ e : ℕ) [Fact ℓ.Prime], ℓ ≠ 3 → 1 ≤ e → ∀ (K : Type) [Field K] [Finite K] [CharP K ℓ],
    Nat.card K = ℓ ^ (e * 3) → ∀ T : K ≃+* K, (∀ c, T c = c ^ (ℓ ^ e)) →
      CoreFreeAt 3 (twistedEntrywiseAut TwistTag.D4 0 T)

theorem d4Graph_zero' {K : Type} [Field K] : d4Graph K 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

theorem d4OuterCoreFree_of_classes (hG : D4GraphCoreFree) (hGF : D4GraphFieldStdCoreFree)
    (hF : D4FieldStdCoreFree) : D4OuterCoreFree := by
  classical
  intro K _ _ hK3 x hx3 hxo
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hn⟩ := FiniteField.card K (ringChar K)
  have hKc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hchar3 : ringChar K ≠ 3 := by
    intro h
    apply hK3
    rw [hKc, h]
    exact dvd_pow_self 3 n.pos.ne'
  obtain ⟨g, a, σ, ε, hε3, hσ3, hxeq⟩ := exists_cube_normal_form_sigma x hx3
  by_cases hσ : σ = 1
  · subst hσ
    have hε : ε = 0 ∨ ε = 1 ∨ ε = 2 := by omega
    rcases hε with rfl | rfl | rfl
    · exfalso
      rw [d4Graph_zero', mul_one] at hxeq
      rw [hxeq] at hx3
      obtain ⟨h, hh⟩ := d4_inner_of_diag hchar3 g a hx3
      exact hxo (by rw [hxeq, hh]; exact ⟨h, rfl⟩)
    · rw [hxeq]
      rw [hxeq] at hx3
      exact hG K hK3 g a 1 (Or.inl rfl) hx3
    · rw [hxeq]
      rw [hxeq] at hx3
      exact hG K hK3 g a 2 (Or.inr rfl) hx3
  · haveI : Fact (ringChar K).Prime := ⟨hpr⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : CharP K (ringChar K) := ringChar.charP K
    have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
    obtain ⟨e, T, he, hef, hT, hσT⟩ :=
      exists_frobenius_eq_or_inv_of_orderOf_three hpr n.pos K hKc σ hord
    have hKe : Nat.card K = ringChar K ^ (e * 3) := by rw [hKc, hef]
    have hK4 : 4 ≤ Nat.card K := by
      rw [hKe]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ ringChar K ^ 2 := Nat.pow_le_pow_left hpr.two_le 2
        _ ≤ ringChar K ^ (e * 3) := Nat.pow_le_pow_right hpr.pos (by omega)
    rcases hσT with hσT | hσT
    · have hα : x = MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K ε) := by
        rw [hxeq, hσT]
      obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hKc hK4 he hef T hT x
        hx3 g a ε hα
      rw [← coreFreeAt_conj_iff x ψ, hψ]
      have hε : ε = 0 ∨ ε = 1 ∨ ε = 2 := by omega
      rcases hε with rfl | rfl | rfl
      · have h0 := hF (ringChar K) e (fun h => hchar3 h) he K hKe T hT
        rw [Nat.cast_zero]
        exact h0
      · exact hGF (ringChar K) e (fun h => hchar3 h) he K hKe T hT 1 (by omega)
      · exact hGF (ringChar K) e (fun h => hchar3 h) he K hKe T hT 2 (by omega)
    · have hα : x = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) := hxeq
      obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hKc hK4 he hef T σ
        hT (by rw [hσT, mul_inv_cancel]) x hx3 g a ε hα
      have hinv : CoreFreeAt 3 x⁻¹ := by
        rw [← coreFreeAt_conj_iff x⁻¹ ψ, hψ]
        have hε : ε = 0 ∨ ε = 1 ∨ ε = 2 := by omega
        rcases hε with rfl | rfl | rfl
        · have h0 := hF (ringChar K) e (fun h => hchar3 h) he K hKe T hT
          rw [Nat.cast_zero, neg_zero]
          exact h0
        · exact hGF (ringChar K) e (fun h => hchar3 h) he K hKe T hT (-1) (by omega)
        · exact hGF (ringChar K) e (fun h => hchar3 h) he K hKe T hT (-2) (by omega)
      simpa using hinv.inv

end Classes

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
