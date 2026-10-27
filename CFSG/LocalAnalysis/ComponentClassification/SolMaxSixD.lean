module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCM

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem card_support_eq_six_of_not_mem_alternatingGroup {σ : Perm (Fin 9)} (h2 : σ * σ = 1)
    (h5 : 5 ≤ σ.support.card) (hA : σ ∉ alternatingGroup (Fin 9)) : σ.support.card = 6 := by
  have hev : 2 ∣ σ.support.card :=
    two_dvd_card_support_of_pow_two_pow (k := 1) (by rw [pow_one, sq]; exact h2)
  have hle : σ.support.card ≤ 9 := by
    have := Finset.card_le_univ σ.support
    rwa [Fintype.card_fin] at this
  rcases (by omega : σ.support.card = 6 ∨ σ.support.card = 8) with h | h
  · exact h
  · exact absurd (mem_alternatingGroup_fin_nine_of_eight h2 h) hA

@[expose] def SignalizerNineSixDihedralInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
          IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
          IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (∀ y ∈ S, y * t = t * y) →
      (∀ y ∈ Q, orderOf y = 2 →
        centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ x y : X, y ∈ S → y ∉ Q → y ∈ Q.map (MulAut.conj x).toMonoidHom →
        Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥) →
    ∀ s ∈ S, s ∉ Q → ∀ g : X, g⁻¹ * t * g = s →
      g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) → s * s = 1 →
      (∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card) →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 →
      (ρ ⟨s, hsN⟩).support.card = 6 → (∃ y ∈ Q, orderOf y = 2 ∧ y ≠ t) →
      Q ⊓ centralizer ({s} : Set X) ≤ zpowers t →
      (∀ ht₁N : g * t * g⁻¹ ∈ normalizer (M : Set X),
        (ρ ⟨g * t * g⁻¹, ht₁N⟩).support.card = 6) → False

end CFSG.ComponentClassification.SolMax
