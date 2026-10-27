module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup

@[expose] def Foote47CentralInvolution : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
    ∀ (R : Sylow 2 S) (τ : MulAut S), τ * τ = 1 → τ ∉ (MulAut.conj : S →* MulAut S).range →
      (R : Subgroup S).map τ.toMonoidHom = R →
      ∀ c ∈ (R : Subgroup S), orderOf c = 2 → (∀ r ∈ (R : Subgroup S), c * r = r * c) →
        τ c = c →
          MulAut.conj c ∈ ⁅(R : Subgroup S).map (MulAut.conj : S →* MulAut S) ⊔ zpowers τ,
            (R : Subgroup S).map (MulAut.conj : S →* MulAut S) ⊔ zpowers τ⁆

@[expose] def Foote47OuterOrderFour : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
    ∀ (R : Sylow 2 S) (x : MulAut S), (∃ k : ℕ, orderOf x = 2 ^ k) → 4 ≤ orderOf x →
      (∀ n : ℕ, x ^ n ∈ (MulAut.conj : S →* MulAut S).range → x ^ n = 1) →
      (R : Subgroup S).map x.toMonoidHom = R → ∃ r ∈ (R : Subgroup S), x r ≠ r

@[expose] def Foote47FourgroupGeneration : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
    ∀ T : Subgroup (MulAut S), IsPGroup 2 T →
      (∃ F : Subgroup (MulAut S), F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8) →
      (∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) →
      ⨆ (W : Subgroup (MulAut S)) (_ : IsKleinFour W)
        (_ : ∃ F : Subgroup (MulAut S), W ≤ F ∧ F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8),
          ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) = ⊤

end CFSG.ComponentClassification.Foote47
