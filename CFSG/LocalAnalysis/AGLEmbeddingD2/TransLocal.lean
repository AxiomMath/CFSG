module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransBorel
import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding

@[expose] def D2TransLocalAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* i.Group) → ∀ p, Pp p →
    ∀ (R : Sylow p X) (A : Subgroup X), A ≤ R → IsElemAbelian p A → Nat.card A = p ^ 2 →
    ∃ z : X, z ∈ A ∧ orderOf z = p ∧ z ∈ K ∧
      Subgroup.zpowers z = (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ∧
      (∀ Y : Subgroup X, Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Y →
        Y = Subgroup.normalizer ((R : Subgroup X) : Set X) ∨ Y = ⊤) ∧
      (∀ W : Subgroup X, W ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) →
        Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Subgroup.normalizer (W : Set X) →
        W = ⊥ ∨ z ∈ W) ∧
      Subgroup.normalizer ((R : Subgroup X) : Set X) ⊓ Subgroup.centralizer ({z} : Set X) ≤ R ∧
      Group.IsSolvable (Subgroup.normalizer ((R : Subgroup X) : Set X)) ∧
      (∃ b ∈ (R : Subgroup X), b * z * b⁻¹ = z ∧
        (∀ y ∈ A, b * y * b⁻¹ * y⁻¹ ∈ Subgroup.zpowers z) ∧
        ∃ a₀ ∈ A, ∀ k : ℕ, 0 < k → k < p → b ^ k * a₀ * (b ^ k)⁻¹ ≠ a₀) ∧
      (∃ b ∈ (R : Subgroup X), b ^ p ≠ 1) ∧
      (∃ t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X),
        ∃ e : ℕ, 6 ∣ e ∧ t ^ e * z * (t ^ e)⁻¹ = z⁻¹) ∧
      ∀ T : Sylow p K, IsCyclic T

theorem d2TransBorelAt_of_local {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : D2TransLocalAt i Pp) : D2TransBorelAt i Pp := by
  intro X _ _ p hp R A X₀ K hK he
  obtain ⟨z, hzA, hz, hzK, hcen, hmax, hdich, hC, hsolv, htrans, hexp, ⟨t, htN, e, he6, hinv⟩,
    hcyc⟩ := h X K hK.normal hK.centralizer_eq_bot he p hp R A hK.A_le hK.elem hK.card_A
  have hX₀ := hK.eq_normalizer_of_maximal hmax
  subst hX₀
  exact ⟨z, hzA, hz, hzK, hcen, hdich, hC, hsolv, htrans, hexp, ⟨t, htN, htN, e, he6, hinv⟩, hcyc⟩

end CFSG.AGLEmbeddingD2
