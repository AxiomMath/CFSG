module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

@[expose] def Input11_3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ B : Subgroup X, GLAIsBmax p B → ∀ L : Subgroup X, GLAPComponent p ⊤ L →
      ¬ B ≤ Subgroup.normalizer (L : Set X) → Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) ≠ ⊥

@[expose] def ActsAsTransposition (p : ℕ) {Y : Type*} [Group Y] (T K : Subgroup Y) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ (e : ↥K ≃* ↥(alternatingGroup (Fin (k * p + 2))))
    (τ : Equiv.Perm (Fin (k * p + 2))), τ.IsSwap ∧ Nat.card (inducedAutGroup T K) = 2 ∧
      ActsLike T K e
        (Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin (k * p + 2))) τ))

@[expose] def ActsAsTransvection (p : ℕ) {Y : Type*} [Group Y] (T K : Subgroup Y) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    ((HasFixedPointFreeOrder true n p ∧
        ∃ e : ↥K ≃* ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))),
          Nat.card (inducedAutGroup T K) = 2 ∧
            ActsLikeTransvection (StatedQuadPlus (n + 1) (ZMod 2)) T K e) ∨
      (HasFixedPointFreeOrder false n p ∧
        ∃ e : ↥K ≃* ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)),
          Nat.card (inducedAutGroup T K) = 2 ∧
            ActsLikeTransvection (StatedQuadMinus (n + 1) (ZMod 2) 1 1) T K e))

@[expose] def Input27_9_3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      ∀ B : Subgroup X, IsElemAbelian p B → B ≤ Subgroup.normalizer (K : Set X) →
        ∀ T : Subgroup X, IsPGroup 2 T → T ≤ Subgroup.normalizer (K : Set X) →
          B ≤ Subgroup.normalizer (T : Set X) →
          ((ActsAsTransposition p T K ∧ GLATwoLocalRank p X ≤ pRank p B) ∨
            ActsAsTransvection p T K) →
          ∀ D : Subgroup X, D ≤ B → IsPPlane p D →
            ∃ (𝒟 : Set X) (Kf : X → Subgroup X),
              (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
              (∀ d ∈ 𝒟, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set X)) (Kf d) ∧
                B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧ IsPiGroup p ↥(Kf d) ∧
                ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧
              K = ⨆ d ∈ 𝒟, Kf d

variable {G : Type*} [Group G]

theorem ActsAsTransposition.of_prop95Alpha {p : ℕ} {M D L : Subgroup G}
    (h : Prop95Alpha p M D L) :
    ActsAsTransposition p (barX p M (gammaD D)) (barX p M L) := by
  obtain ⟨k, hk, hLM, e, τ, hτ, hcard, hact, -⟩ := h
  exact ⟨k, hk, e, τ, hτ, hcard, hact⟩

theorem ActsAsTransvection.of_prop95Beta {p : ℕ} {M D L : Subgroup G}
    (h : Prop95Beta p M D L) :
    ActsAsTransvection p (barX p M (gammaD D)) (barX p M L) := by
  obtain ⟨n, hn, ⟨hfp, hLM, e, hcard, hact, -⟩ | ⟨hfp, hLM, e, hcard, hact, -⟩⟩ := h
  · exact ⟨n, hn, Or.inl ⟨hfp, e, hcard, hact⟩⟩
  · exact ⟨n, hn, Or.inr ⟨hfp, e, hcard, hact⟩⟩

end CFSG.LocalAnalysis.GLTheoremB
