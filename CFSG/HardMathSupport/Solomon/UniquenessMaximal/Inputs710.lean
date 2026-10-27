module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface2

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] noncomputable def oPrimeP {G : Type*} [Group G] (p : ℕ) (L : Subgroup G) : Subgroup G :=
  ((CFSG.Open.pCore p (↥L ⧸ GLAPPrimeCore p ↥L)).comap
    (QuotientGroup.mk' (GLAPPrimeCore p ↥L))).map L.subtype

@[expose] def Input18_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.Open.IsKGroup ↥L → ∀ p : ℕ, p.Prime →
    GLAPComponent p L L → ∀ q : ℕ, q.Prime → ∀ Q : Subgroup G,
      q ∣ Nat.card ↥(⁅L, GLAPPrimeCoreOf p L⁆) → Q ≤ ⁅L, GLAPPrimeCoreOf p L⁆ → IsPGroup q Q →
      ¬ q ∣ Q.relIndex ⁅L, GLAPPrimeCoreOf p L⁆ →
        L ⊓ Subgroup.centralizer (Q : Set G) ≤ oPrimeP p L

@[expose] def Input28_8 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    Subgroup.centralizer (CFSG.Open.pCore 2 X : Set X) ≤ CFSG.Open.pCore 2 X →
    ∀ K T B : Subgroup X, GLAPComponent 3 (⊤ : Subgroup X) K →
      IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) → IsElemAbelian 3 B → IsMaxBInvariantTwo B T →
      barX 3 (⊤ : Subgroup X) K ⊔ barX 3 (⊤ : Subgroup X) T ⊔ barX 3 (⊤ : Subgroup X) B = ⊤ →
      Nat.card ↥(barX 3 (⊤ : Subgroup X) B ⊓ barX 3 (⊤ : Subgroup X) K) = 9 →
        ∃ s : Finset (Fin 3), 2 ≤ s.card ∧ ∀ i ∈ s,
          barX 3 (⊤ : Subgroup X) K ≤
            barX 3 (⊤ : Subgroup X) (Subgroup.normalizer (tripleOf T i : Set X))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
