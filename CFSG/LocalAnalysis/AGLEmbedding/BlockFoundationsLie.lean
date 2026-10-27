module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KFactLieOutPrime : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ^ p = 1 →
      x ∉ L ⊔ Subgroup.centralizer (L : Set Y) →
      (∀ T : Subgroup Y, IsSylowTwoOf T L →
          p ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set Y))) ∨
        ((∀ J : Subgroup Y, IsParabolicTwo L J → (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
            J = L) ∧
          ((∃ J : Subgroup Y, IsParabolicTwo L J ∧ J ≠ L ∧
              ∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
            ∃ D : Subgroup Y, D ≤ L ∧ D ≠ ⊥ ∧ ⁅D, D⁆ = D ∧
              D ≤ Subgroup.centralizer ({x} : Set Y)))

@[expose] def KFactLieOutDiagLevi : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, (p = 5 ∨ p = 7) →
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ^ p = 1 →
      x ∉ L ⊔ Subgroup.centralizer (L : Set Y) →
      (∀ T : Subgroup Y, IsSylowTwoOf T L →
          p ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set Y))) →
      (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
      ∃ X : Subgroup Y, X ≤ J ∧ Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
        ∀ φ : ↥X →* alternatingGroup (Fin p), ¬ φ.ker ≤ Subgroup.center ↥X

@[expose] def KFactLieOutRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ E : Subgroup Y, E ≤ Subgroup.normalizer (L : Set Y) → IsElemAbelian p E →
      Nat.card E = p ^ 2 → E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) = ⊥ →
      ∃ X : Subgroup Y, X ≤ J ∧ Open.IsQuasisimple ↥X ∧ p ^ 2 ∣ Nat.card X

theorem kFactBlockOutRankIb_of_lieOutRank (hR : KFactLieOutRank) : KFactBlockOutRankIb := by
  intro Y _ _ L J hL hcl hpar hne hnB p hp hp5 hIb E hEN hE hEc hE1
  obtain ⟨X, hXJ, hXq, hXp⟩ := hR Y L J hL hcl hpar hne hnB p hp hp5 E hEN hE hEc hE1
  exact hIb X hXJ (commutator_eq_self_of_open_isQuasisimple hXq) hXp

theorem kFactBlockOutRankAltIb_of_lieOutRank (hR : KFactLieOutRank) :
    KFactBlockOutRankAltIb := by
  intro Y _ _ L J hL hcl hpar hne hnB p hp hJ E hEN hE hEc hE1
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  obtain ⟨X, hXJ, hXq, hXp⟩ := hR Y L J hL hcl hpar hne hnB p hpp hp5 E hEN hE hEc hE1
  exact not_sq_dvd_card_of_quasisimple_of_altSqC hpp hJ hXJ hXq hXp

end CFSG.AGLEmbedding
