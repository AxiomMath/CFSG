module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

@[expose] def KFact64iiAt (p : ℕ) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (H Q M₀ : Subgroup A) (x z : A),
    CFSG.Open.IsKGroup ↥H → orderOf x = p → orderOf z = p →
    x * z = z * x → x ∉ zpowers z → CFSG.ABGLocalTools.IsSylowOf p Q H →
    zpowers x ⊔ zpowers z ≤ Q → (∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) →
    x ∉ (frattini ↥Q).map Q.subtype →
    (∀ h ∈ H, h * z * h⁻¹ ∈ zpowers x ⊔ zpowers z → h * z * h⁻¹ ∈ zpowers z) →
    Q ≤ M₀ → M₀ ≤ H → normalizer (zpowers z : Set A) ⊓ H ≤ M₀ →
    ¬ H ≤ M₀ ⊔ rankThreePrimeCore p H →
    (∃ K : Subgroup A, PComp p (M₀ ⊔ rankThreePrimeCore p H) H K z) ∧
      ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
        ¬ CFSG.HasNormalPComplement p ↥(H ⊓ centralizer ({b} : Set A))

@[expose] def KFact64iiThree : Prop := KFact64iiAt 3

theorem kFact64ii_iff : KFact64ii ↔ ∀ p : ℕ, p.Prime → p ≠ 2 → KFact64iiAt p := by
  constructor
  · intro h p hp hp2 A _ _ H Q M₀ x z
    exact h A p H Q M₀ x z hp hp2
  · intro h A _ _ p H Q M₀ x z hp hp2
    exact h p hp hp2 A H Q M₀ x z

theorem kFact64iiThree_of_kFact64ii (h : KFact64ii) : KFact64iiThree :=
  kFact64ii_iff.mp h 3 Nat.prime_three (by norm_num)

@[expose] def PieceNotDeltaThree : Prop :=
  KFact64iiThree →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S : Subgroup G), Hyp P M x z H S → OmegaLe x z H →
    ¬ CFSG.HasNormalPComplement 3 ↥(centralizer ({x} : Set G))

@[expose] def PieceCompOmegaThree : Prop :=
  KFact64iiThree →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S : Subgroup G), Hyp P M x z H S → OmegaLe x z H →
      3 ∣ (zpowers x ⊔ zpowers z).relIndex H → ∃ K : Subgroup G, PComp 3 M H K z

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
