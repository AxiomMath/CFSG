module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def U5CaseAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p q : ℕ) (K B' : Subgroup G) (x' : G) (J : Subgroup G), Concl166 G p q K B' x' J →
    evenRank ↥K = 4 → ∀ n : ℕ, Even n → LabelOf J ⟨.twA, 4, n⟩ →
      q ∣ 2 ^ n + 1 ∧
      ∀ (K₀ : Type) [Group K₀] [Finite K₀],
        GLAMarking K₀ (fun lab _ _ _ _ _ => lab = ⟨.twA, 4, n⟩) →
          5 + CFSG.Open.pRank q (Subgroup.center K₀) ≤
            GLATwoLocalRank q K₀ + CFSG.Open.pRank q (⊤ : Subgroup K₀)

@[expose] def U6CaseAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L : Subgroup G) (lab : GLALabel), LabelOf L lab → Odd lab.n →
    ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) → 3 ∣ Nat.card (Subgroup.center ↥L) →
      ∀ (K₀ : Type) [Group K₀] [Finite K₀], GLAMarking K₀ (fun lab' _ _ _ _ _ => lab' = lab) →
        3 ∣ Nat.card (Subgroup.center K₀) →
          GLATwoLocalRank 3 ↥L + 1 + CFSG.Open.pRank 3 (Subgroup.center K₀) ≤
            GLATwoLocalRank 3 K₀ + CFSG.Open.pRank 3 (⊤ : Subgroup K₀)

@[expose] def CentQuasiAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (K : Subgroup G) (y : G) (r : ℕ), r.Prime → r ≠ 2 → IsChev2 K → CFSG.Open.IsQuasisimple ↥K → y ∈ K →
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ orderOf y = q) →
      ∀ Y : Subgroup G, GLAPComponent r (K ⊓ Subgroup.centralizer ({y} : Set G)) Y →
        CFSG.Open.IsQuasisimple ↥Y

end CFSG.LocalAnalysis.GLTheoremA
