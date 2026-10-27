module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_of_bt (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {A K : Subgroup G}
    (hA : IsPGroup p A) (hAK : A ≤ normalizer (K : Set G)) (hK : p.Coprime (Nat.card K)) {u : G}
    (h3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({u} : Set G)))
    (hcon : HasPrimeConstraint (G := centralizer ({u} : Set G)) p)
    (hcont : ∀ x ∈ centralizer ({u} : Set G),
      x ∈ centralizer ((A ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) → orderOf x = p →
        x ∈ A ⊓ centralizer ({u} : Set G)) :
    K ⊓ centralizer ({u} : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hB : IsPGroup p (A ⊓ centralizer ({u} : Set G) : Subgroup G) := hA.to_le inf_le_left
  have hBN : (A ⊓ centralizer ({u} : Set G) : Subgroup G) ≤
      normalizer ((K ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans hAK) (inf_le_right.trans le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hY := CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains hprime hp2 hcon hB
    inf_le_right hcont inf_le_right
    (hK.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) hBN
  exact (hY.trans (glbPrimeCore_le_pPrimeCoreIn p _)).trans
    (pPrimeCoreIn_centralizer_le hS hp hM h3)

end CFSG.LocalAnalysis.RankThreeTheoremC
