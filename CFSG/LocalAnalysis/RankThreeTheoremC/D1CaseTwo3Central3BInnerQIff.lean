module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.RankThreeDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitBasis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_rankThreeGamma_one {p : ℕ} (hp : p.Prime) {E M : Subgroup G}
    (hE : IsElemAbelian p E) (hΓ : rankThreeGamma 1 p E ≤ M) {x : G} (hxE : x ∈ E)
    (hx1 : x ≠ 1) : Subgroup.centralizer ({x} : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime (hE.2 x hxE) hx1
  have hQE : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.2 hxE
  have hQel : IsElemAbelian p (Subgroup.zpowers x) := hE.mono hQE
  have hcard : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  have hrank : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers x) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hQel hcard
  have hN : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ rankThreeGamma 1 p E := by
    rw [rankThreeGamma, GLBCore]
    exact le_sSup ⟨Subgroup.zpowers x, hQE, hrank, rfl⟩
  refine le_trans ?_ (hN.trans hΓ)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hgx : g * x = x * g := (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hconj : ∀ n : ℤ, g * x ^ n * g⁻¹ = x ^ n := fun n => by
    rw [(Commute.zpow_right hgx n).eq, mul_inv_cancel_right]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, (hconj n).symm⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have : g * h * g⁻¹ = g * x ^ n * g⁻¹ := by rw [hconj n]; exact hn.symm
    simpa using this.symm

end CFSG.LocalAnalysis.RankThreeTheoremC
