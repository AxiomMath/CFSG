module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.AuxiliaryOppositeTauTwoRankOne

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem elementaryAbelianPRank_inf_normalizer_le_one_of_mem_tauTwoPrimes [Fintype G]
    (h₁ : Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (hG : IsOddOrderMinimalSimple G) {M L : Subgroup G} (hM : IsCoatom M) (hL : IsCoatom L)
    (hnc : ∀ g : G, L ≠ conjSubgroup M g) {E : Subgroup G}
    (hE : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    {p : ℕ} (hp : p.Prime) (hpE : p ∣ Nat.card ↥E) (hpτ : p ∈ tauTwoPrimes L)
    {q : ℕ} (hq : q.Prime) (hqσ : q ∈ sigmaPrimes M)
    {Y : Subgroup G} (hYL : Y ≤ L) (hY : Y ≠ ⊥) (hYq : IsPGroup q ↥Y) :
    elementaryAbelianPRank p ↥(L ⊓ normalizer (Y : Set G)) ≤ 1 := by
  have hβ : p ∉ betaPrimes G :=
    notMem_betaPrimes_of_mem_tauTwoPrimes h₂
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩ hL hpτ
  exact h₁ G hG M L hM hL hnc E hE p hp hpE hβ q hq hqσ Y hYL hY hYq

theorem FBG_rank_two_complement_prime_normalizer_bound
    (h₁ : Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u}) :
    Statements.FBG_rank_two_complement_prime_normalizer_bound.{u} := by
  intro G _ _ hG M L hM hL hnc E hE p hp hpE _hpL hpτ q hq hqσ Y hYL hY hYq
  exact elementaryAbelianPRank_inf_normalizer_le_one_of_mem_tauTwoPrimes h₁ h₂ hG hM hL hnc hE hp
    hpE hpτ hq hqσ hYL hY hYq

end

end CFSG.FeitThompson.Proofs
