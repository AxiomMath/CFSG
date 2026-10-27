module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import all CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import all CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem notMem_betaPrimes_of_mem_tauTwoPrimes [Finite G]
    (h₁ : Statements.FNI_outside_sigma_plane_sylow.{u}) (hG : IsOddSimpleMinimal G)
    {M : Subgroup G} (hM : IsCoatom M) {p : ℕ} (hp : p ∈ tauTwoPrimes M) :
    p ∉ betaPrimes G := by
  have hpp : p.Prime := prime_of_mem_tauTwoPrimes hp
  obtain ⟨A, ⟨e⟩⟩ := mem_elementaryAbelianRanks.1
    (show 2 ∈ elementaryAbelianRanks p ↥M from by
      have h := elementaryAbelianPRank_mem_elementaryAbelianRanks (X := ↥M) (p := p) hpp.one_lt
      rwa [elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hp] at h)
  set A' : Subgroup G := A.map M.subtype with hA'
  have hplane : IsElementaryAbelianPlane p A' :=
    ⟨(A.equivMapOfInjective M.subtype M.subtype_injective).symm.trans e⟩
  have hosp : IsOutsideSigmaPlane p M A' :=
    ⟨hM, hpp, notMem_sigmaPrimes_of_mem_tauTwoPrimes hp, Subgroup.map_subtype_le _, hplane⟩
  have hmax : Maximal (IsElementaryAbelianSubgroup p) A' := (h₁ G hG p M A' hosp).2.1
  intro hmem
  obtain ⟨P, hAP⟩ := hmax.prop.isPGroup.exists_le_sylow
  refine not_isPNarrow_of_mem_betaPrimes hmem P ?_
  refine isPNarrow_of_maximal_card_eq (A := A'.subgroupOf (P : Subgroup G)) ?_ ?_
  · refine ⟨hmax.prop.comap (P : Subgroup G).subtype_injective, fun C hC hle => ?_⟩
    have h1 : A' ≤ C.map (P : Subgroup G).subtype := by
      calc A' = (A'.subgroupOf (P : Subgroup G)).map (P : Subgroup G).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hAP).symm
        _ ≤ _ := Subgroup.map_mono hle
    exact Subgroup.map_le_iff_le_comap.1 (hmax.le_of_ge (hC.map _) h1)
  · rw [← Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hAP]
    exact hplane.natCard'

theorem elementaryAbelianPRank_le_one_of_mem_tauTwoPrimes [Finite G]
    (h₁ : Statements.FNI_outside_sigma_plane_sylow.{u}) (hG : IsOddSimpleMinimal G)
    {M T : Subgroup G} (hM : IsCoatom M) (hT : IsCoatom T)
    (hτ : tauTwoPrimes T ⊆ sigmaPrimes M)
    (hβ : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p ∈ sigmaPrimes T → p ∈ betaPrimes ↥T)
    {p : ℕ} (hp : p ∈ tauTwoPrimes M) : elementaryAbelianPRank p ↥T ≤ 1 := by
  have := hG.isSimpleGroup
  have hpp : p.Prime := prime_of_mem_tauTwoPrimes hp
  have hnotbeta : p ∉ betaPrimes G := notMem_betaPrimes_of_mem_tauTwoPrimes h₁ hG hM hp
  by_contra hcon
  by_cases hpT : p ∈ sigmaPrimes T
  ·
    exact hnotbeta ((mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hpT).1
      (hβ p hpp (dvd_natCard_of_mem_tauTwoPrimes hp) hpT))
  ·
    have hle2 : elementaryAbelianPRank p ↥T ≤ 2 := by
      by_contra h3
      exact hpT (mem_sigmaPrimes_of_mem_alphaPrimes hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable_of_ne_top hT (mem_alphaPrimes.2 ⟨hpp, by omega⟩))
    exact notMem_sigmaPrimes_of_mem_tauTwoPrimes hp
      (hτ (mem_tauTwoPrimes_iff.2 ⟨hpp, hpT, by omega⟩))

theorem FTS_auxiliary_opposite_tau_two_rank_one
    (h₁ : Statements.FNI_outside_sigma_plane_sylow.{u}) :
    Statements.FTS_auxiliary_opposite_tau_two_rank_one.{u} := by
  intro G _ _ hG M T hM hT hτ hβ p hp
  exact elementaryAbelianPRank_le_one_of_mem_tauTwoPrimes h₁
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩ hM hT hτ hβ hp

end

end CFSG.FeitThompson.Proofs
