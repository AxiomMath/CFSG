module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
  {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem sylow_structure_of_map_eq {U Z : Subgroup G} (hUH : U ≤ H) (hUp : IsPGroup p U)
    (hZU : Z ≤ U) {T₁ : Subgroup L}
    (hUmap : (U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      T₁.map L.subtype)
    (hZmap : (Z.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (T₁ ⊓ Subgroup.centralizer (T₁ : Set L)).map L.subtype)
    {n : ℕ} (hTcard : Nat.card T₁ = p ^ (3 * n))
    (hTcomm : ⁅T₁, T₁⁆ = T₁ ⊓ Subgroup.centralizer (T₁ : Set L))
    (hTpow : ∀ u ∈ T₁, u ^ p = 1) :
    Z = U ⊓ Subgroup.centralizer (U : Set G) ∧ ⁅U, U⁆ = Z ∧ Nat.card U = p ^ (3 * n) ∧
      ∀ u ∈ U, u ^ p = 1 := by
  have hp : p.Prime := Fact.out
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hUN : U ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hUp (glbPrimeCore_coprime p H)
  have hinj : ∀ {A B : Subgroup G}, A ≤ U → B ≤ U →
      (A.subgroupOf H).map π ≤ (B.subgroupOf H).map π → A ≤ B :=
    fun hAU hBU hAB => le_of_map_mk_le_of_isPGroup hUH hUp hAU hBU hAB
  have hCU : ((U ⊓ Subgroup.centralizer (U : Set G)).subgroupOf H).map π =
      (T₁ ⊓ Subgroup.centralizer (T₁ : Set L)).map L.subtype := by
    rw [map_inf_centralizer_eq hUH hUp, hUmap]
    exact (map_subtype_centerOf T₁).symm
  have hZC : Z = U ⊓ Subgroup.centralizer (U : Set G) :=
    le_antisymm (hinj hZU inf_le_left (by rw [hZmap, hCU]))
      (hinj inf_le_left hZU (by rw [hZmap, hCU]))
  have hcomm : ⁅U, U⁆ = Z := by
    have hmap : ((⁅U, U⁆ : Subgroup G).subgroupOf H).map π = (Z.subgroupOf H).map π := by
      rw [hZmap, ← hTcomm, Subgroup.map_commutator, ← hUmap, ← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUH,
        Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self U).trans hUH)]
    exact le_antisymm (hinj (Subgroup.commutator_le_self U) hZU hmap.le)
      (hinj hZU (Subgroup.commutator_le_self U) hmap.ge)
  have hcardU : Nat.card U = p ^ (3 * n) := by
    have h1 : Nat.card ((U.subgroupOf H).map π) = Nat.card (U.subgroupOf H) :=
      card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hUp.comap_subtype
    rw [hUmap, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv,
      Subgroup.card_map_of_injective L.subtype_injective, hTcard] at h1
    exact h1.symm
  have hpowU : ∀ u ∈ U, u ^ p = 1 := by
    intro u hu
    have hπu : π ⟨u, hUH hu⟩ ∈ (U.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
    rw [hUmap] at hπu
    obtain ⟨v, hv, hvu⟩ := hπu
    have h1 : π ⟨u, hUH hu⟩ ^ p = 1 := by
      rw [← hvu, ← map_pow, hTpow v hv, map_one]
    have h2 : ((⟨u, hUH hu⟩ ^ p : H) : G) ∈ GLBPrimeCore p H := by
      rw [mem_glbPrimeCore_iff_mk_eq_one, map_pow, h1]
    have h3 : ((⟨u, hUH hu⟩ ^ p : H) : G) ∈ U ⊓ GLBPrimeCore p H :=
      ⟨by simpa using U.pow_mem hu p, h2⟩
    rw [hUN, Subgroup.mem_bot] at h3
    simpa using h3
  exact ⟨hZC, hcomm, hcardU, hpowU⟩

end CFSG.AGLEmbedding
