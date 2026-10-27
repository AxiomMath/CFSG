module

public import CFSG.Assembly.OddCoreElimination.Nonisolated
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup

namespace RankFourCoverage

variable {G : Type*} [Group G]

theorem le_centralizer_of_isElemAbelian {V : Subgroup G} (hV : CFSG.Assembly.IsElemAbelian 2 V) :
    V ≤ centralizer (V : Set G) := by
  intro v hv
  rw [mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val (hV.1.is_comm.comm (⟨w, hw⟩ : V) ⟨v, hv⟩)

variable [Finite G]

theorem exists_eight_of_three_le {V H : Subgroup G} (hV : CFSG.Assembly.IsElemAbelian 2 V)
    (hV4 : Nat.card V = 4) (h3 : 3 ≤ CFSG.Assembly.pRank 2 (H ⊓ centralizer (V : Set G))) :
    ∃ E : Subgroup G, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ V ≤ E := by
  obtain ⟨B, hBle, hB, hBcard⟩ :=
    CFSG.SectionRank.exists_pRank one_lt_two (H ⊓ centralizer (V : Set G))
  have hB8 : 8 ≤ Nat.card B := by
    rw [hBcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (H ⊓ centralizer (V : Set G)) :=
        Nat.pow_le_pow_right (by norm_num) h3
  have hBV : ¬ B ≤ V := fun h => by
    have := card_le_of_le h
    omega
  obtain ⟨w, hwB, hwV⟩ := IsConcreteLE.not_le_iff_exists.mp hBV
  have hw1 : w ≠ 1 := fun h => hwV (h ▸ one_mem V)
  have hw2 : orderOf w = 2 := orderOf_eq_prime (hB.2 w hwB) hw1
  have hwC : w ∈ centralizer (V : Set G) := (mem_inf.mp (hBle hwB)).2
  obtain ⟨E, hVE, -, hE, hE8, -⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (firstRank := 2) (secondRank := 1) V (zpowers w) hV
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary w hw2) (by rw [hV4]; norm_num)
      (by rw [Nat.card_zpowers, hw2]; norm_num)
      (le_centralizer_iff.mpr (zpowers_le.mpr hwC))
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint V w hw2 hwV)
  exact ⟨E, hE, by rw [hE8]; norm_num, hVE⟩

end RankFourCoverage

open RankFourCoverage

theorem perfect_four_rank_three_coverage (G : Type) [Group G] [Finite G]
    (hperf : commutator G = ⊤) (hrank : 3 ≤ CFSG.Assembly.twoRank G) (V : Subgroup G)
    (hV : CFSG.Assembly.IsElemAbelian 2 V) (hV4 : Nat.card V = 4) :
    ∃ E : Subgroup G, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ V ≤ E := by
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  obtain ⟨S, hVS⟩ := hVp.exists_le_sylow
  by_cases h3 : 3 ≤ CFSG.Assembly.pRank 2 ((S : Subgroup G) ⊓ centralizer (V : Set G))
  · exact exists_eight_of_three_le hV hV4 h3
  have hge : 2 ≤ CFSG.Assembly.pRank 2 ((S : Subgroup G) ⊓ centralizer (V : Set G)) :=
    CFSG.SectionRank.le_pRank (p := 2) one_lt_two
      (le_inf hVS (le_centralizer_of_isElemAbelian hV)) hV (by rw [hV4]; norm_num)
  obtain ⟨g, -, hg3⟩ :=
    CFSG.Assembly.Dichotomy.nonisolatedConjugate G hperf hrank S V hVS hV hV4 (by omega)
  have hVg : CFSG.Assembly.IsElemAbelian 2 (V.map (MulAut.conj g⁻¹).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hV _
  have hVg4 : Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) = 4 := by
    rw [card_map_of_injective (MulEquiv.injective _), hV4]
  obtain ⟨E₁, hE₁, hE₁8, hVE₁⟩ := exists_eight_of_three_le hVg hVg4 hg3
  refine ⟨E₁.map (MulAut.conj g).toMonoidHom, CFSG.SectionRank.isElemAbelian_map hE₁ _,
    by rw [card_map_of_injective (MulEquiv.injective _), hE₁8], fun v hv => ?_⟩
  refine ⟨g⁻¹ * v * g, hVE₁ ⟨v, hv, ?_⟩, ?_⟩
  · show g⁻¹ * v * g⁻¹⁻¹ = g⁻¹ * v * g
    rw [inv_inv]
  · show g * (g⁻¹ * v * g) * g⁻¹ = v
    group

end CFSG.ComponentClassification.UnbalancedGS
