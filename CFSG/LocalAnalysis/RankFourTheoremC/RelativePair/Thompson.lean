module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Plumb
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ExpAux2
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.thompsonPreFrame {p : ℕ} {P : Sylow p G} {M D R T H V : Subgroup G}
    (hS : ObstructionSetting G) (hD1 : TheoremD1 G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hp : p ∈ rankThreeSigmaA G)
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V)
    (hfacts : OptimalRelPairFacts p M D H V) :
    ThompsonPreFrame p (primeComplementCore (G := H) p) (D.subgroupOf H) := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  obtain ⟨hDab, z, hzD, hz1, hzc, -, hN₀M, -, -⟩ :=
    hS.transitivity_data hD1 hp hd.ext hd.not_le_normalizer hR h13
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  obtain ⟨hDe, hDc⟩ := hd.ext.isElemAbelian_of_isMulCommutative hprime hDab
  have hsylG := hS.isSylowOf_centralizer hD1 hp hd.ext hd.not_le_normalizer hDab hzD hz1 hzc hN₀M
  refine
    { prime := hprime
      odd := hodd
      coprime := primeComplementCore_coprime p
      max := fun N hN hc => normal_coprime_le_primeComplementCore p N hN hc
      elem := thg_isElemAbelian_subgroupOf hDe
      card := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv).trans hDc
      pCore_quot := by exact hfacts.pCore_quotient
      rank_le := thg_card_le hprime hfacts.pRank_eq
      sylow := thg_sylow hprime hDH hsylG
      signalizer := ?_
      join := thg_join hopt.pair.cand.not_coprime }
  intro d hdD hd1
  obtain ⟨K, -, hK2, hK3, hK4⟩ := hfacts.signalizer (d : G) hdD (fun h => hd1 (Subtype.ext h))
  exact thg_signalizer hDH hK2 hK3 hK4

theorem ObstructionSetting.normalizerExponent (hS : ObstructionSetting G) (hD1 : TheoremD1 G)
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D R T : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) : NormalizerExponent p D := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hS.transitivity_data hD1 hp hd.ext hd.not_le_normalizer hR h13
  obtain ⟨hDe, hDc⟩ := hd.ext.isElemAbelian_of_isMulCommutative hprime hDab
  have hsyl := hS.isSylowOf_centralizer hD1 hp hd.ext hd.not_le_normalizer hDab hzD hz1 hzc hN₀M
  obtain ⟨n, hnP, hnD, hnC⟩ := hS.exists_mem_normalizer_not_mem_centralizer hD1 hp
    hd.ext hd.not_le_normalizer hDab hCD
  have hn : ∃ k : ℕ, n ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hnz : n * z = z * n := mem_centralizer_iff.mp hzc n hnP
  obtain ⟨g₁, hg₁N, hg₁M⟩ := IsConcreteLE.not_le_iff_exists.mp hd.ext.obstruction.2.2.2
  have hg₁z : g₁ * z * g₁⁻¹ ∉ zpowers z := by
    intro hmem
    apply hg₁M
    have hz₂p : (g₁ * z * g₁⁻¹) ^ p = 1 := by rw [conj_pow, hzp, mul_one, mul_inv_cancel]
    have hz₂1 : g₁ * z * g₁⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have : z = g₁⁻¹ * (g₁ * z * g₁⁻¹) * g₁ := by group
      rw [this, h]
      group
    have heq : zpowers (g₁ * z * g₁⁻¹) = zpowers z := Subgroup.eq_of_le_of_card_ge
      (zpowers_le.mpr hmem) (by rw [Nat.card_zpowers, Nat.card_zpowers,
        orderOf_eq_prime hzp hz1, orderOf_eq_prime hz₂p hz₂1])
    refine hN₀M ?_
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    exact heq
  obtain ⟨g, hgN, hg⟩ := zje_exists_inv hDe hDc hzD hz1 hn hnD hnz hnC hg₁N hg₁z
  exact zje_exp_of_inverting hodd hDe hDc
    (fun _ hy hyk => zje_mem_of_isSylowOf_centralizer hsyl hy hyk) hgN hg

theorem ObstructionSetting.gl83RelPair2Thompson_of_alt (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (h : GL83RelPair2ThompsonAlt G) : GL83RelPair2Thompson G := by
  intro p hp P M D R T H V hd hopt hfacts
  obtain ⟨L, hL, n, ⟨e⟩⟩ := h p hp P M D R T H V hd hopt hfacts
  have hF := (hS.thompsonPreFrame hD1 hR h13 hp hd hopt hfacts).quotient
  have hL' : CFSG.IsComponent L := (CFSG.isComponent_iff_open L).mpr hL
  obtain ⟨h3, h7⟩ := hF.alt_component hL' e
  subst h7
  exact ⟨h3, L, hL, ⟨e⟩⟩

end CFSG.LocalAnalysis.RankFourTheoremC
