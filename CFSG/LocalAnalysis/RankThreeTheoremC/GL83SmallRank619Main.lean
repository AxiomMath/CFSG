module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Vi
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Excl
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Four
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem Data619.key {M B H S K : Subgroup G} {z : G} {f : ↥K →* GL32}
    (h : Data619 M B H S K z f) :
    S ≤ K ⊔ pCoreOf 2 H ∧ (pCoreOf 2 H).relIndex S = 4 := by
  by_cases hV : K ⊓ S ≤ pCoreOf 2 H
  · exact (h.false_of_inf_le hV).elim
  · exact h.four_of_not_inf_le hV

private theorem pCoreOf_le_primeCore {H : Subgroup G}
    (hH : H ≤ normalizer (pCoreOf 2 H : Set G)) : pCoreOf 2 H ≤ rankThreePrimeCore 3 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_sSup ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H,
    (normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).mpr hH, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H)
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem prop614Core20_of_core21 (hS : Setting G) (h : GL83SmallRankProp614Core21 G) :
    GL83SmallRankProp614Core20 G := by
  intro P M hsit hsolv he x z hx hz H S hext h3 hHN hmax hOS hS1 hS2 hOM hvi hex
  obtain ⟨K, b, hK, hb⟩ := hex
  have hOeq : rankThreePrimeCore 3 H = pCoreOf 2 H :=
    le_antisymm hvi (pCoreOf_le_primeCore hHN.le)
  obtain ⟨f₀, hf₀s, hf₀k⟩ := hb.kbar
  let f : ↥K →* GL32 := (L32Insp.pslEquiv : PSL(3, ZMod 2) ≃* GL32).toMonoidHom.comp f₀
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : Data619 M (zpowers x ⊔ zpowers z) H S K z f :=
    { charTwo := hS.charTwo
      twoLocal := hext.pair.isTwoLocal
      eq_normalizer := hHN
      B_le := hext.pair.le
      maxInv := hmax
      core_le := hOS
      S_ne_bot := hext.pair.ne_bot
      norm_le := hS1
      char_le := hS2
      K_le := hK.le
      K_normal := hK.normal
      K_not_le := hK.not_le
      K_simple := fun N hNK hN hle => by
        rw [← hOeq] at hle ⊢
        exact hK.maximal N hNK hN hle
      f_surj := (L32Insp.pslEquiv : PSL(3, ZMod 2) ≃* GL32).surjective.comp hf₀s
      f_ker := fun k => by
        rw [← hOeq, ← hf₀k k]
        exact map_eq_one_iff _ (L32Insp.pslEquiv : PSL(3, ZMod 2) ≃* GL32).injective
      z_mem_K := hK.mem (mem_zpowers z)
      z_mem_B := Subgroup.mem_sup_right (mem_zpowers z)
      z_order := orderOf_eq_prime hz.pow_eq_one hz.ne_one }
  obtain ⟨hk1, hk2⟩ := hD.key
  exact h P M hsit hsolv he x z hx hz H S hext h3 hHN hmax hOS hS1 hS2 hOM hvi
    ⟨K, b, hK, hb, hk1, hk2⟩

theorem prop614_of_core21 (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (hK : KFactBlockFactorThreePrime) (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (hK1 : KFactRankTwoUniqueness)
    (hK2 : KFactRankThreeStructure) (h627 : GL83SmallRankProp627 G)
    (h632 : GL83SmallRankProp632 G) (h : GL83SmallRankProp614Core21 G) :
    GL83SmallRankProp614 G :=
  prop614_of_core20 hS hU0 hD2 hK hKF1 hKF2 hK1 hK2 h627 h632 (prop614Core20_of_core21 hS h)

end CFSG.LocalAnalysis.RankThreeTheoremC
