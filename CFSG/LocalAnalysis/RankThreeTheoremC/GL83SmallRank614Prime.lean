module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem prime614_characteristic_map {S N : Subgroup G} (hSN : S ≤ N)
    {C : Subgroup ↥N} (hCS : C ≤ S.subgroupOf N)
    (hC : (C.subgroupOf (S.subgroupOf N)).Characteristic) :
    ((C.map N.subtype).subgroupOf S).Characteristic := by
  set e := Subgroup.subgroupOfEquivOfLe hSN
  have heq : (C.map N.subtype).subgroupOf S =
      (C.subgroupOf (S.subgroupOf N)).map e.toMonoidHom := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨y, hCS hy⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
      apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, Subgroup.subgroupOfEquivOfLe_apply_coe]
      exact hyx
    · rintro ⟨z, hz, hzx⟩
      refine ⟨z, Subgroup.mem_subgroupOf.mp hz, ?_⟩
      have := congrArg Subtype.val hzx
      rw [MulEquiv.coe_toMonoidHom, Subgroup.subgroupOfEquivOfLe_apply_coe] at this
      exact this
  rw [heq, Subgroup.characteristic_iff_map_eq]
  intro ψ
  have h1 := Subgroup.characteristic_iff_map_eq.mp hC ((e.trans ψ).trans e.symm)
  calc ((C.subgroupOf (S.subgroupOf N)).map e.toMonoidHom).map ψ.toMonoidHom
      = ((C.subgroupOf (S.subgroupOf N)).map ((e.trans ψ).trans e.symm).toMonoidHom).map
          e.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
    _ = (C.subgroupOf (S.subgroupOf N)).map e.toMonoidHom := by rw [h1]

omit [Finite G] in
private theorem prime614_centralizer_le (hchar2 : IsCharTwoType G) {H N : Subgroup G}
    (hH : IsTwoLocal H) (hNH : N ≤ H) (hQN : pCoreOf 2 H ≤ N) :
    Subgroup.centralizer (CFSG.pCore 2 ↥N : Set ↥N) ≤ CFSG.pCore 2 ↥N := by
  have hnormal : ((pCoreOf 2 H).subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQN).mpr
      (hNH.trans (localGroup_le_normalizer_pCoreOf 2 H))
  have hle : (pCoreOf 2 H).subgroupOf N ≤ CFSG.pCore 2 ↥N :=
    le_sSup ⟨hnormal, (pCoreOf_isPGroup 2 H).comap_subtype⟩
  intro c hc
  apply hle
  rw [Subgroup.mem_subgroupOf]
  apply hchar2 H hH
  refine Subgroup.mem_inf.mpr ⟨hNH c.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : (⟨q, hQN hq⟩ : ↥N) ∈ CFSG.pCore 2 ↥N := hle (Subgroup.mem_subgroupOf.mpr hq)
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc _ hq')

private theorem prime614_not_two_dvd_index {B H S N : Subgroup G} (hB3 : IsPGroup 3 B)
    (hmax : IsMaxTwoInvariantIn B H S) (hNH : N ≤ H) (hSN : S ≤ N) (hN3 : ¬ 3 ∣ Nat.card N)
    (hBN : B ≤ normalizer (N : Set G)) : ¬ 2 ∣ (S.subgroupOf N).index := by
  obtain ⟨⟨-, hS2, hBS⟩, hSmax⟩ := hmax
  obtain ⟨R, hRsyl, hSR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hB3 hN3 hBN hSN hS2 hBS
  have hRS : R = S := hSmax R ⟨hRsyl.1.trans hNH, hRsyl.2.1, hBR⟩ hSR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn (hRS ▸ hRsyl)
  have hsub : S.subgroupOf N = (Q : Subgroup ↥N) := by
    rw [← hQ]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  rw [hsub]
  exact Q.not_dvd_index

omit [Finite G] in
private theorem prime614_le_of_iSup_eq_top {S N M : Subgroup G} (hSN : S ≤ N)
    (htop : (⨆ (T₀ : Subgroup ↥N) (_ : T₀ ≤ S.subgroupOf N) (_ : T₀ ≠ ⊥)
      (_ : (T₀.subgroupOf (S.subgroupOf N)).Characteristic), normalizer (T₀ : Set ↥N)) = ⊤)
    (hchar : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
      normalizer (S₀ : Set G) ≤ M) : N ≤ M := by
  have hle : (⊤ : Subgroup ↥N) ≤ M.comap N.subtype := by
    rw [← htop]
    refine iSup_le fun T₀ => iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine (Subgroup.le_normalizer_map N.subtype).trans (hchar _ ?_ ?_ ?_)
    · exact Subgroup.map_le_iff_le_comap.mpr h1
    · exact fun hbot => h2 ((Subgroup.map_eq_bot_iff_of_injective T₀ N.subtype_injective).mp hbot)
    · exact prime614_characteristic_map hSN h1 h3
  intro g hg
  exact hle (Subgroup.mem_top ⟨g, hg⟩)

theorem primeCore_le_of_isMaxTwoInvariantIn (hS : Setting G) (hK : KFactBlockFactorThreePrime)
    {B H S M : Subgroup G} (hH : IsTwoLocal H) (hB3 : IsPGroup 3 B) (hBH : B ≤ H)
    (hmax : IsMaxTwoInvariantIn B H S)
    (hchar : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
      normalizer (S₀ : Set G) ≤ M) :
    rankThreePrimeCore 3 H ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup G := hS.simple
  obtain ⟨hOH, hHO, hO3⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 H
  have hSH : S ≤ H := hmax.1.1
  have hS2 : IsPGroup 2 S := hmax.1.2.1
  have hNH : rankThreePrimeCore 3 H ⊔ S ≤ H := sup_le hOH hSH
  have hSN : S ≤ rankThreePrimeCore 3 H ⊔ S := le_sup_right
  have hS3 : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hN3 : ¬ 3 ∣ Nat.card (rankThreePrimeCore 3 H ⊔ S : Subgroup G) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.LocalAnalysis.RankThreeUC.coprime_card_sup_of_le_normalizer (hSH.trans hHO) hO3 hS3)
  have hBN : B ≤ normalizer ((rankThreePrimeCore 3 H ⊔ S : Subgroup G) : Set G) :=
    (le_inf (hBH.trans hHO) hmax.1.2.2).trans (inf_normalizer_le_normalizer_sup _ _)
  have hNtop : rankThreePrimeCore 3 H ⊔ S ≠ ⊤ := fun h =>
    twoLocal_ne_top hS.nonab H hH (top_le_iff.mp (h ▸ hNH))
  have hKN : CFSG.IsKGroup ↥(rankThreePrimeCore 3 H ⊔ S) :=
    (CFSG.ComponentClassification.CatalogueKProper.isKProper_iff_kProper.2
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hS.kProper)) _ hNtop
  have hcent := prime614_centralizer_le hS.charTwo hH hNH
    ((pCoreOf_le_of_isMaxTwoInvariantIn hBH hmax).trans hSN)
  have htop := hK _ hKN hN3 hcent (S.subgroupOf _) hS2.comap_subtype
    (prime614_not_two_dvd_index hB3 hmax hNH hSN hN3 hBN)
  exact le_sup_left.trans (prime614_le_of_iSup_eq_top hSN htop hchar)

theorem prop614Ext_of_core (hS : Setting G) (hK : KFactBlockFactorThreePrime)
    (h : GL83SmallRankProp614Core G) : GL83SmallRankProp614Ext G := by
  intro P M hsit hsolv he x z hx hz H S hext h0 h1 h2 h3 h4 h5
  have hB3 : IsPGroup 3 ↥(zpowers x ⊔ zpowers z) :=
    IsPGroup.of_card (n := 2) (SmallRankPlane.of_situation hS hsit hx hz).card_eq
  exact h P M hsit hsolv he x z hx hz H S hext h0 h1 h2 h3 h4 h5
    (primeCore_le_of_isMaxTwoInvariantIn hS hK hext.pair.isTwoLocal hB3 hext.pair.le h2 h5)

end CFSG.LocalAnalysis.RankThreeTheoremC
