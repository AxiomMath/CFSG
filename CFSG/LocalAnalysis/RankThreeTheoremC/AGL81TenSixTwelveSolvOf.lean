module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenSixOf
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQJZeroInV
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneBar
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenSixXOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace TenSixTwelveSolv

theorem pCoreOf_top_normal {X : Type} [Group X] (p : ℕ) :
    (pCoreOf p (⊤ : Subgroup X)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h := localGroup_le_normalizer_pCoreOf p (⊤ : Subgroup X) (Subgroup.mem_top g)
  exact (Subgroup.mem_normalizer_iff.mp h n).mp hn

theorem commutator_mem_pCoreOf_of_cube {Y I₀ N : Subgroup G} (hsub : IsSubnormal I₀ Y)
    (hcube : ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀, x ^ 3 ∈ pCoreOf 2 Y)
    (hNY : N ≤ Y) (hNn : Y ≤ normalizer (N : Set G)) (hN3 : Nat.Coprime 3 (Nat.card N))
    {b x : G} (hb : b ∈ Y) (hx : x ∈ I₀) (hbx : b * x * b⁻¹ * x⁻¹ ∈ N) :
    b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 Y := by
  have hI₀Y : I₀ ≤ Y := hsub.le
  have hxY : x ∈ Y := hI₀Y hx
  set I := CFSG.ComponentClassification.AS76b.oUpperTwo I₀ with hIdef
  have hII₀ : I ≤ I₀ := oUpperTwo_le_self I₀
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have htop : (Y.subgroupOf Y).map π = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ hπs]
  set Ib0 := (I₀.subgroupOf Y).map π with hIb0
  set Ib := (I.subgroupOf Y).map π with hIb
  have hsubIb0 : IsSubnormal Ib0 ⊤ := by
    have h := (hsub.comap Y.subtype).map π
    rwa [show (Y.comap Y.subtype).map π = ⊤ from htop] at h
  have hsubIb : IsSubnormal Ib ⊤ := by
    have h1 : IsSubnormal I Y :=
      IsSubnormal.step hII₀ ((Subgroup.normal_subgroupOf_iff_le_normalizer hII₀).mpr
        fun n hn => mem_normalizer_oUpperTwo hn) hsub
    have h := (h1.comap Y.subtype).map π
    rwa [show (Y.comap Y.subtype).map π = ⊤ from htop] at h
  have hIb3 : IsPGroup 3 Ib := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    refine ⟨1, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, pow_one, OneMemClass.coe_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp (hcube _ (Subgroup.mem_subgroupOf.mp hw))
    have : v = w ^ 3 := Subtype.ext (by simpa using hvw)
    rw [← this]
    exact hv
  set W := pCoreOf 3 (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) with hW
  haveI hWn : W.Normal := pCoreOf_top_normal 3
  have hIbW : Ib ≤ W := CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal hsubIb hIb3
  set ψ := QuotientGroup.mk' W with hψ
  set D := (pCoreOf 2 (⊤ : Subgroup ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ W))).comap ψ with hD
  haveI hDn : D.Normal := (pCoreOf_top_normal 2).comap ψ
  have hIb0D : Ib0 ≤ D := by
    have h2 : IsPGroup 2 (Ib0.map ψ) := by
      rintro ⟨z, hz⟩
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨a, ha⟩ := TenSixX.exists_pow_two_mem_oUpperTwo (Subgroup.mem_subgroupOf.mp hu)
      refine ⟨a, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      apply hIbW
      refine ⟨u ^ 2 ^ a, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by simpa using ha)
    have hs : IsSubnormal (Ib0.map ψ) ⊤ := by
      have h := hsubIb0.map ψ
      rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    have := CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal hs h2
    intro z hz
    exact this ⟨z, hz, rfl⟩
  set Nb := (N.subgroupOf Y).map π with hNb
  haveI hNbn : Nb.Normal := by
    have : (N.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hNn
    exact Subgroup.Normal.map this π hπs
  have h2 : IsPGroup 2 ↥(D ⊓ Nb) := by
    rintro ⟨z, hzD, hzN⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hzN
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup _) ⟨_, hzD⟩
    have hk1 : ψ (π n) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hk' : (π n) ^ 2 ^ k ∈ W := by
      rw [← map_pow] at hk1
      exact (QuotientGroup.eq_one_iff _).mp hk1
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 (⊤ : Subgroup _) ⟨_, hk'⟩
    have hj' : (π n) ^ (2 ^ k * 3 ^ j) = 1 := by
      rw [pow_mul]
      simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime 3 (orderOf (π n)) := by
      have h1 : orderOf (π n) ∣ orderOf n := orderOf_map_dvd π n
      have h2 : orderOf n ∣ Nat.card N := by
        have := Subgroup.orderOf_dvd_natCard N hnN
        rwa [show orderOf (n : G) = orderOf n from Subgroup.orderOf_coe n] at this
      exact hN3.coprime_dvd_right (h1.trans h2)
    have hdvd : orderOf (π n) ∣ 2 ^ k := by
      have h1 := orderOf_dvd_of_pow_eq_one hj'
      exact (Nat.Coprime.pow_left j hcop).symm.dvd_of_dvd_mul_right h1
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hDN : D ⊓ Nb ≤ CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof.le_pCore_of_normal inferInstance h2
  rw [CFSG.LocalAnalysis.RankThreeUC.AGL81C.pCore_two_quot_eq_bot] at hDN
  have hc : π (⟨b, hb⟩ * ⟨x, hxY⟩ * (⟨b, hb⟩ : Y)⁻¹ * (⟨x, hxY⟩ : Y)⁻¹) ∈ D ⊓ Nb := by
    refine ⟨?_, ⟨_, Subgroup.mem_subgroupOf.mpr hbx, rfl⟩⟩
    have hxD : π ⟨x, hxY⟩ ∈ D := hIb0D ⟨⟨x, hxY⟩, hx, rfl⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact D.mul_mem (hDn.conj_mem _ hxD _) (D.inv_mem hxD)
  have h1 := hDN hc
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

end TenSixTwelveSolv

open TenSixTwelveSolv TenFiveX

theorem agl81TenSixTwelveSolvThreeCfg_holds (h98 : AGL81NineEightFour G) :
    AGL81TenSixTwelveSolvThreeCfg G := by
  intro hS P M H Q K hd L hL I₀ hI₀ ha hIX b hb x hx
  obtain ⟨hO2, hbS⟩ := hI₀.shape.resolve_left ha
  obtain ⟨hV, -, -⟩ := hd.nineEightFour' hS h98
  have hsub2 : IsSubnormal (H ⊓ L) (H ⊓ M) := by
    have h := hL.subnormal.inf H
    rwa [inf_comm L H, inf_comm M H] at h
  have hI₀sub : IsSubnormal I₀ (H ⊓ M) := hI₀.subnormal.trans hsub2
  have hI₀H : I₀ ≤ H := hI₀.le.trans inf_le_left
  obtain ⟨⟨b', hb'H⟩, ⟨hbQ, hbK⟩, rfl⟩ := hb
  have hbQ' : b' ∈ Q := hbQ
  have hbK' : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨b', hb'H⟩ ∈ K := hbK
  have hbY : b' ∈ H ⊓ M := ⟨hb'H, hd.base.1 hbQ'⟩
  set N₀ := primeComplementCore (G := H) 3 with hN₀
  have hNY : N₀.map H.subtype ≤ H ⊓ M := le_inf (Subgroup.map_subtype_le _) hd.primeCore_le
  have hN3 : Nat.Coprime 3 (Nat.card (N₀.map H.subtype)) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact primeComplementCore_coprime 3
  have hxH : x ∈ H := hI₀H hx
  have hc := commutator_mem_of_mem_kbar (hIX hx) hxH hb'H hbK'
  have hbx : b' * x * b'⁻¹ * x⁻¹ ∈ N₀.map H.subtype := by
    refine ⟨_, N₀.inv_mem hc, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul]
    group
  have hcube : ∀ y ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀, y ^ 3 ∈ pCoreOf 2 (H ⊓ M) := by
    intro y hy
    have h1 := IsCZeroMember.cube_mem kFactSUThreeTwoShape_holds hbS y hy
    rw [hO2] at h1
    exact TenFiveX.pCoreOf_le_pCoreOf_of_isSubnormal hsub2 h1
  have := commutator_mem_pCoreOf_of_cube hI₀sub hcube hNY
    ((inf_le_left).trans (TenFiveX.le_normalizer_map_primeComplementCore 3)) hN3 hbY hx hbx
  show b' * x * b'⁻¹ * x⁻¹ ∈ pCoreOf 2 H
  rwa [hV] at this

theorem agl81TenSixTwelveCfg_of' (h1031 : AGL81TenThreeOneAt G) (h912 : AGL81NineTwelveOneCfg G)
    (h98 : AGL81NineEightFour G) : AGL81TenSixTwelveCfg G :=
  agl81TenSixTwelveCfg_of h1031 h912 h98 (agl81TenSixTwelveSolvThreeCfg_holds h98)

end CFSG.LocalAnalysis.RankThreeTheoremC
