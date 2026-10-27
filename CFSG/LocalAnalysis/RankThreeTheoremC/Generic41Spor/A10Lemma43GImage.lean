module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45Gen
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_T_sylow (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q]
    (ψ : ↥J →* Q) (hψ : Function.Surjective ψ) :
    ∃ S : Sylow 5 Q, (S : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSylJ : CFSG.ABGLocalTools.IsSylowOf 5 (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ
  refine ⟨Tsyl.mapSurjective hψ, ?_⟩
  rw [Sylow.coe_mapSurjective]
  congr 1
  rw [← hTsyl]
  exact (Subgroup.comap_map_eq_self_of_injective J.subtype_injective _).symm

theorem a10_frattini (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q]
    (ψ : ↥J →* Q) (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    {B : Subgroup G} (hBT : B ≤ u3T P x J) {n : Q}
    (hn : n ∈ Subgroup.normalizer (((B.subgroupOf J).map ψ : Subgroup Q) : Set Q)) :
    ∃ (f : G) (hf : f ∈ J), f ∈ Subgroup.normalizer (B : Set G) ∧ ψ ⟨f, hf⟩ = n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hTP : u3T P x J ≤ (P : Subgroup G) := (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hBJ : B ≤ J := hBT.trans hTJ
  have hBp : IsPGroup 5 (B.subgroupOf J) :=
    (P.isPGroup'.to_le (hBT.trans hTP)).comap_subtype
  have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
  have hOcop : Nat.Coprime 5 (Nat.card (rankThreePrimeCore 5 J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime 5 J
  have hcop : Nat.Coprime 5 (Nat.card ψ.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv]
    exact hOcop
  obtain ⟨j, rfl⟩ := hψ n
  obtain ⟨m, hm, hmj⟩ := typeII_frattini_ker ψ hcop hBp hn
  refine ⟨(m : G), m.2, ?_, hmj⟩
  have h1 : m ∈ Subgroup.normalizer ((B.subgroupOf J : Subgroup ↥J) : Set ↥J) := hm
  rw [← Subgroup.subgroupOf_normalizer_eq hBJ] at h1
  exact h1

theorem a10_NJ_le_M (hS : Setting G) (hU0 : FullCoreLocal G) (hX : A10Facts)
    (hc : PointConfig IsA10Type G 5 P M x J) {B : Subgroup G} (hBT : B ≤ u3T P x J) (hB1 : B ≠ ⊥) :
    J ⊓ Subgroup.normalizer (B : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, hTel, hxJ⟩ := plane_T_structure hX.sylow hc
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTP : u3T P x J ≤ (P : Subgroup G) := (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hxP : x ∈ (P : Subgroup G) := hc.generic.1
  have hx5 : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hxJc : ∀ y ∈ J, y * x = x * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hc.le_cent hy)
  have hSP : B ⊔ Subgroup.zpowers x ≤ (P : Subgroup G) :=
    sup_le (hBT.trans hTP) (Subgroup.zpowers_le.mpr hxP)
  have hSp : IsPGroup 5 (B ⊔ Subgroup.zpowers x : Subgroup G) := P.isPGroup'.to_le hSP
  have h2 : 2 ≤ CFSG.Open.pRank 5 (B ⊔ Subgroup.zpowers x : Subgroup G) := by
    obtain ⟨⟨b, hbB⟩, hb1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
    have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
    have hbT : b ∈ u3T P x J := hBT hbB
    have hb5 : b ^ 5 = 1 := hTel.2 b hbT
    have hbJ : b ∈ J := hTJ hbT
    have hzb : Subgroup.zpowers b ≤ J := Subgroup.zpowers_le.mpr hbJ
    have hxb : x ∉ Subgroup.zpowers b := fun h => hxJ (hzb h)
    have hEel : IsElemAbelian 5 (Subgroup.zpowers b ⊔ Subgroup.zpowers x) := by
      refine CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hb5)
        (CFSG.Open.isElemAbelian_zpowers hx5) ?_
      rintro a ⟨m, rfl⟩ c ⟨n, rfl⟩
      exact (Commute.zpow_zpow (hxJc b hbJ : Commute b x) m n).eq
    have hEcard : Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers x : Subgroup G) = 5 ^ 2 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers (by norm_num) (Subgroup.zpowers b) hx5 hxb
        (fun e he => hxJc e (hzb he)), Nat.card_zpowers, orderOf_eq_prime hb5 hb1, sq]
    exact CFSG.SectionRank.le_pRank (by norm_num)
      (sup_le_sup_right (Subgroup.zpowers_le.mpr hbB) _) hEel hEcard
  have hN := normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core hSp (hSP.trans hPM) h2
  intro f hf
  rw [Subgroup.mem_inf] at hf
  have hfn : f ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨n, rfl⟩
    exact (Commute.zpow_left (hxJc f hf.1).symm n).eq
  exact hN (Subgroup.inf_normalizer_le_normalizer_sup B (Subgroup.zpowers x) ⟨hf.2, hfn⟩)

theorem a10_MJ_image (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hX : A10Facts)
    (hXe : A10Ext) (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) (S : Sylow 5 Q) (hSyl : (S : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ) :
    ((M ⊓ J).subgroupOf J).map ψ = A10Gamma Q (S : Subgroup Q) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hOM : rankThreePrimeCore 5 J ≤ M :=
    (u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hc.le_cent hc.cent_le).1
  have hΓ : A10Gamma Q (S : Subgroup Q) ≤ ((M ⊓ J).subgroupOf J).map ψ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro n ⟨Bt, hBtS, hBt1, hn⟩
    have hBsub : ∀ BJ : Subgroup ↥J, (BJ.map J.subtype).subgroupOf J = BJ :=
      fun BJ => Subgroup.comap_map_eq_self_of_injective J.subtype_injective BJ
    set BJ : Subgroup ↥J := (u3T P x J).subgroupOf J ⊓ Bt.comap ψ with hBJ
    set B : Subgroup G := BJ.map J.subtype with hB
    have hBT : B ≤ u3T P x J := by
      rintro _ ⟨b, hb, rfl⟩
      exact hb.1
    have himg : BJ.map ψ = Bt := by
      apply le_antisymm
      · rintro _ ⟨b, hb, rfl⟩
        exact hb.2
      · intro y hy
        have hy' : y ∈ ((u3T P x J).subgroupOf J).map ψ := hSyl ▸ hBtS hy
        obtain ⟨t, ht, rfl⟩ := hy'
        exact ⟨t, ⟨ht, hy⟩, rfl⟩
    have hB1 : B ≠ ⊥ := by
      intro h
      apply hBt1
      have hBJ0 : BJ = ⊥ := by rw [← hBsub BJ, ← hB, h, Subgroup.bot_subgroupOf]
      rw [← himg, hBJ0, Subgroup.map_bot]
    have hnB : n ∈ Subgroup.normalizer (((B.subgroupOf J).map ψ : Subgroup Q) : Set Q) := by
      rw [hB, hBsub BJ, himg]
      exact hn
    obtain ⟨f, hf, hfN, hfn⟩ := a10_frattini hc ψ hψ hker hBT hnB
    have hfM : f ∈ M := a10_NJ_le_M hS hU0 hX hc hBT hB1 ⟨hf, hfN⟩
    exact ⟨⟨f, hf⟩, ⟨hfM, hf⟩, hfn⟩
  have hne : ((M ⊓ J).subgroupOf J).map ψ ≠ ⊤ := by
    intro htop
    apply hc.not_le
    intro j hj
    have hψj : ψ ⟨j, hj⟩ ∈ ((M ⊓ J).subgroupOf J).map ψ := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmj⟩ := hψj
    have hk : m⁻¹ * ⟨j, hj⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmj, inv_mul_cancel]
    rw [hker] at hk
    have h1 : ((m⁻¹ * ⟨j, hj⟩ : ↥J) : G) ∈ rankThreePrimeCore 5 J := hk
    have h2 : (m : G) ∈ M := (Subgroup.mem_inf.1 (show (m : G) ∈ M ⊓ J from hm)).1
    have h3 : j = (m : G) * ((m⁻¹ * ⟨j, hj⟩ : ↥J) : G) := by simp
    rw [h3]
    exact M.mul_mem h2 (hOM h1)
  rcases hXe.gammaMax Q hQ S _ hΓ with h | h
  · exact h
  · exact absurd h hne

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
