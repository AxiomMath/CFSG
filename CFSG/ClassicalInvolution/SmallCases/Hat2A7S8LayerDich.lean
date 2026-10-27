module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8LayerFam
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Lift
import CFSG.ClassicalInvolution.Q3.Q3T6CoreLift
import CFSG.ClassicalInvolution.Asc77.AscT8Y1Eng
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8.Asc77.T8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem exists_conj_of_map_eq_gen (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N))
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, L = conjSub n K :=
  CFSG.ClassicalInvolution.Q3.Q3T6.exists_conj_of_map_eq_gen hΩ hN hK hL h

end Lift

section Join

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {K J : Subgroup G}

theorem layerJoin_conjSub_eq (hΩ : HypOmegaGen Ω) {n : G} (hn : n ∈ cenZ x) :
    conjSub n (layerJoin Ω x) = layerJoin Ω x := by
  exact CFSG.ClassicalInvolution.Asc77.T8.layerJoin_conjSub_eqE (fun hL hm => layerSet_conj hΩ hL hm) hn

theorem mem_normalizer_oddCoreOf_layerJoin (hΩ : HypOmegaGen Ω) {n : G} (hn : n ∈ cenZ x) :
    n ∈ Subgroup.normalizer (oddCoreOf (layerJoin Ω x) : Set G) :=
  mem_normalizer_oddCore_of_mem_normalizer
    (mem_normalizer_iff_conjSub_eq.mpr (layerJoin_conjSub_eq hΩ hn))

end Join

section Hyp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {Λ : Set (Subgroup G)}

theorem LayerFam.hypOmegaModU (hF : LayerFam Ω x Λ) (hL : LayerHyp Ω x) :
    HypOmegaModU .twoA7 (restrictFamily Λ (famJoin Λ)) where
  conjInvariant := by
    rintro n _ ⟨L, hLΛ, hLY, rfl⟩
    have hnc : (n : G) ∈ cenZ x := hF.famJoin_le_cenZ n.2
    exact ⟨conjSub (n : G) L, hF.inv _ hnc L hLΛ, le_famJoin (hF.inv _ hnc L hLΛ),
      conjSub_subgroupOf _ n L⟩
  classical := by
    rintro _ ⟨L, hLΛ, hLY, rfl⟩
    obtain ⟨u, hu⟩ := hF.cls hL L hLΛ
    exact ⟨⟨u, hLY hu.mem⟩,
      IsClassicalMemberU.of2A7 (hu.subgroupOf hLY hF.famJoin_le_cenZ)⟩
  omega4 := by
    rintro _ ⟨K', hK', hKY, rfl⟩ _ ⟨J', hJ', hJY, rfl⟩ hne
    obtain ⟨K, hK, rfl⟩ := hF.sub hK'
    obtain ⟨J, hJ, rfl⟩ := hF.sub hJ'
    have hKJ : layerRes x K ≠ layerRes x J := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := layerRes_omega4 hL.gen hL.cls hL.sq hK hJ hKJ
    have hcard : Nat.card ↥((layerRes x K).subgroupOf (famJoin Λ) ⊓
        (layerRes x J).subgroupOf (famJoin Λ)) = Nat.card ↥(layerRes x K ⊓ layerRes x J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKY)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h => ?_⟩
    have hle := h2 h
    rw [oddCoreOf_subgroupOf hKY, oddCoreOf_subgroupOf hJY]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅layerRes x K, layerRes x J⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  omega5 := by
    rintro _ ⟨K', hK', hKY, rfl⟩ _ ⟨J', hJ', hJY, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    obtain ⟨K, hK, rfl⟩ := hF.sub hK'
    obtain ⟨J, hJ, rfl⟩ := hF.sub hJ'
    have hKJ : layerRes x K ≠ layerRes x J := fun h => hne (by rw [h])
    have hzK : IsUniqueInvolution (layerRes x K) (z' : G) :=
      isUniqueInvolution_of_subgroupOf hz' hKY
    have hvJ : (v : G) ∈ layerRes x J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ layerRes x J, (v : G) * w = w * (v : G) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp hw'))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := layerRes_omega5 hL.gen hL.cls hL.sq hK hJ hKJ hzK hvJ hnc' hv2'
      (congrArg Subtype.val hvz)
    exact (mem_normalizer_subgroupOf_iff hKY).mp hn

theorem LayerFam.hypOmegaGen (hF : LayerFam Ω x Λ) (hL : LayerHyp Ω x) :
    HypOmegaGen (restrictFamily Λ (famJoin Λ)) :=
  hypOmegaGenU_of_modU (t := .twoA7) trivial (hF.hypOmegaModU hL)

end Hyp

section Dich

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {K J M : Subgroup G}

theorem exists_oddCore_conj_of_layerImg_eq (hL : LayerHyp Ω x) (hK : XMem Ω x K)
    (hJ : XMem Ω x J) (h : layerImg Ω x K = layerImg Ω x J) :
    ∃ n ∈ oddCoreOf (layerJoin Ω x), conjSub n K = J := by
  have hF := LayerFam.layerSet hL.gen hK
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(layerJoin Ω x))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hΛ : HypOmegaGen (restrictFamily (layerSet Ω x) (layerJoin Ω x)) := hF.hypOmegaGen hL
  have hKL : layerRes x K ∈ layerSet Ω x := ⟨K, hK, rfl⟩
  have hJL : layerRes x J ∈ layerSet Ω x := ⟨J, hJ, rfl⟩
  have hK'Λ : (layerRes x K).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hKL, le_layerJoin hKL, rfl⟩
  have hJ'Λ : (layerRes x J).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hJL, le_layerJoin hJL, rfl⟩
  obtain ⟨m, hm, hJ'⟩ := exists_conj_of_map_eq_gen hΛ hodd hK'Λ hJ'Λ h
  have hmy : ((m : ↥(layerJoin Ω x)) : G) ∈ layerJoin Ω x := m.2
  have hmc : ((m : ↥(layerJoin Ω x)) : G) ∈ cenZ x := layerJoin_le_cenZ x hmy
  refine ⟨(m : G), ⟨m, hm, rfl⟩, ?_⟩
  rw [conjSub_subgroupOf] at hJ'
  have h2 := Subgroup.subgroupOf_inj.mp hJ'
  rw [inf_eq_left.mpr (le_layerJoin hJL)] at h2
  have h3 : conjSub (m : G) (layerRes x K) ≤ layerJoin Ω x := by
    rw [layerRes_conj K hmc]
    exact le_layerJoin ⟨_, XMem.conj hL.gen hK hmc, rfl⟩
  rw [inf_eq_left.mpr h3] at h2
  exact XMem.eq_of_layerRes_eq hL.gen hL.cls hL.sq (XMem.conj hL.gen hK hmc) hJ
    ((layerRes_conj K hmc).symm.trans h2.symm)

theorem exists_oddCore_conj_omegaNbr_of_commute (hL : LayerHyp Ω x) (hK : XMem Ω x K)
    (hJ : XMem Ω x J) (hne : layerImg Ω x K ≠ layerImg Ω x J)
    (hcomm : ∀ a ∈ layerRes x K, ∀ b ∈ layerRes x J,
      a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf (layerJoin Ω x)) :
    ∃ n ∈ oddCoreOf (layerJoin Ω x), J ∈ omegaNbr Ω (conjSub n K) := by
  have hΩ : HypOmegaGen Ω := hL.gen
  obtain ⟨zK, hzK, -, arK⟩ := XMem.exists_data hΩ hL.cls hL.sq hK
  obtain ⟨Ra, hRa, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : (⊥ : Subgroup G) ≤ layerRes x J)
  have hRaJ : IsSylow2In Ra J := XMem.isSylow2In_of_layerRes hΩ hL.cls hL.sq hJ hRa
  have hodd : Odd (Nat.card (oddCoreOf (layerJoin Ω x))) := odd_natCard_oddCoreOf _
  have hRaY : Ra ≤ layerJoin Ω x := hRa.1.trans (le_layerJoin ⟨J, hJ, rfl⟩)
  obtain ⟨o, ho, hoK⟩ := exists_nbr_conj hΩ hJ.1 hK.1 hzK (mem_RSet_of_isSylow2In hJ.1 hRaJ)
    hRaJ.1 hodd (fun e he o ho => by
      have hen : e ∈ Subgroup.normalizer (oddCoreOf (layerJoin Ω x) : Set G) :=
        mem_normalizer_oddCoreOf_layerJoin hΩ (layerJoin_le_cenZ x (hRaY he))
      exact (Subgroup.mem_normalizer_iff.mp hen o).mp ho) (fun r hr => by
      have h1 := hcomm zK arK.mem r (hRa.1 hr)
      have hzi : zK⁻¹ = zK := inv_eq_of_mul_eq_one_right hzK.sq
      have e : zK⁻¹ * (r * zK * r⁻¹) = zK * r * zK⁻¹ * r⁻¹ := by rw [hzi]; group
      rw [e]
      exact h1) (fun o ho hoJ => by
      apply hne
      have h1 : layerImg Ω x (conjSub o K) = layerImg Ω x K := layerImg_conj_of_mem_oddCore ho
      rw [← hoJ, h1])
  refine ⟨o, ho, ?_⟩
  exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 (hΩ.conjInvariant o K hK.1) hoK

theorem layer_dichotomy (hL : LayerHyp Ω x) (hK : XMem Ω x K) (hJ : XMem Ω x J) :
    (∃ y ∈ layerJoin Ω x, J = conjSub y K) ∨
      (∃ m ∈ layerJoin Ω x, J ∈ omegaNbr Ω (conjSub m K)) := by
  by_cases heq : layerImg Ω x K = layerImg Ω x J
  · obtain ⟨n, hn, hnK⟩ := exists_oddCore_conj_of_layerImg_eq hL hK hJ heq
    exact Or.inl ⟨n, oddCoreOf_le_self _ hn, hnK.symm⟩
  · have hF := LayerFam.layerSet hL.gen hK
    rcases hF.images_eq_or_commute hL ⟨K, hK, rfl⟩ ⟨J, hJ, rfl⟩ with h | hcomm
    · exact absurd h heq
    · obtain ⟨n, hn, hnb⟩ := exists_oddCore_conj_omegaNbr_of_commute hL hK hJ heq hcomm
      exact Or.inr ⟨n, oddCoreOf_le_self _ hn, hnb⟩

theorem exists_oddCore_conj_mem_dComp (hL : LayerHyp Ω x) (hK : XMem Ω x K) (hM : XMem Ω x M) :
    ∃ ν ∈ oddCoreOf (layerJoin Ω x), conjSub ν M ∈ dComp Ω K := by
  by_cases heq : layerImg Ω x K = layerImg Ω x M
  · obtain ⟨n, hn, hnK⟩ := exists_oddCore_conj_of_layerImg_eq hL hK hM heq
    refine ⟨n⁻¹, (oddCoreOf _).inv_mem hn, ?_⟩
    rw [← hnK, conjSub_inv_conjSub]
    exact Relation.ReflTransGen.refl
  · have hF := LayerFam.layerSet hL.gen hK
    rcases hF.images_eq_or_commute hL ⟨K, hK, rfl⟩ ⟨M, hM, rfl⟩ with h | hcomm
    · exact absurd h heq
    · obtain ⟨n, hn, hnb⟩ := exists_oddCore_conj_omegaNbr_of_commute hL hK hM heq hcomm
      refine ⟨n⁻¹, (oddCoreOf _).inv_mem hn, ?_⟩
      have h1 := omegaNbr_conj hL.gen.conjInvariant hnb n⁻¹
      rw [conjSub_inv_conjSub] at h1
      exact mem_dComp_of_mem_omegaNbr h1

theorem layerJoin_le_sigmaNorm_of_oddCoreOf_le (hL : LayerHyp Ω x) (hK : XMem Ω x K)
    (hO : oddCoreOf (layerJoin Ω x) ≤ sigmaNorm Ω K) : layerJoin Ω x ≤ sigmaNorm Ω K := by
  refine iSup₂_le fun L hLs => ?_
  obtain ⟨M, hM, rfl⟩ := hLs
  obtain ⟨ν, hν, hνM⟩ := exists_oddCore_conj_mem_dComp hL hK hM
  have hMS : M ∈ dComp Ω K := (hO hν M).mpr hνM
  exact (layerRes_le x M).trans ((Subgroup.le_normalizer).trans
    (normalizer_le_sigmaNorm_of_mem hL.gen.conjInvariant hK.1 hMS))

theorem centralizer_le_sigmaNorm_of_layerJoin_le (hL : LayerHyp Ω x) (hK : XMem Ω x K)
    (hY : layerJoin Ω x ≤ sigmaNorm Ω K) :
    Subgroup.centralizer ({x} : Set G) ≤ sigmaNorm Ω K := by
  intro c hc
  have hcz : c ∈ cenZ x := by
    rw [cenZ_eq_centralizer]
    exact hc
  have hKc : XMem Ω x (conjSub c K) := XMem.conj hL.gen hK hcz
  rw [mem_sigmaNorm_iff hL.gen.conjInvariant hK.1]
  rcases layer_dichotomy hL hK hKc with ⟨y, hy, hyc⟩ | ⟨m, hm, hmc⟩
  · rw [hyc]
    exact (mem_sigmaNorm_iff hL.gen.conjInvariant hK.1).1 (hY hy)
  · have hmK := (mem_sigmaNorm_iff hL.gen.conjInvariant hK.1).1 (hY hm)
    exact hmK.trans (Relation.ReflTransGen.single ⟨hKc.1, Or.inl hmc⟩)

end Dich

section Good

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {K : Subgroup G}

theorem XMem.layerRes_cover (hL : LayerHyp Ω x) (h : XMem Ω x K) :
    ∀ y ∈ K, ∃ i ∈ layerRes x K, ∃ n ∈ oddCoreOf K, y = i * n := by
  obtain ⟨z, -, -, ar⟩ := XMem.exists_data hL.gen hL.cls hL.sq h
  exact ar.cover

end Good

end CFSG.ClassicalInvolution.Hat2A7S8.Asc77.T8
