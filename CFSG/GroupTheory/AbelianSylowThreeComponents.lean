module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.CyclicAutOmega
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.Foundations.SteinbergCADefinitionNodes

public section
namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

private lemma eq_top_of_map_mk'_eq_top {X : Type*} [Group X] {O K : Subgroup X} [O.Normal]
    (hcomap : (K.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O) = K)
    (h : K.map (QuotientGroup.mk' O) = ⊤) : K = ⊤ := by
  rw [← hcomap, h, Subgroup.comap_top]

private lemma layer_le_map_of_disjoint_normalClosures {X : Type*} [Group X] [Finite X]
    {O K Q D₁ D₂ : Subgroup X} [O.Normal]
    (hcopO : ¬ 3 ∣ Nat.card O)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤)
    (hD₁ : D₁ ≤ Q) (hD₂ : D₂ ≤ Q)
    (hC₁ : Subgroup.centralizer (D₁ : Set X) ≤ K)
    (hC₂ : Subgroup.centralizer (D₂ : Set X) ≤ K)
    (hdisj : (Subgroup.normalClosure (D₁ : Set X)).map (QuotientGroup.mk' O) ⊓
      (Subgroup.normalClosure (D₂ : Set X)).map (QuotientGroup.mk' O) = ⊥) :
    CFSG.layer (X ⧸ O) ≤ K.map (QuotientGroup.mk' O) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  let Kbar : Subgroup (X ⧸ O) := K.map π
  let N₁ : Subgroup (X ⧸ O) := (Subgroup.normalClosure (D₁ : Set X)).map π
  let N₂ : Subgroup (X ⧸ O) := (Subgroup.normalClosure (D₂ : Set X)).map π
  have hN₁disj : N₁ ⊓ N₂ = ⊥ := by
    simpa [N₁, N₂, π] using hdisj
  have hN₁normal : N₁.Normal :=
    Subgroup.Normal.map Subgroup.normalClosure_normal π (QuotientGroup.mk'_surjective O)
  have hN₂normal : N₂.Normal :=
    Subgroup.Normal.map Subgroup.normalClosure_normal π (QuotientGroup.mk'_surjective O)
  rw [CFSG.layer.eq_sSup]
  refine sSup_le ?_
  intro J hJ
  have hJne : J ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot J).mp (CFSG.LocalCores.isQuasisimple_nontrivial hJ.1)
  have hnotboth : ¬ (J ≤ N₁ ∧ J ≤ N₂) := by
    rintro ⟨h1, h2⟩
    have hJbot : J ≤ (⊥ : Subgroup (X ⧸ O)) := by
      rw [← hN₁disj]
      exact le_inf h1 h2
    exact hJne (le_bot_iff.mp hJbot)
  have hJ' : CFSG.GorensteinWalter.IsComponentOf J ⊤ := by
    obtain ⟨hq, hsn⟩ := hJ
    exact ⟨le_top, Subgroup.IsSubnormal.comap (⊤ : Subgroup (X ⧸ O)).subtype hsn,
      (CFSG.Foundations.SteinbergCA.quasisimple_iff J).2.2.2.mp hq⟩
  have hcomm : ⁅J, D₁.map π⁆ = ⊥ ∨ ⁅J, D₂.map π⁆ = ⊥ := by
    by_cases h1 : J ≤ N₁
    · right
      have h2 : ¬ J ≤ N₂ := fun h2 => hnotboth ⟨h1, h2⟩
      have hcomm₂ : ⁅J, N₂⁆ = ⊥ :=
        (CFSG.GorensteinWalter.component_le_or_commutator_eq_bot_of_normal
          hJ' hN₂normal).resolve_left h2
      exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl
        (Subgroup.map_mono (le_normalClosure (H := D₂)))).trans hcomm₂.le)
    · left
      have hcomm₁ : ⁅J, N₁⁆ = ⊥ :=
        (CFSG.GorensteinWalter.component_le_or_commutator_eq_bot_of_normal
          hJ' hN₁normal).resolve_left h1
      exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl
        (Subgroup.map_mono (le_normalClosure (H := D₁)))).trans hcomm₁.le)
  rcases hcomm with hcomm | hcomm
  · have hcen : J ≤ Subgroup.centralizer ((D₁.map π : Subgroup (X ⧸ O)) : Set (X ⧸ O)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
    have hcen_eq : Subgroup.centralizer ((D₁.map π : Subgroup (X ⧸ O)) : Set (X ⧸ O)) =
        (Subgroup.centralizer (D₁ : Set X)).map π :=
      CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hcopO (hQ.isPGroup.to_le hD₁)
    exact hcen.trans (hcen_eq ▸ Subgroup.map_mono hC₁)
  · have hcen : J ≤ Subgroup.centralizer ((D₂.map π : Subgroup (X ⧸ O)) : Set (X ⧸ O)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
    have hcen_eq : Subgroup.centralizer ((D₂.map π : Subgroup (X ⧸ O)) : Set (X ⧸ O)) =
        (Subgroup.centralizer (D₂ : Set X)).map π :=
      CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hcopO (hQ.isPGroup.to_le hD₂)
    exact hcen.trans (hcen_eq ▸ Subgroup.map_mono hC₂)

private lemma generalizedFitting_le_map {X : Type*} [Group X] [Finite X]
    {O K Q : Subgroup X} [O.Normal]
    (hcore : CFSG.pPrimeCore 3 (X ⧸ O) = ⊥)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤) (hQK : Q ≤ K)
    (hE : CFSG.layer (X ⧸ O) ≤ K.map (QuotientGroup.mk' O)) :
    CFSG.generalizedFitting (X ⧸ O) ≤ K.map (QuotientGroup.mk' O) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  let Y := X ⧸ O
  let Kbar : Subgroup Y := K.map π
  have hindex : ¬ 3 ∣ Q.index := by
    have := (CFSG.ABGLocalTools.isSylowOf_iff.mp hQ).2.2
    simpa [Subgroup.relIndex_top_right] using this
  let QX : Sylow 3 X := hQ.isPGroup.toSylow hindex
  have hQXcoe : (QX : Subgroup X) = Q := rfl
  let Sbar : Sylow 3 Y := Sylow.mapSurjective (QuotientGroup.mk'_surjective O) QX
  have hSbarcoe : (Sbar : Subgroup Y) = Q.map π := by
    change (Sylow.mapSurjective (QuotientGroup.mk'_surjective O) QX : Subgroup Y) = _
    rw [Sylow.coe_mapSurjective, hQXcoe]
  let Qbar : Subgroup Y := Q.map π
  have hpCore_le_Qbar : CFSG.pCore 3 Y ≤ Qbar := by
    have h := IsPGroup.le_sylow_of_normal (p := 3) (N := CFSG.pCore 3 Y)
      (CFSG.pCore_isPGroup) Sbar
    simpa [hSbarcoe, Qbar] using h
  have hFit_le : CFSG.fittingSubgroup Y ≤ Kbar := by
    rw [CFSG.Fitting_eq_pcore Y 3 hcore]
    exact hpCore_le_Qbar.trans (Subgroup.map_mono hQK)
  have hFstar_le : CFSG.generalizedFitting Y ≤ Kbar := by
    change CFSG.fittingSubgroup Y ⊔ CFSG.layer Y ≤ Kbar
    exact sup_le hFit_le hE
  exact hFstar_le

private lemma preimage_generalizedFitting_frattini {X : Type*} [Group X] [Finite X]
    {O K Q F S : Subgroup X} [O.Normal]
    (hcomap : (K.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O) = K)
    (hF : F = (CFSG.generalizedFitting (X ⧸ O)).comap (QuotientGroup.mk' O))
    (hS : S = Q ⊓ F)
    (hFstar : CFSG.generalizedFitting (X ⧸ O) ≤ K.map (QuotientGroup.mk' O))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤) :
    F ≤ K ∧ CFSG.ABGLocalTools.IsSylowOf 3 S F ∧
      F ⊔ Subgroup.normalizer (S : Set X) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF_le_K : F ≤ K := by
    rw [hF]
    exact (Subgroup.comap_mono hFstar).trans (le_of_eq hcomap)
  have hFnormal : F.Normal := by
    rw [hF]
    exact (CFSG.LocalCores.generalized_fitting_characteristic (G := X ⧸ O)).2.comap _
  letI : F.Normal := hFnormal
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S F := by
    rw [hS]
    exact hQ.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  obtain ⟨P, hP⟩ := hS_sylow.exists_sylow_eq_subgroupOf
  have hPmap : (P : Subgroup ↥F).map F.subtype = S := by
    rw [hP, Subgroup.map_subgroupOf_eq_of_le (hS.symm ▸ inf_le_right)]
  have hfratt : Subgroup.normalizer (S : Set X) ⊔ F = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top P
    rwa [hPmap] at h
  refine ⟨hF_le_K, hS_sylow, ?_⟩
  rw [sup_comm, hfratt]

private lemma map_eq_top_of_exists_omega_not_le {X : Type*} [Group X]
    {O K Q F S : Subgroup X} [O.Normal] {z : X}
    (hF_le : F ≤ K)
    (hX_eq : F ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (hSQ : S ≤ Q)
    (hQab : IsMulCommutative ↥Q)
    (hN : ∀ U : Subgroup X, U ≤ Q → (∀ u ∈ U, u ^ 3 = 1) →
      ¬ U ≤ Subgroup.zpowers z → Subgroup.normalizer (U : Set X) ≤ K)
    (hex : ∃ s ∈ S, s ^ 3 = 1 ∧ s ∉ Subgroup.zpowers z) :
    K.map (QuotientGroup.mk' O) = ⊤ := by
  classical
  obtain ⟨s, hsS, hs3, hsz⟩ := hex
  have hcommS : ∀ a b : ↥S, a * b = b * a := by
    intro a b
    apply Subtype.ext
    have := hQab.is_comm.comm (⟨a.1, hSQ a.2⟩ : ↥Q) (⟨b.1, hSQ b.2⟩ : ↥Q)
    simpa using congrArg (fun t : ↥Q => (t : X)) this
  let U : Subgroup X := (CFSG.omega₁ ↥S (p := 3)).map S.subtype
  have hUQ : U ≤ Q := (Subgroup.map_subtype_le _).trans hSQ
  have hUexp : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hu
    have hs'3 : (s' : ↥S) ^ 3 = 1 := (CFSG.mem_omega₁_iff_of_comm hcommS).mp hs'
    simpa using congrArg (fun t : ↥S => (t : X)) hs'3
  have hUnotz : ¬ U ≤ Subgroup.zpowers z := by
    intro hle
    have hsOmega : (⟨s, hsS⟩ : ↥S) ∈ CFSG.omega₁ ↥S (p := 3) :=
      (CFSG.mem_omega₁_iff_of_comm hcommS).mpr (Subtype.ext (by simpa using hs3))
    have hsin : s ∈ U := Subgroup.mem_map.mpr ⟨⟨s, hsS⟩, hsOmega, rfl⟩
    exact hsz (hle hsin)
  have hNS_le : Subgroup.normalizer (S : Set X) ≤ K :=
    (CFSG.GroupTheory.normalizer_le_normalizer_omega₁_map_subtype S).trans
      (hN U hUQ hUexp hUnotz)
  have htop : (⊤ : Subgroup X) ≤ K := by
    rw [← hX_eq]
    exact sup_le hF_le hNS_le
  have hKtop : K = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    exact htop (Subgroup.mem_top x)
  rw [hKtop]
  exact Subgroup.map_top_of_surjective (QuotientGroup.mk' O)
    (QuotientGroup.mk'_surjective O)

private lemma mk'_center_order_three_data {X : Type*} [Group X] [Finite X]
    {O : Subgroup X} [O.Normal] {z : X}
    (hcopO : ¬ 3 ∣ Nat.card O) (hzZ : z ∈ Subgroup.center X) (hz : orderOf z = 3) :
    QuotientGroup.mk' O z ∈ Subgroup.center (X ⧸ O) ∧
      (QuotientGroup.mk' O z) ^ 3 = 1 ∧ orderOf (QuotientGroup.mk' O z) = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : z ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hcenter : QuotientGroup.mk' O z ∈ Subgroup.center (X ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    have hzcomm : x * z = z * x := (Subgroup.mem_center_iff.mp hzZ) x
    calc QuotientGroup.mk' O x * QuotientGroup.mk' O z
        = QuotientGroup.mk' O (x * z) := by rw [map_mul]
      _ = QuotientGroup.mk' O (z * x) := by rw [hzcomm]
      _ = QuotientGroup.mk' O z * QuotientGroup.mk' O x := by rw [map_mul]
  have hne : QuotientGroup.mk' O z ≠ 1 := by
    intro h1
    have hzO : z ∈ O :=
      (QuotientGroup.eq_one_iff (N := O) z).mp (by simpa using h1)
    have hdvd : 3 ∣ Nat.card O := by
      have h := Subgroup.orderOf_dvd_natCard O hzO
      rwa [hz] at h
    exact hcopO hdvd
  have hpow : (QuotientGroup.mk' O z) ^ 3 = 1 := by
    rw [← map_pow, hz3, map_one]
  exact ⟨hcenter, hpow, orderOf_eq_prime hpow hne⟩

private lemma mem_comap_generalizedFitting_of_central_order_three {X : Type*} [Group X]
    [Finite X] {O : Subgroup X} [O.Normal] {z : X}
    (hcopO : ¬ 3 ∣ Nat.card O) (hzZ : z ∈ Subgroup.center X) (hz : orderOf z = 3) :
    z ∈ (CFSG.generalizedFitting (X ⧸ O)).comap (QuotientGroup.mk' O) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcenter, hpow, horder⟩ := mk'_center_order_three_data hcopO hzZ hz
  have hpgrp : IsPGroup 3 ↥(Subgroup.zpowers (QuotientGroup.mk' O z)) :=
    IsPGroup.of_card (p := 3) (n := 1)
      (by rw [Nat.card_zpowers, horder]; norm_num)
  have hnormal : (Subgroup.zpowers (QuotientGroup.mk' O z)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcenter)
  have hpCore : QuotientGroup.mk' O z ∈ CFSG.pCore 3 (X ⧸ O) :=
    le_sSup (show Subgroup.zpowers (QuotientGroup.mk' O z) ∈
      {K : Subgroup (X ⧸ O) | K.Normal ∧ IsPGroup 3 K} from ⟨hnormal, hpgrp⟩)
      (Subgroup.mem_zpowers (QuotientGroup.mk' O z))
  change QuotientGroup.mk' O z ∈ CFSG.fittingSubgroup (X ⧸ O) ⊔ CFSG.layer (X ⧸ O)
  exact Subgroup.mem_sup_left ((CFSG.pCore_le_fitting (X ⧸ O) 3) hpCore)

private lemma isCyclic_of_forall_pow_three_mem_zpowers {X : Type*} [Group X] [Finite X]
    {S : Subgroup X} {z : X} (hS : IsPGroup 3 ↥S) (hzS : z ∈ S) (hz : orderOf z = 3)
    (hno : ∀ s ∈ S, s ^ 3 = 1 → s ∈ Subgroup.zpowers z) : IsCyclic ↥S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 ↥S) := ⟨hS⟩
  by_contra hnc
  obtain ⟨A, -, hAcard, hAelem⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have hZ0card : Nat.card ↥(Subgroup.zpowers (⟨z, hzS⟩ : ↥S)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk z hzS, hz]
  have hA_le_Z0 : A ≤ Subgroup.zpowers (⟨z, hzS⟩ : ↥S) := by
    intro a ha
    have ha3 : a ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
    have hx3 : ((a : ↥S) : X) ^ 3 = 1 := by
      simpa using congrArg (fun t : ↥S => (t : X)) ha3
    have hmem : ((a : ↥S) : X) ∈ Subgroup.zpowers z := hno _ a.2 hx3
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  have hcard := Subgroup.card_le_of_le hA_le_Z0
  rw [hAcard, hZ0card] at hcard
  norm_num at hcard

private lemma map_preimage_sylow_data {X : Type*} [Group X] [Finite X]
    {O Q F S : Subgroup X} [O.Normal]
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤)
    (hF : F = (CFSG.generalizedFitting (X ⧸ O)).comap (QuotientGroup.mk' O))
    (hS : S = Q ⊓ F)
    (hScyc : IsCyclic ↥S) :
    S.map (QuotientGroup.mk' O) =
        Q.map (QuotientGroup.mk' O) ⊓ CFSG.generalizedFitting (X ⧸ O) ∧
      CFSG.ABGLocalTools.IsSylowOf 3 (S.map (QuotientGroup.mk' O))
        (CFSG.generalizedFitting (X ⧸ O)) ∧
      IsCyclic ↥(S.map (QuotientGroup.mk' O)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  let Y := X ⧸ O
  let Qbar : Subgroup Y := Q.map π
  have hSmap_eq : S.map π = Qbar ⊓ CFSG.generalizedFitting Y := by
    rw [hS, hF]
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Subgroup.mem_map.mpr ⟨s, hs.1, rfl⟩, hs.2⟩
    · rintro ⟨hyQ, hyF⟩
      obtain ⟨q, hqQ, hqy⟩ := Subgroup.mem_map.mp hyQ
      have hqF : q ∈ (CFSG.generalizedFitting Y).comap π := by
        change π q ∈ CFSG.generalizedFitting Y
        rw [hqy]
        exact hyF
      exact ⟨q, Subgroup.mem_inf.mpr ⟨hqQ, hqF⟩, hqy⟩
  have hindex : ¬ 3 ∣ Q.index := by
    have := (CFSG.ABGLocalTools.isSylowOf_iff.mp hQ).2.2
    simpa [Subgroup.relIndex_top_right] using this
  let QX : Sylow 3 X := hQ.isPGroup.toSylow hindex
  have hQXcoe : (QX : Subgroup X) = Q := rfl
  let Sbar : Sylow 3 Y := Sylow.mapSurjective (QuotientGroup.mk'_surjective O) QX
  have hSbarcoe : (Sbar : Subgroup Y) = Qbar := by
    change (Sylow.mapSurjective (QuotientGroup.mk'_surjective O) QX : Subgroup Y) = _
    rw [Sylow.coe_mapSurjective, hQXcoe]
  have hQbar_sylow : CFSG.ABGLocalTools.IsSylowOf 3 Qbar ⊤ := by
    refine ⟨Sbar.subtype le_top, ?_⟩
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le le_top]
    simpa [Qbar] using hSbarcoe
  have hSmap_sylow : CFSG.ABGLocalTools.IsSylowOf 3 (S.map π)
      (CFSG.generalizedFitting Y) := by
    letI : (CFSG.generalizedFitting Y).Normal :=
      (CFSG.LocalCores.generalized_fitting_characteristic (G := Y)).2
    have h := hQbar_sylow.inf_of_le_normalizer (N := CFSG.generalizedFitting Y) le_top (by
      rw [Subgroup.normalizer_eq_top])
    simpa [hSmap_eq, Qbar] using h
  have hSmap_cyc : IsCyclic ↥(S.map π) := by
    let f : ↥S →* ↥(S.map π) :=
      (π.comp S.subtype).codRestrict (S.map π)
        (fun x => Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)
    refine isCyclic_of_surjective f ?_
    intro y
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
  exact ⟨hSmap_eq, hSmap_sylow, hSmap_cyc⟩

private lemma map_eq_top_of_cyclic_of_layer_eq_bot {X : Type*} [Group X] [Finite X]
    {O K Q S : Subgroup X} [O.Normal]
    (hQab : IsMulCommutative ↥Q) (hQp : IsPGroup 3 ↥Q)
    (hQcyc : ¬ IsCyclic ↥Q) (hcopO : ¬ 3 ∣ Nat.card O) (hSQ : S ≤ Q)
    (hSmap_sylow : CFSG.ABGLocalTools.IsSylowOf 3 (S.map (QuotientGroup.mk' O))
      (CFSG.generalizedFitting (X ⧸ O)))
    (hSmap_cyc : IsCyclic ↥(S.map (QuotientGroup.mk' O)))
    (hEbot : CFSG.layer (X ⧸ O) = ⊥)
    (hcore : CFSG.pPrimeCore 3 (X ⧸ O) = ⊥) :
    K.map (QuotientGroup.mk' O) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  let Y := X ⧸ O
  have hSmap_sylow' : CFSG.ABGLocalTools.IsSylowOf 3 (S.map π)
      (CFSG.generalizedFitting Y) := by
    simpa [π, Y] using hSmap_sylow
  have hSmap_cyc' : IsCyclic ↥(S.map π) := by simpa [π] using hSmap_cyc
  have hFstar_eq_pCore : CFSG.generalizedFitting Y = CFSG.pCore 3 Y := by
    change CFSG.fittingSubgroup Y ⊔ CFSG.layer Y = CFSG.pCore 3 Y
    rw [hEbot, sup_bot_eq, CFSG.Fitting_eq_pcore Y 3 hcore]
  have hSmap_eq_pCore : S.map π = CFSG.pCore 3 Y := by
    have h := hSmap_sylow'
    rw [hFstar_eq_pCore] at h
    exact (h.eq_of_le h.le le_rfl CFSG.pCore_isPGroup).symm
  have hFstar_eq_S : CFSG.generalizedFitting Y = S.map π :=
    hFstar_eq_pCore.trans hSmap_eq_pCore.symm
  have hQbar_comm : ∀ a b : ↥(Q.map π), a * b = b * a := by
    intro a b
    obtain ⟨a', ha'Q, ha'eq⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb'Q, hb'eq⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    change a.1 * b.1 = b.1 * a.1
    rw [← ha'eq, ← hb'eq, ← map_mul, ← map_mul]
    have hcommX : a' * b' = b' * a' :=
      congrArg (fun t : ↥Q => (t : X)) (hQab.is_comm.comm ⟨a', ha'Q⟩ ⟨b', hb'Q⟩)
    rw [hcommX]
  have hSmap_le_Qbar : S.map π ≤ Q.map π := Subgroup.map_mono hSQ
  have hQbar_le_cent : Q.map π ≤
      Subgroup.centralizer ((S.map π : Subgroup Y) : Set Y) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (congrArg Subtype.val (hQbar_comm ⟨q, hq⟩ ⟨s, hSmap_le_Qbar hs⟩)).symm
  have hQbar_le_Smap : Q.map π ≤ S.map π := by
    refine hQbar_le_cent.trans ?_
    rw [← hFstar_eq_S]
    exact CFSG.centralizer_generalizedFitting_le Y
  have hQbar_cyc : IsCyclic ↥(Q.map π) := by
    letI : IsCyclic ↥(S.map π) := hSmap_cyc'
    exact isCyclic_of_le hQbar_le_Smap
  have hQcyc' : IsCyclic ↥Q := by
    let f : ↥Q →* ↥(Q.map π) :=
      (π.comp Q.subtype).codRestrict (Q.map π)
        (fun x => Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)
    refine isCyclic_of_injective f ?_
    intro x y hxy
    exact CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hcopO hQp
      (congrArg Subtype.val hxy)
  exact (hQcyc hQcyc').elim

private lemma false_of_cyclic_of_layer_ne_bot {X : Type*} [Group X] [Finite X]
    {O S : Subgroup X} [O.Normal] {z : X}
    (hcopO : ¬ 3 ∣ Nat.card O) (hzZ : z ∈ Subgroup.center X) (hz : orderOf z = 3)
    (hzS : z ∈ S)
    (hcore : CFSG.pPrimeCore 3 (X ⧸ O) = ⊥)
    (hSmap_sylow : CFSG.ABGLocalTools.IsSylowOf 3 (S.map (QuotientGroup.mk' O))
      (CFSG.generalizedFitting (X ⧸ O)))
    (hSmap_cyc : IsCyclic ↥(S.map (QuotientGroup.mk' O)))
    (hEbot : CFSG.layer (X ⧸ O) ≠ ⊥) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  let Y := X ⧸ O
  have hSmap_sylow' : CFSG.ABGLocalTools.IsSylowOf 3 (S.map π)
      (CFSG.generalizedFitting Y) := by
    simpa [π, Y] using hSmap_sylow
  have hSmap_cyc' : IsCyclic ↥(S.map π) := by simpa [π] using hSmap_cyc
  obtain ⟨hzbar_center, hzbar3, hzbar_order⟩ :=
    mk'_center_order_three_data hcopO hzZ hz
  have hcomp : ∃ J : Subgroup Y, CFSG.IsComponent J ∧ J ≠ ⊥ := by
    by_contra h
    apply hEbot
    rw [CFSG.layer.eq_sSup]
    refine le_antisymm ?_ bot_le
    refine sSup_le ?_
    intro J hJ
    by_cases hJb : J = ⊥
    · rw [hJb]
    · exact False.elim (h ⟨J, hJ, hJb⟩)
  obtain ⟨J, hJ, hJne⟩ := hcomp
  have hJnotcop : ¬ Nat.Coprime 3 (Nat.card ↥J) := by
    intro hcop
    have hle : J ≤ CFSG.pPrimeCore 3 Y :=
      CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hJ.2 hcop
    rw [hcore] at hle
    exact hJne (le_bot_iff.mp hle)
  have hJ3 : 3 ∣ Nat.card ↥J := (Nat.prime_three.dvd_iff_not_coprime).mpr hJnotcop
  have hJleF : J ≤ CFSG.generalizedFitting Y := by
    have h1 := CFSG.LocalCores.component_le_layer hJ
    simpa [CFSG.generalizedFitting, CFSG.WholeGroup.fstarOf] using
      h1.trans (le_sup_right : CFSG.layer Y ≤ CFSG.fittingSubgroup Y ⊔ CFSG.layer Y)
  have hFit_le_norm : CFSG.fittingSubgroup Y ≤ Subgroup.normalizer (J : Set Y) := by
    have hcomm : CFSG.fittingSubgroup Y ≤ Subgroup.centralizer (CFSG.layer Y : Set Y) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.LocalCores.fitting_layer_commute (G := Y))
    refine hcomm.trans ((Subgroup.centralizer_le ?_).trans
      (Subgroup.centralizer_le_normalizer _))
    exact CFSG.LocalCores.component_le_layer hJ
  have hLayer_le_norm : CFSG.layer Y ≤ Subgroup.normalizer (J : Set Y) :=
    CFSG.LocalCores.layer_le_normalizer hJ
  have hF_le_norm : CFSG.generalizedFitting Y ≤ Subgroup.normalizer (J : Set Y) := by
    simpa [CFSG.generalizedFitting, CFSG.WholeGroup.fstarOf] using
      sup_le hFit_le_norm hLayer_le_norm
  have hInt_sylow : CFSG.ABGLocalTools.IsSylowOf 3 (S.map π ⊓ J) J :=
    hSmap_sylow'.inf_of_le_normalizer hJleF hF_le_norm
  obtain ⟨P, hP⟩ := hInt_sylow.exists_sylow_eq_subgroupOf
  have hPne : (P : Subgroup J) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hJ3
  have hInt_ne : S.map π ⊓ J ≠ ⊥ := by
    intro hbot
    apply hPne
    rw [hP, hbot]
    simp
  have hInt_cyc : IsCyclic ↥(S.map π ⊓ J) := by
    letI : IsCyclic ↥(S.map π) := hSmap_cyc'
    exact isCyclic_of_le inf_le_left
  have hP_cyc : IsCyclic ↥(P : Subgroup J) := by
    letI : IsCyclic ↥(S.map π ⊓ J) := hInt_cyc
    let f : ↥(P : Subgroup J) →* ↥(S.map π ⊓ J) :=
      (J.subtype.comp (P : Subgroup J).subtype).codRestrict _
        (fun x => by
          have hx : (x : J) ∈ (S.map π ⊓ J).subgroupOf J := by
            rw [← hP]
            exact x.2
          exact hx)
    refine isCyclic_of_injective f ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : ↥(S.map π ⊓ J) => (t : Y)) hab
  letI : Group.IsPerfect ↥J := hJ.1.1
  letI : IsCyclic ↥(P : Subgroup J) := hP_cyc
  obtain ⟨n, -, hnInv⟩ :=
    CFSG.GroupTheory.exists_mem_normalizer_conj_eq_inv_of_perfect P hPne
  let ΩS : Subgroup Y :=
    (CFSG.omega₁ ↥(S.map π) (p := 3)).map (S.map π).subtype
  letI : CommGroup ↥(S.map π) := IsCyclic.commGroup
  have hzbar_mem_Smap : π z ∈ S.map π := Subgroup.mem_map.mpr ⟨z, hzS, rfl⟩
  have h3dvdSmap : 3 ∣ Nat.card ↥(S.map π) := by
    have h := Subgroup.orderOf_dvd_natCard (S.map π) hzbar_mem_Smap
    rwa [hzbar_order] at h
  have hOmega_card : Nat.card ↥ΩS = 3 := by
    rw [show Nat.card ↥ΩS = Nat.card ↥(CFSG.omega₁ ↥(S.map π) (p := 3)) from
      Subgroup.card_map_of_injective (S.map π).subtype_injective]
    rw [CFSG.card_omega₁_of_isCyclic, Nat.gcd_eq_right h3dvdSmap]
  have hOmega_le_H : ΩS ≤ S.map π ⊓ J := by
    have hH_pgroup : IsPGroup 3 ↥(S.map π ⊓ J) := hInt_sylow.isPGroup
    have hHcard_ne : Nat.card ↥(S.map π ⊓ J) ≠ 1 := by
      intro h1
      exact hInt_ne (Subgroup.card_eq_one.mp h1)
    have h3dvdH : 3 ∣ Nat.card ↥(S.map π ⊓ J) := by
      rcases hH_pgroup.card_eq_or_dvd with h | h
      · exact absurd h hHcard_ne
      · exact h
    haveI : Fintype ↥(S.map π ⊓ J) := Fintype.ofFinite _
    have h3dvdH' : 3 ∣ Fintype.card ↥(S.map π ⊓ J) := by
      rwa [Nat.card_eq_fintype_card] at h3dvdH
    obtain ⟨y, hy3⟩ := exists_prime_orderOf_dvd_card (G := ↥(S.map π ⊓ J)) 3 h3dvdH'
    have hy_pow : (y : Y) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (y : ↥(S.map π ⊓ J))
      rw [hy3] at h
      simpa using congrArg (fun t : ↥(S.map π ⊓ J) => (t : Y)) h
    have hy_omega : (y : Y) ∈ ΩS := by
      refine Subgroup.mem_map.mpr ⟨⟨(y : Y), (Subgroup.mem_inf.mp y.2).1⟩, ?_, rfl⟩
      rw [CFSG.mem_omega₁_iff_of_comm (fun a b => mul_comm a b)]
      simpa using hy_pow
    have hy_order : orderOf (y : Y) = 3 := by
      have h := Subgroup.orderOf_coe (H := S.map π ⊓ J) y
      rw [hy3] at h
      exact h
    have hzpowers_card : Nat.card ↥(Subgroup.zpowers (y : Y)) = 3 := by
      rw [Nat.card_zpowers, hy_order]
    have heq : Subgroup.zpowers (y : Y) = ΩS := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy_omega) ?_
      rw [hOmega_card, hzpowers_card]
    rw [← heq]
    exact Subgroup.zpowers_le.mpr y.2
  have hzbar_mem_omega : π z ∈ ΩS := by
    refine Subgroup.mem_map.mpr ⟨⟨π z, hzbar_mem_Smap⟩, ?_, rfl⟩
    rw [CFSG.mem_omega₁_iff_of_comm (fun a b => mul_comm a b)]
    simpa [π] using hzbar3
  have hzbar_mem_J : π z ∈ J := (Subgroup.mem_inf.mp (hOmega_le_H hzbar_mem_omega)).2
  let aJ : ↥J := ⟨π z, hzbar_mem_J⟩
  have haJ_center : aJ ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hzbar_center) (j : Y)
  have haJ_order : orderOf aJ = 3 := by
    have h := Subgroup.orderOf_coe aJ
    rw [show (aJ : Y) = π z from rfl, hzbar_order] at h
    exact h.symm
  have hzpowers_normal : (Subgroup.zpowers aJ).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haJ_center)
  letI : (Subgroup.zpowers aJ).Normal := hzpowers_normal
  have haJ_pgroup : IsPGroup 3 ↥(Subgroup.zpowers aJ) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [Nat.card_zpowers, haJ_order]; norm_num)
  have hzpowers_le_P : Subgroup.zpowers aJ ≤ (P : Subgroup J) :=
    IsPGroup.le_sylow_of_normal haJ_pgroup P
  have haJP : aJ ∈ (P : Subgroup J) := hzpowers_le_P (Subgroup.mem_zpowers aJ)
  have haJ_omegaP : (⟨aJ, haJP⟩ : ↥(P : Subgroup J)) ∈
      CFSG.omega₁ ↥(P : Subgroup J) (p := 3) := by
    letI : CommGroup ↥(P : Subgroup J) := IsCyclic.commGroup
    rw [CFSG.mem_omega₁_iff_of_comm (fun a b => mul_comm a b)]
    apply Subtype.ext
    change aJ ^ 3 = 1
    apply Subtype.ext
    change (π z) ^ 3 = 1
    exact hzbar3
  have hmem_map : aJ ∈ (CFSG.omega₁ ↥(P : Subgroup J) (p := 3)).map
      (P : Subgroup J).subtype :=
    Subgroup.mem_map.mpr ⟨⟨aJ, haJP⟩, haJ_omegaP, rfl⟩
  have hinv := hnInv aJ hmem_map
  have hcentJ : n * aJ * n⁻¹ = aJ := by
    have h := Subgroup.mem_center_iff.mp haJ_center n
    calc n * aJ * n⁻¹ = aJ * n * n⁻¹ := by rw [h]
      _ = aJ := by group
  have heq : aJ = aJ⁻¹ := by
    rw [hcentJ] at hinv
    exact hinv
  have h2 : aJ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [heq]
    exact mul_inv_cancel aJ
  have hdvd : orderOf aJ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [haJ_order] at hdvd
  exact absurd hdvd (by norm_num)

theorem eq_top_of_abelianSylowThree {X : Type*} [Group X] [Finite X]
    {K Q D₁ D₂ : Subgroup X} {z : X}
    (hOK : CFSG.pPrimeCore 3 X ≤ K) (hQK : Q ≤ K)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤)
    (hQab : IsMulCommutative ↥Q) (hQcyc : ¬ IsCyclic ↥Q)
    (hzQ : z ∈ Q) (hzZ : z ∈ Subgroup.center X) (hz : orderOf z = 3)
    (hN : ∀ U : Subgroup X, U ≤ Q → (∀ u ∈ U, u ^ 3 = 1) →
      ¬ U ≤ Subgroup.zpowers z → Subgroup.normalizer (U : Set X) ≤ K)
    (hD₁ : D₁ ≤ Q) (hD₂ : D₂ ≤ Q)
    (hC₁ : Subgroup.centralizer (D₁ : Set X) ≤ K)
    (hC₂ : Subgroup.centralizer (D₂ : Set X) ≤ K)
    (hdisj : (Subgroup.normalClosure (D₁ : Set X)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      (Subgroup.normalClosure (D₂ : Set X)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    K = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup X := CFSG.pPrimeCore 3 X
  have hcopO : ¬ 3 ∣ Nat.card O :=
    (Nat.prime_three.coprime_iff_not_dvd).1
      (by simpa [O] using CFSG.pPrimeCore_coprime_card (p := 3) (G := X))
  have hKcomap : (K.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O) = K := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr (by simpa [O] using hOK)
  have hE_le : CFSG.layer (X ⧸ O) ≤ K.map (QuotientGroup.mk' O) :=
    layer_le_map_of_disjoint_normalClosures (O := O) hcopO hQ hD₁ hD₂ hC₁ hC₂
      (by simpa [O] using hdisj)
  have hcore : CFSG.pPrimeCore 3 (X ⧸ O) = ⊥ := by
    simpa [O] using CFSG.pPrimeCore_quotient_eq_bot (p := 3) Nat.prime_three
  have hFstar_le : CFSG.generalizedFitting (X ⧸ O) ≤ K.map (QuotientGroup.mk' O) :=
    generalizedFitting_le_map hcore hQ hQK hE_le
  let F : Subgroup X := (CFSG.generalizedFitting (X ⧸ O)).comap (QuotientGroup.mk' O)
  let S : Subgroup X := Q ⊓ F
  obtain ⟨hF_le_K, hS_sylow, hX_eq⟩ :=
    preimage_generalizedFitting_frattini hKcomap rfl rfl hFstar_le hQ
  by_cases hex : ∃ s ∈ S, s ^ 3 = 1 ∧ s ∉ Subgroup.zpowers z
  · refine eq_top_of_map_mk'_eq_top hKcomap ?_
    exact map_eq_top_of_exists_omega_not_le hF_le_K hX_eq
      (show S ≤ Q from inf_le_left) hQab hN hex
  · have hno : ∀ s ∈ S, s ^ 3 = 1 → s ∈ Subgroup.zpowers z := by
      intro s hsS hs3
      by_contra hsz
      exact hex ⟨s, hsS, hs3, hsz⟩
    have hzF : z ∈ F :=
      mem_comap_generalizedFitting_of_central_order_three hcopO hzZ hz
    have hzS : z ∈ S := Subgroup.mem_inf.mpr ⟨hzQ, hzF⟩
    have hScyc : IsCyclic ↥S :=
      isCyclic_of_forall_pow_three_mem_zpowers hS_sylow.isPGroup hzS hz hno
    obtain ⟨-, hSmap_sylow, hSmap_cyc⟩ :=
      map_preimage_sylow_data hQ rfl rfl hScyc
    by_cases hEbot : CFSG.layer (X ⧸ O) = ⊥
    · refine eq_top_of_map_mk'_eq_top hKcomap ?_
      exact map_eq_top_of_cyclic_of_layer_eq_bot hQab hQ.isPGroup hQcyc hcopO
        (show S ≤ Q from inf_le_left) hSmap_sylow hSmap_cyc hEbot hcore
    · exact (false_of_cyclic_of_layer_ne_bot hcopO hzZ hz hzS hcore
        hSmap_sylow hSmap_cyc hEbot).elim

end CFSG.GroupTheory
