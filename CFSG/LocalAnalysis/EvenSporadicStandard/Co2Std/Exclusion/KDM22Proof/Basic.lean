module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Foundations.Basic
public import CFSG.Open.FusionDefs
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

structure M22Normal {C : Type*} [Group C] (N : Subgroup C) : Prop where
  normal : N.Normal
  isSimpleGroup : IsSimpleGroup N
  card_eq : Nat.card N = 443520

variable {C : Type*} [Group C] {N : Subgroup C}

private lemma eq_bot_of_normal_odd_card {G : Type*} [Group G] [IsSimpleGroup G]
    (M : Subgroup G) [M.Normal] (hodd : Odd (Nat.card M)) (heven : Even (Nat.card G)) :
    M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hbot | htop
  · exact hbot
  · exfalso
    rw [htop, Subgroup.card_top] at hodd
    exact Nat.not_even_iff_odd.2 hodd heven

private lemma injOn_of_inf_ker_eq_bot {G H : Type*} [Group G] [Group H] (f : G →* H)
    {K : Subgroup G} (hK : K ⊓ f.ker = ⊥) : Set.InjOn f K := by
  intro x hx y hy hxy
  have hmem : x⁻¹ * y ∈ K ⊓ f.ker := by
    refine ⟨K.mul_mem (K.inv_mem hx) hy, ?_⟩
    change f (x⁻¹ * y) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  rw [hK, Subgroup.mem_bot] at hmem
  calc x = x * (x⁻¹ * y) := by rw [hmem, mul_one]
    _ = y := by group

theorem M22Normal.exists_mul_ne_mul (h : M22Normal N) : ∃ a b : N, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  haveI hsimple : IsSimpleGroup N := h.isSimpleGroup
  haveI : IsMulCommutative N := ⟨⟨hcomm⟩⟩
  have hprime : (Nat.card N).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  rw [h.card_eq] at hprime
  exact absurd hprime (by norm_num)

theorem M22Normal.center_eq_bot (h : M22Normal N) : center N = ⊥ := by
  haveI : IsSimpleGroup N := h.isSimpleGroup
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.exists_mul_ne_mul).2

theorem M22Normal.card_quotient_center (h : M22Normal N) :
    Nat.card (N ⧸ center N) = 443520 := by
  calc Nat.card (N ⧸ center N) = Nat.card (N ⧸ ⊥) := by rw [h.center_eq_bot]
    _ = Nat.card N := Nat.card_congr (QuotientGroup.quotientBot).toEquiv
    _ = 443520 := h.card_eq

theorem M22Normal.isComponent (h : M22Normal N) : CFSG.IsComponent N := by
  haveI : IsSimpleGroup N := h.isSimpleGroup
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.exists_mul_ne_mul).1,
    h.normal.isSubnormal⟩

theorem M22Normal.fusionZStar_eq_bot [Finite C] (h : M22Normal N) :
    CFSG.Open.fusionZStar N = ⊥ := by
  haveI : IsSimpleGroup N := h.isSimpleGroup
  have hO : CFSG.Open.fusionOddCore N = ⊥ := by
    show CFSG.oddCore N = ⊥
    exact eq_bot_of_normal_odd_card _
      (CFSG.ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore N)
      (by rw [h.card_eq]; norm_num)
  have hcenter : center (N ⧸ CFSG.Open.fusionOddCore N) = ⊥ := by
    let e : N ⧸ CFSG.Open.fusionOddCore N ≃* N :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    have hmap : Subgroup.map (e : N ⧸ CFSG.Open.fusionOddCore N →* N)
        (center (N ⧸ CFSG.Open.fusionOddCore N)) = ⊥ := by
      rw [Subgroup.map_center_eq, h.center_eq_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective (f :=
      (e : N ⧸ CFSG.Open.fusionOddCore N →* N)) _ e.injective).mp hmap
  rw [CFSG.Open.fusionZStar, hcenter, MonoidHom.comap_bot, QuotientGroup.ker_mk', hO]

theorem M22Normal.card_quotient_fusionZStar [Finite C] (h : M22Normal N) :
    Nat.card (N ⧸ CFSG.Open.fusionZStar N) = 443520 := by
  calc Nat.card (N ⧸ CFSG.Open.fusionZStar N) = Nat.card (N ⧸ ⊥) := by
        rw [h.fusionZStar_eq_bot]
    _ = Nat.card N := Nat.card_congr (QuotientGroup.quotientBot).toEquiv
    _ = 443520 := h.card_eq

private lemma inf_pPrimeCore_two_eq_bot [Finite C] (h : M22Normal N) :
    N ⊓ CFSG.pPrimeCore 2 C = ⊥ := by
  haveI hNnormal : N.Normal := h.normal
  haveI hNsimple : IsSimpleGroup N := h.isSimpleGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPodd : Odd (Nat.card (CFSG.pPrimeCore 2 C)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C))
  have hModd : Odd (Nat.card ((N ⊓ CFSG.pPrimeCore 2 C).subgroupOf N)) := by
    have hdvd : Nat.card ((N ⊓ CFSG.pPrimeCore 2 C).subgroupOf N) ∣
        Nat.card (CFSG.pPrimeCore 2 C) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : N ⊓ CFSG.pPrimeCore 2 C ≤ N)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact Odd.of_dvd_nat hPodd hdvd
  have hMbot : (N ⊓ CFSG.pPrimeCore 2 C).subgroupOf N = ⊥ := by
    haveI : ((N ⊓ CFSG.pPrimeCore 2 C).subgroupOf N).Normal :=
      (inferInstance : (N ⊓ CFSG.pPrimeCore 2 C).Normal).subgroupOf N
    exact eq_bot_of_normal_odd_card _ hModd (by rw [h.card_eq]; norm_num)
  rw [eq_bot_iff]
  intro x hx
  have hxM : (⟨x, hx.1⟩ : N) ∈ (N ⊓ CFSG.pPrimeCore 2 C).subgroupOf N :=
    Subgroup.mem_subgroupOf.mpr hx
  rw [hMbot, Subgroup.mem_bot] at hxM
  exact Subtype.ext_iff.mp hxM

private lemma isComponent_map_pPrimeCore_two [Finite C] (h : M22Normal N) :
    CFSG.IsComponent (N.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 C))) := by
  have hinf := inf_pPrimeCore_two_eq_bot h
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card N = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [h.card_eq] at hcard
    norm_num at hcard
  have hnotle : ¬ N ≤ (QuotientGroup.mk' (CFSG.pPrimeCore 2 C)).ker := by
    rw [QuotientGroup.ker_mk']
    intro hle
    exact hNne (by rw [← inf_eq_left.mpr hle, hinf])
  have hq : CFSG.IsQuasisimple (N.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 C))) :=
    CFSG.LocalCores.isQuasisimple_map h.isComponent.1 _ hnotle
  exact ⟨hq, (h.normal.map _ (QuotientGroup.mk'_surjective _)).isSubnormal⟩

private lemma map_ne_map_of_lt_of_inf_ker_eq_bot {G H : Type*} [Group G] [Group H]
    (f : G →* H) {J N : Subgroup G} (hJ : J < N) (hNker : N ⊓ f.ker = ⊥) :
    J.map f ≠ N.map f := by
  have hinj : Set.InjOn f N := injOn_of_inf_ker_eq_bot f hNker
  intro hmaps
  have hJle : J ≤ N := hJ.le
  have hNle : N ≤ J := by
    intro x hx
    have hxmap : f x ∈ N.map f := Subgroup.mem_map_of_mem f hx
    rw [← hmaps] at hxmap
    obtain ⟨j, hjJ, hjm⟩ := hxmap
    exact (hinj hx (hJle hjJ) hjm.symm) ▸ hjJ
  exact hJ.ne (le_antisymm hJle hNle)

theorem M22Normal.isPComponent_two [Finite C] (h : M22Normal N) :
    CFSG.IsPComponent 2 N := by
  have hker : N ⊓ (QuotientGroup.mk' (CFSG.pPrimeCore 2 C)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact inf_pPrimeCore_two_eq_bot h
  refine ⟨N.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 C)),
    isComponent_map_pPrimeCore_two h, h.normal.isSubnormal, rfl, ?_⟩
  intro J hJ _
  exact map_ne_map_of_lt_of_inf_ker_eq_bot _ hJ hker

theorem M22Normal.dvd_card [Finite C] (h : M22Normal N) : 443520 ∣ Nat.card C := by
  rw [← h.card_eq]
  exact Subgroup.card_subgroup_dvd_card N

theorem m22Normal_subgroupOf {F : Type*} [Group F] {α : MulAut F} {K : Subgroup F}
    (hKα : ∀ k ∈ K, α k = k) (hKs : IsSimpleGroup K) (hK : Nat.card K = 443520)
    (hnorm : ∀ x : F, α x = x → ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    M22Normal (K.subgroupOf (fixedSubgroup α)) := by
  have hle : K ≤ fixedSubgroup α := fun k hk => hKα k hk
  haveI : IsSimpleGroup K := hKs
  refine ⟨?_, (Subgroup.subgroupOfEquivOfLe hle).isSimpleGroup, ?_⟩
  · refine Subgroup.Normal.mk fun k hk x => ?_
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hnorm (x : F) x.2 (k : F) hk
  · calc Nat.card (K.subgroupOf (fixedSubgroup α)) = Nat.card K :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      _ = 443520 := hK

theorem card_fixedSubgroup_eq {F : Type*} [Group F] (α : MulAut F) :
    Nat.card (fixedSubgroup α) = Nat.card {x : F // α x = x} := rfl

end CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof
