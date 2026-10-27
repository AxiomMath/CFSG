module

public import CFSG.LargeExtraspecial.S63BBasic
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Timmesfeld.Bridge.Asc72YU3
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InOut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld CFSG.ComponentClassification
open scoped Pointwise

namespace S63

variable {X : Type} [Group X] [Finite X] {ζ : X} {F : Subgroup X}

namespace SmithConf

variable (hC : SmithConf ζ F) (hs : IsSimpleGroup (UZ ζ))
include hC hs

theorem isPGroup_iota_range_sup {τ : X} (hτ : τ ∈ CorB.conjCent ζ) :
    IsPGroup 2 ((iota (F := F) hs).range ⊔
      zpowers (piU ζ ⟨τ, mem_normalClosure_of_isConj hτ.2⟩) : Subgroup (UZ ζ)) := by
  obtain ⟨hNC, hNn, hN2, -, -⟩ := hC.iota_range_props hs
  set t := piU ζ ⟨τ, mem_normalClosure_of_isConj hτ.2⟩ with ht
  have ht2 : t ^ 2 = 1 := by
    rw [← hC.orderOf_piU hs hτ.2]
    exact pow_orderOf_eq_one t
  have htC : t ∈ centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ)) := by
    rw [mem_centralizer_singleton_iff, ht, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hτ.1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ht2])
  refine hN2.to_sup_of_normal_left' ?_ ?_
  · intro g
    obtain ⟨g, hg⟩ := g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, ht2, one_zpow]
  · rw [zpowers_le, mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hNn t htC n hn, fun hn => ?_⟩
    have := hNn t htC _ hn
    rwa [htinv, show t * (t * n * t) * t = (t * t) * n * (t * t) by group, ← pow_two, ht2,
      one_mul, mul_one] at this

theorem false_of_psl2 {n : ℕ} (hn : 2 ≤ n) (e : UZ ζ ≃* Theory.Comparator.PSL2Model n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : (2 : GaloisField 2 n) = 0 := CharTwo.two_eq_zero
  obtain ⟨ψ, hψ⟩ :=
    QuasithinUnique.Lin2.exists_injective_outer_sl2_char_two (GaloisField 2 n) hK2
  have : IsCyclic (GaloisField 2 n ≃+* GaloisField 2 n) :=
    (LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two (GaloisField 2 n)
      (GaloisField.card 2 n (by omega))).2
  let E := OuterAutomorphisms.equivalence
    (e.trans (QuasithinUnique.Lin2.psl2EquivSl2 (GaloisField 2 n) hK2))
  have hF2 := hC.card_le_two_mul_card_Finn_of_injective (ψ.comp E.toMonoidHom)
    (hψ.comp E.injective)
  obtain ⟨-, -, hN2, -, -⟩ := hC.iota_range_props hs
  obtain ⟨T, hT⟩ := hN2.exists_le_sylow
  have hTab := Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_psl2 hn e T
  refine hC.false_of_abelian (Finn_le ζ F) (fun a ha b hb => ?_) hF2
  have h1 := hTab _ (hT ⟨⟨a, ha⟩, rfl⟩) _ (hT ⟨⟨b, hb⟩, rfl⟩)
  have h2 : iota hs (⟨a, ha⟩ * ⟨b, hb⟩) = iota hs (⟨b, hb⟩ * ⟨a, ha⟩) := by
    rw [map_mul, map_mul]
    exact h1.eq
  exact congrArg Subtype.val (hC.iota_injective hs h2)

theorem false_of_suzuki {n : ℕ} (hn : 1 ≤ n)
    (e : UZ ζ ≃* Theory.Comparator.SzModel n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : BenderSuzuki.IsBenderGroup (UZ ζ) := .isSuzuki n hn e
  obtain ⟨E⟩ := SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup n
  have hmodel : Theory.Comparator.SzModel n = CFSG.Open.Sz n := CFSG.Models.benderSzModel_eq_sz n
  have hSM : Blueprint.SuzukiModel (UZ ζ) 2 (2 * n + 1) :=
    ⟨rfl, n, hn, GaloisField 2 (2 * n + 1), inferInstance, inferInstance, rfl,
      GaloisField.card 2 (2 * n + 1) (by omega),
      ⟨(e.trans (MulEquiv.subgroupCongr hmodel)).trans E⟩⟩
  have hodd := (LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} (UZ ζ) 2
    (2 * n + 1) hSM).1.2.2
  have hFeq := hC.Finn_eq_of_odd hodd
  obtain ⟨τ, hτc, hτne⟩ := hC.nonIsolated
  obtain ⟨T, hT⟩ := (hC.isPGroup_iota_range_sup hs hτc).exists_le_sylow
  set t := piU ζ ⟨τ, mem_normalClosure_of_isConj hτc.2⟩ with ht
  have htT : t ∈ (T : Subgroup (UZ ζ)) := hT (mem_sup_right (mem_zpowers t))
  have htt : t * t = 1 := by
    rw [← pow_two, ← hC.orderOf_piU hs hτc.2]
    exact pow_orderOf_eq_one t
  have htc := Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hB T htT htt
  refine hC.false_of_forall_fix hs hτc hτne fun f hf => ?_
  have hf' : f ∈ Finn ζ F := by rw [hFeq]; exact hf
  have h1 := htc _ (hT (mem_sup_left ⟨⟨f, hf'⟩, rfl⟩))
  rw [show f = ((⟨f, hf'⟩ : ↥(Finn ζ F)) : X) from rfl, conjAut_eq_iota hs, ← h1.eq,
    mul_inv_cancel_right]

theorem false_of_psu3 {n : ℕ} (hn : 2 ≤ n) (e : UZ ζ ≃* Theory.Comparator.PSU3Model n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : BenderSuzuki.IsBenderGroup (UZ ζ) := .isPSU3 n hn e
  have hmodel : Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
      CFSG.Models.benderPSU3Model_eq_psu3 n
  let e' : UZ ζ ≃* CFSG.Open.PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
  obtain ⟨τ, hτc, hτne⟩ := hC.nonIsolated
  set t := piU ζ ⟨τ, mem_normalClosure_of_isConj hτc.2⟩ with ht
  set z := piU ζ (zetaU ζ) with hz
  have hzt : t * z = z * t := by
    rw [ht, hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hτc.1
  have hz2 : orderOf z = 2 := hC.orderOf_piU hs (IsConj.refl ζ)
  have htt : t * t = 1 := by
    rw [← pow_two, ← hC.orderOf_piU hs hτc.2]
    exact pow_orderOf_eq_one t
  have hzP : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2,
    pow_one])
  have htP : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hC.orderOf_piU hs hτc.2, pow_one])
  have h2 : IsPGroup 2 (zpowers z ⊔ zpowers t : Subgroup (UZ ζ)) := by
    refine hzP.to_sup_of_normal_left' htP ?_
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      rw [((Commute.zpow_right (show Commute t z from hzt) k).eq), mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers z) k
    · intro hh
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hh
      have hc : Commute t (z ^ k) := Commute.zpow_right (show Commute t z from hzt) k
      have : h = z ^ k := by
        calc h = t⁻¹ * (t * h * t⁻¹) * t := by group
          _ = t⁻¹ * (z ^ k * t) := by rw [← hk, mul_assoc]
          _ = t⁻¹ * (t * z ^ k) := by rw [hc.eq]
          _ = z ^ k := by group
      rw [this]
      exact zpow_mem (mem_zpowers z) k
  obtain ⟨T, hT⟩ := h2.exists_le_sylow
  have hzT : z ∈ (T : Subgroup (UZ ζ)) := hT (mem_sup_left (mem_zpowers z))
  have htT : t ∈ (T : Subgroup (UZ ζ)) := hT (mem_sup_right (mem_zpowers t))
  have htc := Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hB T htT htt
  obtain ⟨q, k, hBorel, -⟩ := Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_fusionBenderBorel hB
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  refine hC.false_of_involutions_comm hτc hτne fun f hf hff => ?_
  set α := SmithConf.conjAut ζ f with hα
  have hαα : α * α = 1 := by rw [hα, ← map_mul, hff, map_one]
  have hαz : α z = z := conjAut_zeta (hC.comm_zeta hf)
  have hαz' : α⁻¹ z = z := by
    calc α⁻¹ z = α⁻¹ (α z) := by rw [hαz]
      _ = z := MulAut.inv_apply_self (UZ ζ) α z
  have hTT : α • T = T := by
    by_contra hne
    refine hz1 (ComponentClassification.AschbacherToolkit.Bender.Omega.eq_one_of_mem_of_mem
      (hBorel T).1 hne hzT ?_)
    rw [ComponentClassification.AschbacherToolkit.Bender.Omega.mem_smul_iff, hαz']
    exact hzT
  have hαT : ∀ y ∈ (T : Subgroup (UZ ζ)), α y ∈ T := by
    intro y hy
    have : α y ∈ ((α • T : Sylow 2 (UZ ζ)) : Subgroup (UZ ζ)) := by
      rw [ComponentClassification.AschbacherToolkit.Bender.Omega.mem_smul_iff,
        MulAut.inv_apply_self (UZ ζ)]
      exact hy
    rwa [hTT] at this
  exact hC.conj_eq_of_conjAut_fix hs hτc.2
    (Timmesfeld.Bridge.Asc72.YU3.fix_center_of_mulEquiv_psu3 hn e' T α hαα hαT htT htc)

end SmithConf

theorem smith55Input : Smith55Input := by
  intro X _ _ ζ F hC hB
  have hs : IsSimpleGroup (UZ ζ) := Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hB
  rcases hB with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact hC.false_of_psl2 hs hn e
  · exact hC.false_of_suzuki hs hn e
  · exact hC.false_of_psu3 hs hn e

end S63

end CFSG.LargeExtraspecial
