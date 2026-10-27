module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent

public section

open scoped Pointwise

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem card_centralizer_x₁ [Finite G] (hC : CentData z ι)
    (hx : IsConj z (ι τ₀)) :
    Nat.card (centralizer ({ι τ₀} : Set G)) = 7257600 := by
  obtain ⟨ι₁, ε, χ, hT⟩ := exists_twistData hC hx
  have htop : centralizer ({1} : Set G) = ⊤ := by
    ext x; simp [mem_centralizer_singleton_iff]
  have h1 := hT.cent.card_inf_centralizer (1 : Perm (Fin 10))
  simp only [map_one] at h1
  rw [htop, inf_top_eq] at h1
  rw [two_mul_card_centralizer_perm_ten (σ := (1 : Perm (Fin 10))) (by rw [mul_one]),
    cycleType_one, Multiset.card_zero] at h1
  rw [h1]
  norm_num [N10, Nat.factorial]

private theorem not_two_dvd_relIndex {A B : Subgroup G} (hAB : A ≤ B)
    (hA : Nat.card A = 2 ^ 9) (hB : Nat.card B = 2 ^ 9 * 14175) :
    ¬ 2 ∣ A.relIndex B := by
  intro h2
  obtain ⟨k, hk⟩ := h2
  have hkey := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.mpr hAB] at hkey
  have hdvd : 2 ^ 10 ∣ Nat.card B := by
    rw [← hkey, hk, hA]
    exact ⟨k, by ring⟩
  rw [hB] at hdvd
  norm_num at hdvd

theorem exists_normalizer_Tgrp_swap [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) :
    ∃ g₀ : G, g₀ ∈ normalizer ((Tgrp z ι Q : Subgroup G) : Set G) ∧ g₀ * z * g₀⁻¹ = ι τ₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Subgroup G := Tgrp z ι Q
  let N : Subgroup G := centralizer ({ι τ₀} : Set G)
  have hTN : T ≤ N := le_trans (Tgrp_le_CEgrp hC hQ) inf_le_right
  have hTpg : IsPGroup 2 T := Tgrp_isPGroup hC hQ.pgroup
  have hTcard : Nat.card T = 2 ^ 9 := by
    change Nat.card (Tgrp z ι Q) = 2 ^ 9
    rw [Tgrp_card hC Q, hQ.card]; norm_num
  have hNcard : Nat.card N = 7257600 := card_centralizer_x₁ hC hx
  have hNcard' : Nat.card N = 2 ^ 9 * 14175 := by rw [hNcard]; norm_num
  obtain ⟨h, hh⟩ := isConj_iff.mp hx
  let T' : Subgroup G := T.map (MulAut.conj h).toMonoidHom
  have hT'N : T' ≤ N := by
    intro x hx'
    rw [mem_centralizer_singleton_iff]
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx'
    have htz : t * z = z * t :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (le_trans (Tgrp_le_CEgrp hC hQ) inf_le_left ht)
    calc MulAut.conj h t * ι τ₀
        = (h * t * h⁻¹) * ι τ₀ := by rw [MulAut.conj_apply]
      _ = (h * t * h⁻¹) * (h * z * h⁻¹) := by rw [← hh]
      _ = h * (t * z) * h⁻¹ := by group
      _ = h * (z * t) * h⁻¹ := by rw [htz]
      _ = (h * z * h⁻¹) * (h * t * h⁻¹) := by group
      _ = ι τ₀ * (h * t * h⁻¹) := by rw [hh]
      _ = ι τ₀ * MulAut.conj h t := by rw [MulAut.conj_apply]
  have hT'pg : IsPGroup 2 T' := by
    change IsPGroup 2 (T.map (MulAut.conj h).toMonoidHom)
    exact hTpg.of_equiv
      (Subgroup.equivMapOfInjective T (MulAut.conj h).toMonoidHom (MulAut.conj h).injective)
  have hT'card : Nat.card T' = 2 ^ 9 := by
    change Nat.card (T.map (MulAut.conj h).toMonoidHom) = 2 ^ 9
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hTcard]
  have hTp : IsPGroup 2 (T.subgroupOf N) :=
    hTpg.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm
  have hT'p : IsPGroup 2 (T'.subgroupOf N) :=
    hT'pg.of_equiv (Subgroup.subgroupOfEquivOfLe hT'N).symm
  have hnotT : ¬ 2 ∣ (T.subgroupOf N).index := not_two_dvd_relIndex hTN hTcard hNcard'
  have hnotT' : ¬ 2 ∣ (T'.subgroupOf N).index :=
    not_two_dvd_relIndex hT'N hT'card hNcard'
  let P₁ : Sylow 2 N := hTp.toSylow hnotT
  let P₂ : Sylow 2 N := hT'p.toSylow hnotT'
  have hP₁ : (P₁ : Subgroup N) = T.subgroupOf N := IsPGroup.toSylow_coe hTp hnotT
  have hP₂ : (P₂ : Subgroup N) = T'.subgroupOf N := IsPGroup.toSylow_coe hT'p hnotT'
  haveI : Finite (Sylow 2 N) := Sylow.finite_of_finiteIndex P₁
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N P₂ P₁
  have hEqN : MulAut.conj c • (P₂ : Subgroup N) = (P₁ : Subgroup N) := by
    have := congrArg (fun P : Sylow 2 N => (P : Subgroup N)) hc
    rwa [Sylow.coe_subgroup_smul] at this
  have hEq : (MulAut.conj (c : G) • T').subgroupOf N = T.subgroupOf N := by
    rw [hP₂, hP₁] at hEqN
    rwa [Subgroup.conj_smul_subgroupOf hT'N c] at hEqN
  have hconjsub : MulAut.conj (c : G) • T' = T := by
    have := congrArg (Subgroup.map N.subtype) hEq
    rwa [Subgroup.map_subgroupOf_eq_of_le (Subgroup.conj_smul_le_of_le hT'N c),
      Subgroup.map_subgroupOf_eq_of_le hTN] at this
  have hsmulmap : MulAut.conj h • T = T' := rfl
  have hconjT : MulAut.conj ((c : G) * h) • T = T := by
    rw [map_mul, mul_smul, hsmulmap]
    exact hconjsub
  refine ⟨(c : G) * h, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    have hset := congrArg (fun S : Subgroup G => (S : Set G)) hconjT
    rwa [Subgroup.coe_pointwise_smul] at hset
  · have hcx₁ : (c : G) * ι τ₀ = ι τ₀ * (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2
    calc (c * h) * z * (c * h)⁻¹
        = (c : G) * (h * z * h⁻¹) * (c : G)⁻¹ := by group
      _ = (c : G) * ι τ₀ * (c : G)⁻¹ := by rw [hh]
      _ = ι τ₀ := by rw [hcx₁]; group

end CFSG.OddStandard.AltStdSec.SwapPartner
