module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec7l78_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem sec7l78_isSimpleGroup_oddCore_of_isOmega5 [Finite G] {X : Subgroup G}
    (h : IsOmega5 X) : IsSimpleGroup (X ⧸ oddCore X) :=
  (CFSG.LieType.Simplicity.fam_classical_converse (X ⧸ oddCore X)
    ⟨.PSp, 2, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)⟩).2.2

private theorem sec7l78_layerCent_subgroupOf (L : Subgroup G) (s : G) :
    (layerCent L s).subgroupOf (L ⊓ centralizer ({s} : Set G)) =
      CFSG.layer ↥(L ⊓ centralizer ({s} : Set G)) := by
  ext x
  rw [Subgroup.mem_subgroupOf, layerCent, CFSG.inSubgroup]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : y = x := Subtype.ext hyx
    simpa [hyx'] using hy
  · intro hx
    exact Subgroup.mem_map_of_mem (L ⊓ centralizer ({s} : Set G)).subtype hx

private theorem sec7l78_le_normalizer_layerCent (L : Subgroup G) (r : G) :
    (L ⊓ centralizer ({r} : Set G)) ≤ normalizer (layerCent L r : Set G) := by
  let H : Subgroup G := L ⊓ centralizer ({r} : Set G)
  have hEq : (layerCent L r).subgroupOf H = CFSG.layer ↥H :=
    sec7l78_layerCent_subgroupOf L r
  have hN : ((layerCent L r).subgroupOf H).Normal := by
    rw [hEq]
    haveI : (CFSG.layer ↥H).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hle : layerCent L r ≤ H := Subgroup.map_subtype_le (CFSG.layer ↥H)
  show H ≤ normalizer (layerCent L r : Set G)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hN

theorem sec7l78_odd_in_layer [Finite G] (hP : Asc82Tab6P) (hOm5 : Sec8T84FactOm5Out)
    {L : Subgroup G} (hL : IsOm6P L) {r : G} (hr : orderOf r = 2)
    (hrN : r ∈ normalizer (L : Set G)) (hα : ∃ α : ℤˣ, InducesTypeSome L r 6 1 1 α) {x : G}
    (hxL : x ∈ L) (hxr : x * r = r * x) (hodd : Odd (orderOf x)) : x ∈ layerCent L r := by
  let H : Subgroup G := L ⊓ centralizer ({r} : Set G)
  let Y : Subgroup G := layerCent L r
  have hOm5Y : IsOmega5 Y := hP.layer_i1 G L hL r hr hrN hα
  have hcomp : IsComponentIn Y H := isComponentIn_layerCent (L := L) (s := r) (Or.inl hOm5Y)
  have hYq : IsOm5Q Y := ⟨hcomp.isQuasisimple, hOm5Y⟩
  have hs : IsSimpleGroup (Y ⧸ oddCore Y) := sec7l78_isSimpleGroup_oddCore_of_isOmega5 hOm5Y
  have hxH : x ∈ H := by
    refine ⟨hxL, ?_⟩
    change x ∈ centralizer ({r} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hxr.symm
  have hxnorm : x ∈ normalizer (Y : Set G) :=
    (sec7l78_le_normalizer_layerCent L r) hxH
  obtain ⟨y, hyY, c, hcC, hxyc⟩ :=
    innerOn_decompose (hOm5 G Y hYq x hxnorm hodd)
  have hyH : y ∈ H := hcomp.le hyY
  have hyL : y ∈ L := hyH.1
  have hcL : c ∈ L := by
    have hceq : c = y⁻¹ * x := by rw [hxyc]; group
    rw [hceq]
    exact L.mul_mem (L.inv_mem hyL) hxL
  have hR : zpowers c ≤ normalizer (L : Set G) ⊓ centralizer (Y : Set G) := by
    refine le_inf ?_ ?_
    · rw [Subgroup.zpowers_le]; exact Subgroup.le_normalizer hcL
    · rw [Subgroup.zpowers_le]; exact hcC
  have hrel_le : (centralizer (L : Set G)).relIndex (zpowers c) ≤ 2 :=
    hP.aut_cent_i1 G L hL r hr hrN hα (zpowers c) hR
  have hsub : (centralizer (L : Set G)).subgroupOf (zpowers c) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    have hzL : (z : G) ∈ L := Subgroup.zpowers_le.mpr hcL z.2
    have hzc : (z : G) ∈ centerIn L := by
      rw [centerIn, Subgroup.mem_map]
      refine ⟨⟨(z : G), hzL⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro a
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz a a.2)
    have hz1 : (z : G) = 1 := by
      have hbot := hP.center_triv G L hL
      rw [hbot] at hzc
      simpa using hzc
    exact Subtype.ext hz1
  have hrel_eq : (centralizer (L : Set G)).relIndex (zpowers c) = orderOf c := by
    rw [Subgroup.relIndex, hsub, Subgroup.index_bot, Nat.card_zpowers]
  have horder_le : orderOf c ≤ 2 := hrel_eq ▸ hrel_le
  have hpos : 0 < orderOf c := (isOfFinOrder_of_finite c).orderOf_pos
  have hcases : orderOf c = 1 ∨ orderOf c = 2 := by omega
  have hc2 : c * c = 1 := by
    have h2 : c ^ 2 = 1 := by
      rcases hcases with h | h
      · rw [orderOf_eq_one_iff.mp h]; simp
      · rw [← h]; exact pow_orderOf_eq_one c
    rwa [pow_two] at h2
  have hyc : Commute y c := Subgroup.mem_centralizer_iff.mp hcC y hyY
  have hcm : c ^ orderOf x = (y ^ orderOf x)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← hyc.mul_pow (orderOf x)]
    rw [← hxyc]
    exact pow_orderOf_eq_one x
  have hcmY : c ^ orderOf x ∈ Y := by
    rw [hcm]
    exact Y.inv_mem (Y.pow_mem hyY _)
  have hcm_eq_c : c ^ orderOf x = c := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, pow_two, hc2, one_pow, one_mul]
  have hcY : c ∈ Y := hcm_eq_c ▸ hcmY
  have hcO : (⟨c, hcY⟩ : ↥Y) ∈ CFSG.oddCore ↥Y := by
    rw [← center_eq_oddCore_of_simple hYq.1 hs]
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC z z.2)
  have hdvd : orderOf (⟨c, hcY⟩ : ↥Y) ∣ Nat.card (CFSG.oddCore ↥Y) :=
    (CFSG.oddCore ↥Y).orderOf_dvd_natCard hcO
  have hodd_c : Odd (orderOf c) := by
    have h := (sec7l78_odd_card_oddCore ↥Y).of_dvd_nat hdvd
    rwa [Subgroup.orderOf_mk c hcY] at h
  have hc1 : c = 1 := by
    have hdvd2 : orderOf c ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hc2)
    have h1 : orderOf c = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact h
      · rw [h] at hodd_c
        obtain ⟨k, hk⟩ := hodd_c
        omega
    exact orderOf_eq_one_iff.mp h1
  rw [hxyc, hc1, mul_one]
  exact hyY

end CFSG.OddStandard.SmallF3.Omega
