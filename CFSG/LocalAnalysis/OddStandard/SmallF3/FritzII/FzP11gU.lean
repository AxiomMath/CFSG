module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32CaseA

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.Asc76X
open CFSG.ComponentClassification.AschbacherToolkit.Bender
  (sylowCenter mem_sylowCenter map_center_eq_sylowCenter)

theorem fz_not_u34 {X : Type} [Group X] [Finite X] {S Q : Subgroup X} (hS : IsSylowOf 2 S ⊤)
    (hQS : Q ≤ S) (hQ4 : Nat.card Q = 4) (hQ2 : ∀ x ∈ Q, x ^ 2 = 1)
    (hQc : Q ⊓ ⁅S, S⁆ = ⊥) :
    ¬ Nonempty (↥(normalClosure (Q : Set X)) ⧸ CFSG.Assembly.oddCore ↥(normalClosure (Q : Set X))
      ≃* PSU3 2 2) := by
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup X := normalClosure (Q : Set X) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hQM : Q ≤ M := subset_normalClosure
  have hQ2g : IsPGroup 2 Q := hS.isPGroup.to_le hQS
  have hQb4 : Nat.card (bar M Q) = 4 := by
    rw [card_bar_of_pGroup hQM hQ2g, hQ4]
  have hSb : IsSylowOf 2 (bar M S) ⊤ :=
    CFSG.ComponentClassification.Asc76X.Hall32.isSylowOf_bar hMn hS
  obtain ⟨P₀, hP₀⟩ := exists_sylow_eq_of_isSylowOf_top hSb
  have hB : fusionBenderBorel (BarGroup M) (2 ^ 2) 3 :=
    fusionBenderBorel_of_mulEquiv_psu3 (le_refl 2) e
  have hQbar_sq : ∀ x ∈ bar M Q, x ^ 2 = 1 := by
    rintro x ⟨q, hq, rfl⟩
    rw [← map_pow, show q ^ 2 = 1 from Subtype.ext (by simpa using hQ2 (q : X) hq), map_one]
  have hQleZ : bar M Q ≤ sylowCenter (bar M S) := by
    intro x hx
    refine mem_sylowCenter.mpr ⟨bar_mono hQS hx, ?_⟩
    intro t ht
    have hcent := mem_centralizer_of_fusionBenderBorel hB (by norm_num) P₀
      (by rw [hP₀]; exact bar_mono hQS hx) (hQbar_sq x hx)
    exact mem_centralizer_iff.mp hcent t (by rw [hP₀]; exact ht)
  have hZ4 : Nat.card (sylowCenter (bar M S)) = 4 := by
    have h2 := (hB P₀).2.2.2.1
    rw [CFSG.ComponentClassification.Asc76X.Hall32.card_center_eq_card_sylowCenter, hP₀] at h2
    rw [h2]
    norm_num
  have hQZ : bar M Q = sylowCenter (bar M S) :=
    eq_of_le_of_card_ge hQleZ (by rw [hZ4, hQb4])
  have hP64 : Nat.card ↥(bar M S) = 64 := by
    have h2 := (hB P₀).2.2.2.2
    rw [hP₀] at h2
    rw [h2]
    norm_num
  have hZc4 : Nat.card (Subgroup.center ↥(bar M S)) = 4 := by
    rw [CFSG.ComponentClassification.Asc76X.Hall32.card_center_eq_card_sylowCenter (bar M S), hZ4]
  have hPnab : ¬ IsMulCommutative ↥(bar M S) := by
    intro hcomm
    have htop : Subgroup.center ↥(bar M S) = ⊤ := center_eq_top_iff.mpr hcomm
    have hcard : Nat.card (Subgroup.center ↥(bar M S)) = Nat.card ↥(bar M S) := by
      rw [htop, Subgroup.card_top]
    rw [hZc4, hP64] at hcard
    norm_num at hcard
  haveI : Group.IsNilpotent ↥(bar M S) := hSb.isPGroup.isNilpotent
  have hDne : _root_.commutator ↥(bar M S) ≠ ⊥ := fun h =>
    hPnab ((_root_.commutator_eq_bot_iff ↥(bar M S)).mp h)
  have hInt : _root_.commutator ↥(bar M S) ⊓ Subgroup.center ↥(bar M S) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hDne
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hInt
  let u : ↥(bar M S) := (z : ↥(bar M S))
  have huD : u ∈ _root_.commutator ↥(bar M S) := (Subgroup.mem_inf.mp z.2).1
  have huC : u ∈ Subgroup.center ↥(bar M S) := (Subgroup.mem_inf.mp z.2).2
  have hu1 : u ≠ 1 := fun h => hz1 (Subtype.ext h)
  let ub : BarGroup M := (u : BarGroup M)
  have hAcomm : (⁅S.subgroupOf M, S.subgroupOf M⁆).map M.subtype ≤ ⁅S, S⁆ := by
    rw [Subgroup.map_commutator (S.subgroupOf M) (S.subgroupOf M) M.subtype,
      Subgroup.subgroupOf_map_subtype]
    exact Subgroup.commutator_mono inf_le_left inf_le_left
  have hDle : ⁅bar M S, bar M S⁆ ≤ bar M ⁅S, S⁆ := by
    have h1 : ⁅bar M S, bar M S⁆ = (⁅S.subgroupOf M, S.subgroupOf M⁆).map (barMk M) := by
      rw [Subgroup.map_commutator (S.subgroupOf M) (S.subgroupOf M) (barMk M)]
      rfl
    rw [h1, bar]
    refine map_mono fun c hc => ?_
    rw [Subgroup.mem_subgroupOf]
    exact hAcomm (Subgroup.mem_map_of_mem M.subtype hc)
  have hubD : ub ∈ ⁅bar M S, bar M S⁆ := by
    have h := Subgroup.mem_map_of_mem (bar M S).subtype huD
    rw [Subgroup.map_subtype_commutator (bar M S)] at h
    exact h
  have hubZ : ub ∈ sylowCenter (bar M S) := by
    have h := Subgroup.mem_map_of_mem (bar M S).subtype huC
    rw [map_center_eq_sylowCenter (bar M S)] at h
    exact h
  have hubQ : ub ∈ bar M Q := by rw [hQZ]; exact hubZ
  obtain ⟨c, hc, hcu⟩ := hDle hubD
  obtain ⟨q, hq, hqu⟩ := hubQ
  have hker : barMk M (q⁻¹ * c) = 1 := by
    rw [map_mul, map_inv, hqu, hcu, inv_mul_cancel]
  have hqS : q ∈ S.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (hQS (Subgroup.mem_subgroupOf.mp hq))
  have hcS : c ∈ S.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr
      (Subgroup.commutator_le_self S (Subgroup.mem_subgroupOf.mp hc))
  have hqcS : q⁻¹ * c ∈ S.subgroupOf M := mul_mem (inv_mem hqS) hcS
  have hS2M : IsPGroup 2 (S.subgroupOf M) :=
    hS.isPGroup.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨k, hk⟩ := hS2M ⟨q⁻¹ * c, hqcS⟩
  have hpow : (q⁻¹ * c) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hqc1 : q⁻¹ * c = 1 :=
    eq_one_of_two_element_of_ker (barMk M) (odd_card_ker_barMk M) (k := k) hpow hker
  have hqceq : q = c := inv_mul_eq_one.mp hqc1
  have hqmem : (q : X) ∈ Q ⊓ ⁅S, S⁆ :=
    mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hq,
      hqceq ▸ Subgroup.mem_subgroupOf.mp hc⟩
  have hqbot : (q : X) ∈ (⊥ : Subgroup X) := by rw [← hQc]; exact hqmem
  have hq1X : (q : X) = 1 := by simpa using hqbot
  have hq1 : q = 1 := Subtype.ext hq1X
  have hub1 : ub = 1 := by rw [← hqu, hq1, map_one]
  exact hu1 (Subtype.ext hub1)

end CFSG.OddStandard.SmallF3.FritzII
