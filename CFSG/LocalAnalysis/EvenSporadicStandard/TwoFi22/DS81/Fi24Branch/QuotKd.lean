module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotKc
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.PerfectCover

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C] [Finite C] {c : CInv C} {R : Subgroup C} {L1 : Subgroup c.Qt}

private theorem zpowers_mem_center {C : Type} [Group C] (c : CInv C) {x : C}
    (hx : x ∈ zpowers c.z) : x ∈ Subgroup.center C :=
  (Subgroup.zpowers_le (H := Subgroup.center C)).mpr
    (Subgroup.mem_center_iff.mpr c.central) hx

theorem exists_cover (hR : RData c R) (h : UniqueComp c R L1) :
    ∃ (Yh : Type) (_ : Group Yh) (π : Yh →* ↥L1), Function.Surjective π ∧
      commutator Yh = ⊤ ∧ π.ker ≤ center Yh ∧ Nat.card π.ker = 2 := by
  let P : Subgroup C := L1.comap c.qmap
  have hzP : c.z ∈ P := by
    rw [Subgroup.mem_comap, c.qmap_eq_one_iff.mpr (Subgroup.mem_zpowers c.z)]
    exact L1.one_mem
  have hzP_le : zpowers c.z ≤ P := Subgroup.zpowers_le.mpr hzP
  have hbarP : c.bar P = L1 := c.bar_comap L1
  have hbarcomm : c.bar ⁅P, P⁆ = c.bar P := by
    rw [c.bar_commutator, hbarP, L1_perfect h]
  have h2 : (c.bar ⁅P, P⁆).comap c.qmap = ⁅P, P⁆ ⊔ zpowers c.z := by
    change ((⁅P, P⁆).map c.qmap).comap c.qmap = ⁅P, P⁆ ⊔ zpowers c.z
    rw [Subgroup.comap_map_eq, c.ker_qmap]
  have hperf : ⁅P, P⁆ ⊔ zpowers c.z = P := by
    rw [← h2, hbarcomm]
    exact c.comap_bar hzP_le
  obtain ⟨L, hLP, hLperf, hLz⟩ := exists_perfect_cover c.central c.sq c.ne hzP hperf
  have hRP : R ≤ P := (Subgroup.map_le_iff_le_comap).mp h.R_le
  have hR2 : IsPGroup 2 ↥R := IsPGroup.of_card (p := 2) (n := 13) hR.card
  have hRcard : 2 < Nat.card ↥R := by rw [hR.card]; norm_num
  have hzL : c.z ∈ L :=
    z_mem_of_perfect_cover c.central c.sq c.ne hRP hR.z_mem hR2 hRcard hR.center hLP hLz
  have hzL_le : zpowers c.z ≤ L := Subgroup.zpowers_le.mpr hzL
  let π : ↥L →* ↥L1 :=
    (c.qmap.comp L.subtype).codRestrict L1 fun x => Subgroup.mem_comap.mp (hLP x.2)
  have hπval : ∀ x : ↥L, (π x : c.Qt) = c.qmap (x : C) := fun _ => rfl
  have hsurj : Function.Surjective π := by
    intro y
    have hy : (y : c.Qt) ∈ c.bar P := by rw [hbarP]; exact y.2
    obtain ⟨p, hpP, hpy⟩ := hy
    have hp : p ∈ L ⊔ zpowers c.z := by rw [hLz]; exact hpP
    rw [Subgroup.mem_sup_of_normal_right] at hp
    obtain ⟨l, hlL, w, hwz, hlw⟩ := hp
    refine ⟨⟨l, hlL⟩, ?_⟩
    apply Subtype.ext
    show c.qmap l = (y : c.Qt)
    have hw1 : c.qmap w = 1 := c.qmap_eq_one_iff.mpr hwz
    rw [← hpy, ← hlw, map_mul, hw1, mul_one]
  have hker_center : π.ker ≤ center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hq : c.qmap (x : C) = 1 := by
      have hmem := MonoidHom.mem_ker.mp hx
      have h2 := congrArg (fun y : ↥L1 => (y : c.Qt)) hmem
      rw [hπval x] at h2
      simpa using h2
    have hxcen : (x : C) ∈ Subgroup.center C :=
      zpowers_mem_center c (c.qmap_eq_one_iff.mp hq)
    exact Subtype.ext (by simpa using Subgroup.mem_center_iff.mp hxcen (g : C))
  have hmapker : π.ker.map L.subtype = zpowers c.z := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hq : c.qmap (x : C) = 1 := by
        have hmem := MonoidHom.mem_ker.mp hx
        have h2 := congrArg (fun y : ↥L1 => (y : c.Qt)) hmem
        rw [hπval x] at h2
        simpa using h2
      exact c.qmap_eq_one_iff.mp hq
    · intro hy
      refine ⟨⟨y, hzL_le hy⟩, ?_, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      show c.qmap y = (1 : c.Qt)
      exact c.qmap_eq_one_iff.mpr hy
  have hker : Nat.card ↥π.ker = 2 := by
    rw [← Subgroup.card_map_of_injective L.subtype_injective (K := π.ker), hmapker,
      c.card_zpowers]
  have hcommL : commutator ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subtype_commutator, hLperf, Subgroup.map_top, Subgroup.range_subtype]
  exact ⟨↥L, inferInstance, π, hsurj, hcommL, hker_center, hker⟩

theorem two_pow_19_dvd (hC : CCore c) (hcat : CatSections C) (hSch : CatalogOuterSolvable)
    (h : UniqueComp c R L1) {Y0 : Subgroup C} (hY0 : Y0Data Y0) :
    2 ^ 19 ∣ Nat.card ↥L1 := by
  have hbar : c.bar Y0 ≤ L1 := perfect_le_L1 hC hcat hSch h (c.bar_perfect hY0.perfect)
  have hdvd : Nat.card ↥(c.bar Y0) ∣ Nat.card ↥L1 := Subgroup.card_dvd_of_le hbar
  have hcard : Nat.card ((zpowers c.z).subgroupOf Y0) * Nat.card ↥(c.bar Y0) =
      2 ^ 20 * 3 ^ 3 * 5 := by
    have h := Subgroup.card_ker_mul_card_range (c.qmap.domRestrict Y0)
    rw [MonoidHom.ker_domRestrict, c.ker_qmap, MonoidHom.domRestrict_range, hY0.card] at h
    exact h
  have hkerdvd : Nat.card ((zpowers c.z).subgroupOf Y0) ∣ 2 := by
    have hle : ((zpowers c.z).subgroupOf Y0).map Y0.subtype ≤ zpowers c.z := by
      rintro x ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    have hd := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective Y0.subtype_injective
      (K := (zpowers c.z).subgroupOf Y0), c.card_zpowers] at hd
  have h19 : 2 ^ 19 ∣ Nat.card ↥(c.bar Y0) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hkerdvd with hk | hk
    · rw [hk, one_mul] at hcard
      rw [hcard]
      exact ⟨2 * 3 ^ 3 * 5, by norm_num⟩
    · rw [hk] at hcard
      have hm : Nat.card ↥(c.bar Y0) = 2 ^ 19 * 3 ^ 3 * 5 := by
        norm_num at hcard ⊢
        omega
      rw [hm]
      exact ⟨3 ^ 3 * 5, by norm_num⟩
  exact h19.trans hdvd

theorem not_two_pow_21_dvd (hC : CCore c) (L1 : Subgroup c.Qt) : ¬ 2 ^ 21 ∣ Nat.card ↥L1 := by
  intro h21
  apply hC.two_part
  have hcardC : Nat.card C = 2 * Nat.card c.Qt := by
    have h := c.card_bar (S := ⊤) le_top
    rw [Subgroup.card_top] at h
    have hbar : c.bar ⊤ = ⊤ := by
      change (⊤ : Subgroup C).map c.qmap = ⊤
      rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr c.qmap_surjective]
    rw [hbar, Subgroup.card_top] at h
    exact h
  rw [hcardC, show 2 ^ 22 = 2 * 2 ^ 21 by norm_num]
  exact mul_dvd_mul_left 2 (dvd_trans h21 (Subgroup.card_subgroup_dvd_card L1))

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
