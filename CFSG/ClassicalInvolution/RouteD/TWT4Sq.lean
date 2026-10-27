module

public import CFSG.ClassicalInvolution.RouteD.TWT4Cent
public import CFSG.ClassicalInvolution.RouteD.TWT4Sqrt
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Helpers

theorem commute_of_locMk_commute {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}
    (hP1 : LocalOddCentral Ω {x}) {c z' : ↥(locLayer Ω x)} (hz2 : z' * z' = 1)
    (h : locMk Ω x c * locMk Ω x z' = locMk Ω x z' * locMk Ω x c) : c * z' = z' * c := by
  set o : ↥(locLayer Ω x) := c * z' * c⁻¹ * z'⁻¹ with ho
  have hoO : o ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := by
    refine (QuotientGroup.eq_one_iff o).mp ?_
    show locMk Ω x o = 1
    rw [ho, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hoc : o ∈ Subgroup.center ↥(locLayer Ω x) := hP1 hoO
  have hz1 : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz2
  have hcz : c * z' * c⁻¹ = o * z' := by
    rw [ho, hz1, mul_assoc, mul_assoc, hz2, mul_one]
  have hsq : (o * z') * (o * z') = 1 := by
    rw [← hcz]
    calc c * z' * c⁻¹ * (c * z' * c⁻¹) = c * (z' * z') * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hoz : z' * o = o * z' := Subgroup.mem_center_iff.mp hoc z'
  have ho2 : o * o = 1 := by
    have h1 : (o * z') * (o * z') = (o * o) * (z' * z') := by
      calc (o * z') * (o * z') = o * (z' * o) * z' := by group
        _ = o * (o * z') * z' := by rw [hoz]
        _ = (o * o) * (z' * z') := by group
    rw [hz2, mul_one] at h1
    rw [← h1]
    exact hsq
  have ho1 : o = 1 := by
    set o' : ↥(classicalInvolutionOddCore ↥(locLayer Ω x)) := ⟨o, hoO⟩ with ho'
    have h2 : orderOf o' ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      show o ^ 2 = 1
      rw [pow_two, ho2]
    have h3 : orderOf o' ∣ Nat.card ↥(classicalInvolutionOddCore ↥(locLayer Ω x)) :=
      orderOf_dvd_natCard o'
    have h4 : Nat.Coprime 2 (Nat.card ↥(classicalInvolutionOddCore ↥(locLayer Ω x))) :=
      Nat.coprime_two_left.mpr (CFSG.ComponentClassification.OddCore.odd_card _)
    have h5 : orderOf o' ∣ 1 := by
      have := Nat.dvd_gcd h2 h3
      rwa [h4] at this
    have h6 : orderOf o' = 1 := Nat.dvd_one.mp h5
    have h7 : o' = 1 := orderOf_eq_one_iff.mp h6
    exact congrArg Subtype.val h7
  rw [ho1] at hcz
  rw [one_mul] at hcz
  rw [mul_inv_eq_iff_eq_mul] at hcz
  exact hcz

theorem eq_of_locMk_eq_of_mem {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}
    {M : Subgroup G}
    (hbot : M.subgroupOf (locLayer Ω x) ⊓ classicalInvolutionOddCore ↥(locLayer Ω x) = ⊥)
    {m m' : ↥(locLayer Ω x)} (hm : m ∈ M.subgroupOf (locLayer Ω x))
    (hm' : m' ∈ M.subgroupOf (locLayer Ω x)) (h : locMk Ω x m = locMk Ω x m') : m = m' := by
  have h1 : m⁻¹ * m' ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := QuotientGroup.eq.mp h
  have h2 : m⁻¹ * m' ∈ M.subgroupOf (locLayer Ω x) ⊓
      classicalInvolutionOddCore ↥(locLayer Ω x) :=
    ⟨(M.subgroupOf (locLayer Ω x)).mul_mem ((M.subgroupOf (locLayer Ω x)).inv_mem hm) hm', h1⟩
  rw [hbot, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.mp h2

end Helpers

section Visible

variable {p f : ℕ} [Fact p.Prime]


theorem exists_sqrt_visible (hmod : (p ^ f) % 4 = 3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {K T J : Subgroup G} {z t : G} (S : RouteDSetup p f K z)
    (e : TwinElt K T z) (A : AtT p f K T J z t .PSU 4) {M : Subgroup G}
    (hMu : M ∈ centralizingMembers (𝒞 K) {e.u}) (hMt : M ∈ centralizingMembers (𝒞 K) {t})
    (hMJ : M ≠ J) (hMJ₂ : M ≠ A.J₂) {w : G} (hw : IsClassicalMember p f M w) :
    ∃ c ∈ M, c * c = w ∧ c * z = z * c := by
  classical
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts A e
  obtain ⟨RM, hRM, hMR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
    A.hJiso A.hJ₂iso hMt hMJ hMJ₂
  have h1 : locImg (𝒞 K) t M ≤
      Subgroup.centralizer ({locMk (𝒞 K) t ⟨e.u, huY⟩} : Set _) :=
    (le_centralizer_iff_locImg S.inClass A.hP1 hMt ⟨e.u, huY⟩).mp hMu.2
  have h2 : RM ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv .PSU 4 p f Fact.out).K) :=
    (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf RM hRM) (ã * ã')).mpr (by
      rw [hψu, ← hMR]
      exact h1)
  have h3 : ∀ s ∈ RM, (ã * ã') * s = s * (ã * ã') := fun s hs =>
    (Subgroup.mem_centralizer_singleton_iff.mp (h2 hs)).symm
  obtain ⟨r, hrR, cm, hcmR, hr2, hr1, hrc, hcmc, hcma, hcma'⟩ := twinMF_sqrt_central S.odd S.five
    hmod A.hdat.toOn hãR hã'R hsq hsq' A.d.ψ A.d.ker_le hRM h3
  have hwY : w ∈ locLayer (𝒞 K) t := le_centralizingLayer hMt hw.mem
  have hψr : A.d.ψ r ∈ locImg (𝒞 K) t M := by
    rw [hMR]
    exact ⟨r, hrR, rfl⟩
  have hψc : A.d.ψ cm ∈ locImg (𝒞 K) t M := by
    rw [hMR]
    exact ⟨cm, hcmR, rfl⟩
  have hbot := TWZ.subgroupOf_inf_oddCore_eq_bot S.exact hMt
  obtain ⟨m, hm, hmr⟩ := hψr
  obtain ⟨c, hc, hcc⟩ := hψc
  have hm2 : m * m = 1 := by
    have hmem : m * m ∈ M.subgroupOf (locLayer (𝒞 K) t) ⊓
        classicalInvolutionOddCore ↥(locLayer (𝒞 K) t) := by
      refine ⟨mul_mem hm hm, ?_⟩
      show m * m ∈ classicalInvolutionOddCore ↥(locLayer (𝒞 K) t)
      refine (QuotientGroup.eq_one_iff (m * m)).mp ?_
      show locMk (𝒞 K) t (m * m) = 1
      rw [map_mul, hmr, ← map_mul, hr2, map_one]
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hm1 : m ≠ 1 := by
    intro h
    apply hr1
    rw [← hmr, h, map_one]
  have hUw := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hw
  have hmw : (m : G) = w := by
    rcases hUw.unique (m : G) (Subgroup.mem_subgroupOf.mp hm)
      (by simpa using congrArg Subtype.val hm2) with h | h
    · exact absurd (Subtype.ext h) hm1
    · exact h
  have hcsq : locMk (𝒞 K) t (c * c) = locMk (𝒞 K) t m := by
    rw [map_mul, hcc, ← map_mul, hcmc, hmr]
  have hcm : c * c = m := eq_of_locMk_eq_of_mem hbot (mul_mem hc hc) hm hcsq
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hζ : ã * ã * A.x⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p f Fact.out).K := hsq
  have hx_eq : A.x = (ã * ã * A.x⁻¹)⁻¹ * (ã * ã) := by group
  have hcmx : cm * A.x = A.x * cm := by
    have hcc' : cm * (ã * ã) = (ã * ã) * cm := by
      rw [← mul_assoc, hcma, mul_assoc, hcma, ← mul_assoc]
    have hz' := Subgroup.mem_center_iff.mp ((Subgroup.center _).inv_mem hζ) cm
    calc cm * A.x = cm * ((ã * ã * A.x⁻¹)⁻¹ * (ã * ã)) := by rw [← hx_eq]
      _ = (cm * (ã * ã * A.x⁻¹)⁻¹) * (ã * ã) := by group
      _ = ((ã * ã * A.x⁻¹)⁻¹ * cm) * (ã * ã) := by rw [hz']
      _ = (ã * ã * A.x⁻¹)⁻¹ * (cm * (ã * ã)) := by group
      _ = (ã * ã * A.x⁻¹)⁻¹ * ((ã * ã) * cm) := by rw [hcc']
      _ = A.x * cm := by rw [← mul_assoc, ← hx_eq]
  have hlz : locMk (𝒞 K) t c * locMk (𝒞 K) t ⟨z, A.hzY⟩ =
      locMk (𝒞 K) t ⟨z, A.hzY⟩ * locMk (𝒞 K) t c := by
    rw [← A.hxz, hcc, ← map_mul, ← map_mul, hcmx]
  have hcz := commute_of_locMk_commute A.hP1
    (c := c) (z' := ⟨z, A.hzY⟩) (Subtype.ext hz2) hlz
  refine ⟨(c : G), Subgroup.mem_subgroupOf.mp hc, ?_, congrArg Subtype.val hcz⟩
  rw [← hmw]
  exact congrArg Subtype.val hcm

end Visible

end CFSG.ClassicalInvolution.RouteD.TWT4
