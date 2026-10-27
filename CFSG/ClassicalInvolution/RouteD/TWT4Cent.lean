module

public import CFSG.ClassicalInvolution.RouteD.TWT4Inv
public import CFSG.ClassicalInvolution.RouteD.TWT4Vis
public import CFSG.ClassicalInvolution.RouteD.TWZAct
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

section Cent

variable {p f : ℕ} [Fact p.Prime]


theorem visible_involution_central (hmod : (p ^ f) % 4 = 3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {K T J : Subgroup G} {z t : G} (S : RouteDSetup p f K z)
    (e : TwinElt K T z) (hT : IsTwinAt (𝒞 K) K T z) (A : AtT p f K T J z t .PSU 4)
    (hJu : J ∈ centralizingMembers (𝒞 K) {e.u})
    (hJ₂u : A.J₂ ∈ centralizingMembers (𝒞 K) {e.u}) {M : Subgroup G}
    (hMu : M ∈ centralizingMembers (𝒞 K) {e.u}) (hMt : M ∈ centralizingMembers (𝒞 K) {t})
    (hMJ : M ≠ J) (hMJ₂ : M ≠ A.J₂) {w : G} (hw : IsClassicalMember p f M w) :
    ∀ y ∈ centralizingLayer (𝒞 K) {t}, (w * e.u) * y = y * (w * e.u) := by
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
  obtain ⟨r, hrR, hr2, hr1, hrc⟩ := twinMF_inv_central S.odd S.five hmod A.hdat.toOn hãR hã'R
    hsq hsq' A.d.ψ A.d.ker_le hRM h3
  have hwY : w ∈ locLayer (𝒞 K) t := le_centralizingLayer hMt hw.mem
  have hψr : A.d.ψ r ∈ locImg (𝒞 K) t M := by
    rw [hMR]
    exact ⟨r, hrR, rfl⟩
  obtain ⟨m, hm, hmr⟩ := hψr
  have hm2 : m * m = 1 := by
    have hmem : m * m ∈ M.subgroupOf (locLayer (𝒞 K) t) ⊓
        classicalInvolutionOddCore ↥(locLayer (𝒞 K) t) := by
      refine ⟨mul_mem hm hm, ?_⟩
      show m * m ∈ classicalInvolutionOddCore ↥(locLayer (𝒞 K) t)
      refine (QuotientGroup.eq_one_iff (m * m)).mp ?_
      show locMk (𝒞 K) t (m * m) = 1
      rw [map_mul, hmr, ← map_mul, hr2, map_one]
    rw [TWZ.subgroupOf_inf_oddCore_eq_bot S.exact hMt] at hmem
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
  have hmw' : m = ⟨w, hwY⟩ := Subtype.ext hmw
  set v : G := w * e.u with hv
  have hvY : v ∈ locLayer (𝒞 K) t := mul_mem hwY huY
  set c : (modelUniv .PSU 4 p f Fact.out).K := r * (ã * ã') with hc
  have hψv : locMk (𝒞 K) t ⟨v, hvY⟩ = A.d.ψ c := by
    have e1 : (⟨v, hvY⟩ : ↥(locLayer (𝒞 K) t)) = ⟨w, hwY⟩ * ⟨e.u, huY⟩ := rfl
    rw [e1, map_mul, ← hmw', hmr, hc, map_mul, hψu]
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT' hz2
  have hw2 : w * w = 1 := mul_self_eq_one_of_orderOf_eq_two hw.orderOf_eq_two
  have hwu : w * e.u = e.u * w := Subgroup.mem_centralizer_singleton_iff.mp (hMu.2 hw.mem)
  have hv2 : v * v = 1 := by
    calc v * v = w * (e.u * w) * e.u := by rw [hv]; group
      _ = w * (w * e.u) * e.u := by rw [← hwu]
      _ = (w * w) * (e.u * e.u) := by group
      _ = 1 := by rw [hw2, hu2, one_mul]
  have hvY2 : (⟨v, hvY⟩ : ↥(locLayer (𝒞 K) t)) * ⟨v, hvY⟩ = 1 := Subtype.ext hv2
  have hmember : ∀ L ∈ centralizingMembers (𝒞 K) {t},
      L ≤ Subgroup.centralizer ({v} : Set G) := by
    intro L hL
    by_cases hLJ : L = J
    · rw [hLJ]
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : y * w = w * y := A.hJiso M hMt hMJ y hy w hw.mem
      have h2 : y * e.u = e.u * y := Subgroup.mem_centralizer_singleton_iff.mp (hJu.2 hy)
      calc y * (w * e.u) = (y * w) * e.u := by group
        _ = (w * y) * e.u := by rw [h1]
        _ = w * (y * e.u) := by group
        _ = w * (e.u * y) := by rw [h2]
        _ = (w * e.u) * y := by group
    by_cases hLJ₂ : L = A.J₂
    · rw [hLJ₂]
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : y * w = w * y := A.hJ₂iso M hMt hMJ₂ y hy w hw.mem
      have h2 : y * e.u = e.u * y := Subgroup.mem_centralizer_singleton_iff.mp (hJ₂u.2 hy)
      calc y * (w * e.u) = (y * w) * e.u := by group
        _ = (w * y) * e.u := by rw [h1]
        _ = w * (y * e.u) := by group
        _ = w * (e.u * y) := by rw [h2]
        _ = (w * e.u) * y := by group
    obtain ⟨RL, hRL, hLR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
      A.hJiso A.hJ₂iso hL hLJ hLJ₂
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyY : y ∈ locLayer (𝒞 K) t := le_centralizingLayer hL hy
    have hys : locMk (𝒞 K) t ⟨y, hyY⟩ ∈ RL.map A.d.ψ := by
      rw [← hLR]
      exact ⟨⟨y, hyY⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    obtain ⟨s, hs, hsy⟩ := hys
    set yY : ↥(locLayer (𝒞 K) t) := ⟨y, hyY⟩ with hyYdef
    have hb : (yY * ⟨v, hvY⟩ * yY⁻¹) * (yY * ⟨v, hvY⟩ * yY⁻¹) = 1 := by
      calc (yY * ⟨v, hvY⟩ * yY⁻¹) * (yY * ⟨v, hvY⟩ * yY⁻¹)
          = yY * (⟨v, hvY⟩ * ⟨v, hvY⟩) * yY⁻¹ := by group
        _ = 1 := by rw [hvY2]; group
    have hcomm : A.d.ψ s * A.d.ψ c = A.d.ψ c * A.d.ψ s := by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hrc s]
    have heq := eq_of_involutions_of_mk A.hP1 hvY2 hb (by
      show locMk (𝒞 K) t ⟨v, hvY⟩ = locMk (𝒞 K) t (yY * ⟨v, hvY⟩ * yY⁻¹)
      rw [map_mul, map_mul, map_inv, hψv, ← hsy]
      exact (mul_inv_eq_iff_eq_mul.mpr hcomm).symm)
    have hval := congrArg Subtype.val heq
    have hval' : v = y * v * y⁻¹ := hval
    calc y * v = (y * v * y⁻¹) * y := by group
      _ = v * y := by rw [← hval']
  intro y hy
  have hy' : y ∈ Subgroup.centralizer ({v} : Set G) :=
    (iSup₂_le hmember : centralizingLayer (𝒞 K) {t} ≤ Subgroup.centralizer ({v} : Set G)) hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp hy').symm

end Cent

end CFSG.ClassicalInvolution.RouteD.TWT4
