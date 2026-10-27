module

public import CFSG.ClassicalInvolution.SmallCases.NDBC1
import CFSG.ClassicalInvolution.Asc77.WP3SCUTq
import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa
import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinSide
import CFSG.ClassicalInvolution.Asc77.AscE189Lift
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyFrames
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
import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3
import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace Cover

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem conjSub_eq_of_centralizes (hΩ : ConjInvariant Ω) (hz2 : IsPGroup 2 (Subgroup.zpowers z))
    {N : Subgroup G} (hN : N ∈ tqMembers Ω z) {n : G} (hn : IsClassicalMember p f N n) {x : G}
    (hxC : x ∈ Subgroup.centralizer ({z} : Set G)) (hxn : x * n = n * x)
    (hcent : ∀ y ∈ modOdd z (exactCore z N), oddQuotMk z ⟨x, hxC⟩ * y = y * oddQuotMk z ⟨x, hxC⟩) :
    conjSub x N = N := by
  have hN' : conjSub x N ∈ tqMembers Ω z := conjSub_mem_tqMembers hΩ hxC hN
  have hn' : IsClassicalMember p f (conjSub x N) n := by
    have h := hn.conj x
    have e : x * n * x⁻¹ = n := by rw [hxn]; group
    rwa [e] at h
  refine eq_of_modOdd_exactCore_eq hn' hn hz2 hN'.2 hN.2 ?_
  have e1 : exactCore z (conjSub x N) = conjSub x (exactCore z N) := by
    have h := exactCore_conjSub x z N
    rwa [Bootstrap.conj_eq_of_mem_centralizer_singleton hxC] at h
  rw [e1, Asc77.modOdd_conjSub_of_mem_centralizer hxC, Asc77.conjSub_eq_of_forall_commute]
  exact fun y hy => (hcent y hy).symm

theorem exists_fuzzyFrameOn_of_commute (C : Asc77.XCtx p f Ω z) {N₁ N₂ : Subgroup G}
    (h₁ : N₁ ∈ tqMembers Ω z) (h₂ : N₂ ∈ tqMembers Ω z) {n₁ n₂ : G}
    (hn₁ : IsClassicalMember p f N₁ n₁) (hn₂ : IsClassicalMember p f N₂ n₂)
    (hcomm : ∀ x ∈ modOdd z (exactCore z N₁), ∀ y ∈ modOdd z (exactCore z N₂), x * y = y * x)
    (h1z : oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ ≠
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩)
    (h2z : oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ ≠
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩)
    (h12 : oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ ≠
      oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩)
    (h12z : oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ *
      oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ ≠
        oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩) :
    ∃ A : Subgroup G, Theorem5.FuzzyFrameOn p f Ω A := by
  have hzC := Asc77.XCtx.hzC z
  have hΩ := C.hΩ.conjInvariant
  have hn₁C := C.involution_mem_centralizer h₁ hn₁
  have hn₂C := C.involution_mem_centralizer h₂ hn₂
  have hc₁ := hn₁.isCentralInvolution
  have hc₂ := hn₂.isCentralInvolution
  have hn₁E := C.involution_mem_exactCore h₁ hn₁
  have hn₂E := C.involution_mem_exactCore h₂ hn₂
  have hn₂N : oddQuotMk z ⟨n₂, hn₂C⟩ ∈ modOdd z (exactCore z N₂) :=
    oddQuotMk_mem_modOdd hn₂E hn₂C
  have hn₁N : oddQuotMk z ⟨n₁, hn₁C⟩ ∈ modOdd z (exactCore z N₁) :=
    oddQuotMk_mem_modOdd hn₁E hn₁C
  obtain ⟨o, ho, hoc⟩ := Asc77.exists_conj_involution_commuting
    (N := oddCoreIn (Subgroup.centralizer ({z} : Set G))) (odd_card_oddCoreIn _)
    (F := Subgroup.zpowers n₁) (Subgroup.zpowers_le.mpr (normalizer_oddCoreIn _ hn₁C))
    (isPGroup_zpowers_of_sq_eq_one hc₁.sq) hc₂.sq (fun x hx => by
      have hxE : x ∈ exactCore z N₁ := (Subgroup.zpowers_le.mpr hn₁E) hx
      have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := (Subgroup.zpowers_le.mpr hn₁C) hx
      have hcx := hcomm _ (oddQuotMk_mem_modOdd hxE hxC) _ hn₂N
      have h := (DeltaClosure.mk_comm_eq_iff hxC hn₂C).mp hcx
      have e : n₂⁻¹ = n₂ := inv_eq_of_mul_eq_one_left hc₂.sq
      rwa [e] at h)
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho
  set n₂' := o * n₂ * o⁻¹ with hn₂'def
  have hn₁₂ : n₁ * n₂' = n₂' * n₁ := hoc n₁ (Subgroup.mem_zpowers n₁)
  have h₂' : conjSub o N₂ ∈ tqMembers Ω z := conjSub_mem_tqMembers hΩ hoC h₂
  have hn₂' : IsClassicalMember p f (conjSub o N₂) n₂' := hn₂.conj o
  have hn₂'C : n₂' ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hoC hn₂C) (Subgroup.inv_mem _ hoC)
  have ho1 : oddQuotMk z ⟨o, hoC⟩ = 1 := by
    apply oddQuotMk_eq_one_iff.mpr
    obtain ⟨o', ho', rfl⟩ := ho
    exact ho'
  have hbar : oddQuotMk z ⟨n₂', hn₂'C⟩ = oddQuotMk z ⟨n₂, hn₂C⟩ := by
    have e : (⟨n₂', hn₂'C⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨o, hoC⟩ * ⟨n₂, hn₂C⟩ * ⟨o, hoC⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, ho1]
    group
  have himg : modOdd z (exactCore z (conjSub o N₂)) = modOdd z (exactCore z N₂) := by
    have h := exactCore_conjSub o z N₂
    rw [Bootstrap.conj_eq_of_mem_centralizer_singleton hoC] at h
    rw [h, Asc77.modOdd_conjSub_of_mem_oddCoreIn ho]
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; have := C.hq; simp at this)
  have hzn₁ : z ≠ n₁ := by
    rintro rfl
    exact h1z rfl
  have hzn₂' : z ≠ n₂' := fun h =>
    h2z (by rw [← hbar]; exact congrArg (oddQuotMk z) (Subtype.ext h.symm))
  have hn₁n₂' : n₁ ≠ n₂' := fun h =>
    h12 (by rw [← hbar]; exact congrArg (oddQuotMk z) (Subtype.ext h))
  have hzn₁c : z * n₁ = n₁ * z := (Subgroup.mem_centralizer_singleton_iff.mp hn₁C).symm
  have hind : z * n₁ ≠ n₂' := by
    intro h
    have hmap : oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨n₁, hn₁C⟩ = oddQuotMk z ⟨n₂', hn₂'C⟩ := by
      rw [← map_mul]
      exact congrArg (oddQuotMk z) (Subtype.ext h)
    have hcz : oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨n₁, hn₁C⟩ =
        oddQuotMk z ⟨n₁, hn₁C⟩ * oddQuotMk z ⟨z, hzC⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk z) (Subtype.ext hzn₁c)
    have hsq : oddQuotMk z ⟨n₁, hn₁C⟩ * oddQuotMk z ⟨n₁, hn₁C⟩ = 1 := by
      rw [← map_mul]
      have e : (⟨n₁, hn₁C⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨n₁, hn₁C⟩ = 1 :=
        Subtype.ext hc₁.sq
      rw [e, map_one]
    apply h12z
    rw [← hbar, ← hmap, hcz, ← mul_assoc, hsq, one_mul]
  have hN₁K : N₁ ≠ C.K := by
    rintro rfl
    exact hzn₁ (hn₁.eq_of_isCentralInvolution C.hp hf C.K_cl.isCentralInvolution)
  have hN₂K : conjSub o N₂ ≠ C.K := by
    intro h
    rw [h] at hn₂'
    exact hzn₂' (hn₂'.eq_of_isCentralInvolution C.hp hf C.K_cl.isCentralInvolution)
  have hq₁ := mem_trivialOnQuot_K C h₁ hn₁ hN₁K
  have hq₂ := mem_trivialOnQuot_K C h₂' hn₂' hN₂K
  have hcent₁ : ∀ y ∈ modOdd z (exactCore z N₁),
      oddQuotMk z ⟨n₂', hn₂'C⟩ * y = y * oddQuotMk z ⟨n₂', hn₂'C⟩ := by
    rw [hbar]
    exact fun y hy => (hcomm y hy _ hn₂N).symm
  have hcent₂ : ∀ y ∈ modOdd z (exactCore z (conjSub o N₂)),
      oddQuotMk z ⟨n₁, hn₁C⟩ * y = y * oddQuotMk z ⟨n₁, hn₁C⟩ := by
    rw [himg]
    exact fun y hy => hcomm _ hn₁N y hy
  have hnorm₁ := conjSub_eq_of_centralizes hΩ C.hc2 h₁ hn₁ hn₂'C hn₁₂.symm hcent₁
  have hnorm₂ := conjSub_eq_of_centralizes hΩ C.hc2 h₂' hn₂' hn₁C hn₁₂ hcent₂
  have ht₁₂ : n₂' ∈ Bootstrap.trivialOnQuot N₁ :=
    Asc77.mem_trivialOnQuot_of_centralizes_modOdd hn₁ C.hc2 h₁.2 hn₂'C
      (Asc77.mem_normalizer_iff_conjSub_eq.mpr hnorm₁) hcent₁
  have ht₂₁ : n₁ ∈ Bootstrap.trivialOnQuot (conjSub o N₂) :=
    Asc77.mem_trivialOnQuot_of_centralizes_modOdd hn₂' C.hc2 h₂'.2 hn₁C
      (Asc77.mem_normalizer_iff_conjSub_eq.mpr hnorm₂) hcent₂
  have hT : Bootstrap.AxisTriangle p f C.K N₁ (conjSub o N₂) z n₁ n₂' :=
    { cls₁ := C.K_cl
      cls₂ := hn₁
      cls₃ := hn₂'
      comm₁₂ := hzn₁c
      comm₁₃ := (Subgroup.mem_centralizer_singleton_iff.mp hn₂'C).symm
      comm₂₃ := hn₁₂
      tq₁₂ := hq₁
      tq₁₃ := hq₂
      tq₂₁ := h₁.2
      tq₂₃ := ht₁₂
      tq₃₁ := h₂'.2
      tq₃₂ := ht₂₁ }
  exact ⟨_, Bootstrap.fuzzyFrameOn_of_axisTriangle hT C.hK h₁.1 h₂'.1 hzn₁ hzn₂' hn₁n₂' hind⟩

end Frame

end Cover

end CFSG.ClassicalInvolution.NDB
