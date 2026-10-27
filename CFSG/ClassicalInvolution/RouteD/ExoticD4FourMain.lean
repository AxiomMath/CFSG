module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourCaseI
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourTwins
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourPair
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourNodes
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

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Balance

section Aux

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_oddCoreIn_of_pow_four {X : Subgroup G} {t : G}
    (ht : t ∈ oddCoreIn X) (h4 : t ^ 4 = 1) : t = 1 := by
  have hd : orderOf t ∣ Nat.card (oddCoreIn X) := Subgroup.orderOf_dvd_natCard _ ht
  have hodd : Odd (orderOf t) := (odd_card_oddCoreIn X).of_dvd_nat hd
  have h2 : orderOf t ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hle : orderOf t ≤ 4 := Nat.le_of_dvd (by norm_num) h2
  obtain ⟨m, hm⟩ := hodd
  have hm1 : m ≤ 1 := by omega
  interval_cases m
  · exact orderOf_eq_one_iff.mp (by omega)
  · exfalso
    rw [show orderOf t = 3 by omega] at h2
    omega

omit [Finite G] in
theorem isPGroup_closure_of_commuting_involutions {ι : Type} (z : ι → G)
    (hsq : ∀ k, z k * z k = 1) (hcomm : ∀ j k, z j * z k = z k * z j) :
    IsPGroup 2 (Subgroup.closure (Set.range z)) := by
  have hS : ∀ a ∈ Set.range z, ∀ b ∈ Set.range z, a * b = b * a := by
    rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩
    exact hcomm j k
  have h1 : ∀ s ∈ Set.range z, Subgroup.closure (Set.range z) ≤
      Subgroup.centralizer ({s} : Set G) := fun s hs =>
    (Subgroup.closure_le _).mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hS t ht s hs)
  have h2 : ∀ g ∈ Subgroup.closure (Set.range z), ∀ h ∈ Subgroup.closure (Set.range z),
      g * h = h * g := by
    intro g hg h hh
    have hgc : Subgroup.closure (Set.range z) ≤ Subgroup.centralizer ({g} : Set G) :=
      (Subgroup.closure_le _).mpr fun s hs =>
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
          (h1 s hs hg)).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hgc hh)).symm
  have h3 : ∀ g ∈ Subgroup.closure (Set.range z), g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hsq k
    | one => simp
    | mul a b ha hb iha ihb =>
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [h2 b hb a ha]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, mul_one]
    | inv a ha iha =>
      rw [inv_eq_of_mul_eq_one_right iha, iha]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_two] using h3 g.1 g.2

omit [Finite G] in
theorem commModOdd_le_conjSub {u : G} {X : Subgroup G}
    (hXC : X ≤ Subgroup.centralizer ({u} : Set G))
    {n : G} (hn : n ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G))) :
    commModOdd u X ≤ commModOdd u (conjSub n X) := by
  rintro g ⟨hg, h⟩
  refine ⟨hg, fun y hy => ?_⟩
  obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ ∈ X, y = n * y₀ * n⁻¹ :=
    ⟨n⁻¹ * y * n, mem_conjSub_iff.mp hy, by group⟩
  have hm : g * n * g⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G)) :=
    conj_mem_oddCoreIn hg hn
  have hc := h y₀ hy₀
  have hconj : y₀ * ((g * n * g⁻¹)⁻¹ * n) * y₀⁻¹ ∈
      oddCoreIn (Subgroup.centralizer ({u} : Set G)) :=
    conj_mem_oddCoreIn (hXC hy₀) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hn)
  have e : g * (n * y₀ * n⁻¹) * g⁻¹ * (n * y₀ * n⁻¹)⁻¹ = (g * n * g⁻¹) *
      (g * y₀ * g⁻¹ * y₀⁻¹) * (y₀ * ((g * n * g⁻¹)⁻¹ * n) * y₀⁻¹) * n⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hc) hconj)
    (Subgroup.inv_mem _ hn)

end Aux

end CFSG.ClassicalInvolution.RouteD.Exotic
