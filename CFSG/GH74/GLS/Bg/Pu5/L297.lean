module

public import CFSG.GH74.GLS.Bg.Pu5.L294
public import CFSG.GH74.GLS.Bg.Iii2.Statements
public import CFSG.GH74.E2.TermLeaves

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

variable {G : Type} [Group G] [Finite G]

theorem central_involution_eq (hquat : II4_4_quat) (h44 : II4_44) (h43d : II4_43d) (h296 : L296)
    {z t : G} {S : Subgroup G} (hC : Cfg G z t S) {g : G} (_hgS : g ∈ S)
    (hgc : ∀ s ∈ S, s * g = g * s) (hg2 : g * g = 1) : g = 1 ∨ g = z := by
  obtain ⟨K₀, hK₀⟩ := rigid_nonempty hC.hz hC.hzK
  have hrank := (h296 G z t S hC).2 K₀ hK₀
  have hgz : g ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hgc z hC.z_mem_S).symm
  have hP : IsSylowOf 2 (S ⊓ K₀) K₀ := rr_sylow hK₀ hC.sylow
  have hnorm : g ∈ normalizer (K₀ : Set G) := by
    by_contra hn
    have hK' : IsRigidRankOneComp z (cmap g K₀) := isRigidRankOneComp_cmap hK₀ hgz
    have hne : K₀ ≠ cmap g K₀ := fun h => hn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
    obtain ⟨n, hn3, hqd⟩ := hquat G hC.simple z hC.hz S K₀ hC.sylow (rr_pcomp hK₀) hK₀.2
    obtain ⟨z₀, ψ, -, -, -, -, -, -, -, -, hnc⟩ := quat_data ⟨n, hn3, hqd⟩
    apply hnc
    intro x hx y hy
    have hyK' : y ∈ S ⊓ cmap g K₀ := by
      refine ⟨hy.1, ?_⟩
      have := conj_mem_cmap' hy.2 g
      have hyg : g * y * g⁻¹ = y := by
        rw [← hgc y hy.1]
        group
      rwa [hyg] at this
    exact rr_sylow_comm hK₀ hK' hne hC.sylow x hx y hyK'
  have hgK : g ∈ cSec K₀ :=
    h43d G hC.simple z hC.hz K₀ hK₀ g hg2 hgz hnorm (S ⊓ K₀) hP fun p hp => (hgc p hp.1).symm
  by_contra hne
  push Not at hne
  have hg2' : orderOf g = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hg2) hne.1
  have hgD : g ∈ centralizer ({z, t} : Set G) ⊓ cSec K₀ := by
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, hgK⟩
    rintro h (rfl | rfl)
    · exact hgc _ hC.z_mem_S
    · exact hgc _ hC.tS
  have hzK : z ∈ cSec K₀ :=
    mem_cSec_of_mem_zStar h44 hquat hC.simple hC.gen4 hC.z_mem_zStar
      (exists_two_pow_eq_one_of_orderOf hC.hz) hK₀
  have hzD : z ∈ centralizer ({z, t} : Set G) ⊓ cSec K₀ := by
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, hzK⟩
    rintro h (rfl | rfl)
    · rfl
    · exact Subgroup.mem_centralizer_singleton_iff.1 hC.tC
  have h2 := CFSG.GH74.E2.two_le_pRank_of_commuting_involutions
    (a := (⟨g, hgD⟩ : ↥(centralizer ({z, t} : Set G) ⊓ cSec K₀))) (b := ⟨z, hzD⟩)
    (by rw [← Subgroup.orderOf_coe]; exact hg2') (by rw [← Subgroup.orderOf_coe]; exact hC.hz)
    (fun h => hne.2 (congrArg Subtype.val h)) (Subtype.ext (hgc z hC.z_mem_S).symm)
  omega

theorem l297_of (hquat : II4_4_quat) (h44 : II4_44) (h43d : II4_43d) (h296 : L296) : L297 := by
  intro G _ _ z t S hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ₁ : ∀ g ∈ S, (∀ s ∈ S, s * g = g * s) → g * g = 1 → g = 1 ∨ g = z :=
    fun g hgS hgc hg2 => central_involution_eq hquat h44 h43d h296 hC hgS hgc hg2
  have hzc : ∀ s ∈ S, s * z = z * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (hC.sylow.le hs)
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hC.hz, sq] at this
  have hz1 : z ≠ 1 := fun h => by
    have := hC.hz
    rw [h, orderOf_one] at this
    omega
  obtain ⟨P, hP, hSP⟩ := exists_isSylowOf_ge' (K := (⊤ : Subgroup G)) (le_top : S ≤ ⊤)
    hC.sylow.isPGroup
  have hPp : IsPGroup 2 ↥P := hP.isPGroup
  have hPS : P = S := by
    have hntP : Nontrivial ↥P := ⟨⟨1, ⟨z, hSP hC.z_mem_S⟩, fun h => hz1 (congrArg Subtype.val h).symm⟩⟩
    have hZnt : Nontrivial ↥(Subgroup.center ↥P) := hPp.center_nontrivial
    have hZp : IsPGroup 2 ↥(Subgroup.center ↥P) := hPp.to_subgroup _
    have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥P) := by
      rcases hZp.card_eq_or_dvd with h | h
      · exact absurd (Nat.card_eq_one_iff_unique.1 h).1 (not_subsingleton _)
      · exact h
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥P)) 2 hdvd
    have hcP : ∀ g : ↥P, g * (c : ↥P) = (c : ↥P) * g := Subgroup.mem_center_iff.1 c.2
    set y : G := ((c : ↥P) : G) with hy
    have hyP : y ∈ P := (c : ↥P).2
    have hy2 : y * y = 1 := by
      have h1 : orderOf (c : ↥P) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
      have h2 : (c : ↥P) * (c : ↥P) = 1 := by
        have := pow_orderOf_eq_one (c : ↥P)
        rwa [h1, sq] at this
      exact congrArg Subtype.val h2
    have hy1 : y ≠ 1 := fun h => by
      have h1 : orderOf (c : ↥P) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
      have : (c : ↥P) = 1 := Subtype.ext h
      rw [this, orderOf_one] at h1
      omega
    have hyc : ∀ p ∈ P, p * y = y * p := fun p hp => congrArg Subtype.val (hcP ⟨p, hp⟩)
    have hyz : y ∈ centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hyc z (hSP hC.z_mem_S)).symm
    have hySle : S ⊔ zpowers y ≤ P := sup_le hSP (zpowers_le.2 hyP)
    have hysub : S ⊔ zpowers y ≤ centralizer ({z} : Set G) :=
      sup_le hC.sylow.le (zpowers_le.2 hyz)
    have hyS : y ∈ S := by
      have heq := hC.sylow.eq_of_le (le_sup_left : S ≤ S ⊔ zpowers y) hysub (hPp.to_le hySle)
      rw [← heq]
      exact Subgroup.mem_sup_right (mem_zpowers y)
    have hyz' : y = z := by
      rcases hZ₁ y hyS (fun s hs => hyc s (hSP hs)) hy2 with h | h
      · exact absurd h hy1
      · exact h
    have hPC : P ≤ centralizer ({z} : Set G) := fun p hp =>
      Subgroup.mem_centralizer_singleton_iff.2 (by rw [← hyz']; exact hyc p hp)
    exact hC.sylow.eq_of_le hSP hPC hPp
  rw [hPS] at hP
  have hcard : Nat.card S = 2 ^ (Nat.card G).factorization 2 := by
    have := hP.card_eq
    rwa [Subgroup.card_top] at this
  refine ⟨Sylow.ofCard S hcard, fun g => ?_⟩
  rw [Sylow.coe_ofCard]
  constructor
  · rintro ⟨hgS, hgc, hg2⟩
    have hg2' : g * g = 1 := by rwa [sq] at hg2
    rcases hZ₁ g hgS hgc hg2' with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨S.zpow_mem hC.z_mem_S k, fun s hs => ?_, ?_⟩
    · exact ((Commute.zpow_right (show Commute s z from hzc s hs) k).eq)
    · have hz2 : z ^ 2 = 1 := by rw [sq]; exact hzz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]

end CFSG.GH74.GLS.Bg.Pu5
