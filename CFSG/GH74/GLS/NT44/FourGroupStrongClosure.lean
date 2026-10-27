module

public import CFSG.GroupTheory.ABGLocalTools.Basic

import CFSG.GH74.GLS.NT44.ConjugateFusion

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

theorem conjugate_closure_isConj_and_stronglyClosed_of_card_four
    {G : Type} [Group G] [Finite G]
    {T : Subgroup G} {x : G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hx2 : orderOf x = 2)
    (hxT : x ∈ T)
    (hxcent : ∀ t ∈ T, t * x = x * t)
    (h4 : Nat.card ↥(Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}) = 4) :
    (∀ z ∈ Subgroup.closure {a : G | a ∈ T ∧ IsConj x a},
      z ≠ 1 → IsConj x z) ∧
    (∀ z ∈ Subgroup.closure {a : G | a ∈ T ∧ IsConj x a},
      ∀ g : G, g⁻¹ * z * g ∈ T →
        g⁻¹ * z * g ∈ Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Set G := {a : G | a ∈ T ∧ IsConj x a} with hU
  set Z : Subgroup G := Subgroup.closure U with hZ
  set N : Subgroup G := Subgroup.normalizer (Z : Set G) with hN
  have h4Z : Nat.card ↥Z = 4 := by
    simpa [hZ, hU] using h4
  have hxU : x ∈ U := by
    rw [hU]
    exact ⟨hxT, IsConj.refl x⟩
  have hZT : Z ≤ T := by
    rw [hZ, Subgroup.closure_le]
    intro a ha
    rw [hU] at ha
    exact ha.1
  have hxZ : x ∈ Z := by
    rw [hZ]
    exact Subgroup.subset_closure hxU
  have hZcomm : IsMulCommutative Z := by
    refine IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := ↥Z) ?_
    rw [h4Z]
    norm_num
  have hZC : Z ≤ Subgroup.centralizer (Z : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    simpa using congrArg Subtype.val
      ((isMulCommutative_iff.mp hZcomm) (⟨w, hw⟩ : Z) (⟨z, hz⟩ : Z))
  have hTN : T ≤ N := by
    rw [hN, hZ, Subgroup.le_normalizer_closure_iff]
    intro t ht a ha
    rw [hU] at ha
    exact Subgroup.subset_closure (by
      rw [hU]
      exact ⟨T.mul_mem (T.mul_mem ht ha.1) (T.inv_mem ht),
        ha.2.trans (isConj_iff.mpr ⟨t, rfl⟩)⟩)
  have hxN : x ∈ N := hTN hxT
  let xN : N := ⟨x, hxN⟩
  have hTSN : CFSG.ABGLocalTools.IsSylowOf 2 T N :=
    hT.of_le hTN le_top
  obtain ⟨S, hS⟩ := hTSN.exists_sylow_eq_subgroupOf
  have hSC : (S : Subgroup N) ≤ Subgroup.centralizer ({xN} : Set N) := by
    rw [hS]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    apply Subtype.ext
    change x * (s : G) = (s : G) * x
    exact (hxcent (s : G) (Subgroup.mem_subgroupOf.mp hs)).symm
  have hImgSubU : N.subtype '' conjugatesOf xN ⊆ U := by
    rintro a ⟨b, hb, rfl⟩
    have hb' : IsConj xN b := hb
    obtain ⟨c, hc⟩ := isConj_iff.mp hb'
    have hcG : (c : G) * x * (c : G)⁻¹ = (b : G) := by
      have h := congrArg (fun z : N => (z : G)) hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      change (c : G) * x * (c : G)⁻¹ = (b : G) at h
      exact h
    have hcN : (c : G) ∈ Subgroup.normalizer (Z : Set G) := by
      exact c.2
    have hbT : (b : G) ∈ T := by
      rw [← hcG]
      exact hZT ((Subgroup.mem_normalizer_iff.mp hcN x).mp hxZ)
    have hbConj : IsConj x (b : G) :=
      isConj_iff.mpr ⟨(c : G), hcG⟩
    rw [hU]
    exact ⟨hbT, hbConj⟩
  have hUsubImg : U ⊆ N.subtype '' conjugatesOf xN := by
    intro a haU
    have haU' : a ∈ U := haU
    rw [hU] at haU
    obtain ⟨haT, haConj⟩ := haU
    obtain ⟨g, hg⟩ := isConj_iff.mp haConj
    have haZ : a ∈ Z := by
      rw [hZ]
      exact Subgroup.subset_closure haU'
    have hxD : ({x} : Set G) ⊆ (Subgroup.centralizer (Z : Set G) : Set G) := by
      intro d hd
      rw [Set.mem_singleton_iff] at hd
      rw [hd]
      exact hZC hxZ
    have hxDg : (fun d : G => g * d * g⁻¹) '' ({x} : Set G) ⊆
        (Subgroup.centralizer (Z : Set G) : Set G) := by
      rintro _ ⟨d, hd, rfl⟩
      rw [Set.mem_singleton_iff] at hd
      rw [hd]
      change g * x * g⁻¹ ∈ (Subgroup.centralizer (Z : Set G) : Set G)
      rw [hg]
      exact hZC haZ
    have hxD' : ({x} : Set G) ⊆
        (Subgroup.centralizer
          (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} : Set G) : Set G) := by
      simpa [hZ, hU] using hxD
    have hxDg' : (fun d : G => g * d * g⁻¹) '' ({x} : Set G) ⊆
        (Subgroup.centralizer
          (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} : Set G) : Set G) := by
      simpa [hZ, hU] using hxDg
    obtain ⟨n, hnN, hnd⟩ :=
      exists_normalizer_conj_eq_on_of_conjugate_closure (T := T) (x := x) hT
        (D := ({x} : Set G)) (g := g) hxD' hxDg'
    have hnx : n * x * n⁻¹ = a := (hnd x (by simp)).trans hg
    have hnN' : n ∈ N := by
      simpa [hN, hZ, hU] using hnN
    let nN : N := ⟨n, hnN'⟩
    refine ⟨nN * xN * nN⁻¹, ?_, ?_⟩
    · exact isConj_iff.mpr ⟨nN, rfl⟩
    · change ((nN * xN * nN⁻¹ : N) : G) = a
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      change n * x * n⁻¹ = a
      exact hnx
  have hImgEq : N.subtype '' conjugatesOf xN = U :=
    Set.Subset.antisymm hImgSubU hUsubImg
  have hUncard_eq : U.ncard = (conjugatesOf xN).ncard := by
    rw [← hImgEq]
    exact Set.ncard_image_of_injective (conjugatesOf xN)
      (Subgroup.subtype_injective N)
  have hUncard_index : U.ncard = (Subgroup.centralizer ({xN} : Set N)).index := by
    rw [hUncard_eq, ← Subgroup.index_centralizer_eq_ncard xN]
  have hdvd : (Subgroup.centralizer ({xN} : Set N)).index ∣
      (S : Subgroup N).index :=
    Subgroup.index_dvd_of_le hSC
  have hSnot : ¬ 2 ∣ (S : Subgroup N).index := Sylow.not_dvd_index S
  have hUnot : ¬ 2 ∣ U.ncard := by
    rw [hUncard_index]
    intro h2
    exact hSnot (h2.trans hdvd)
  have hUsub : U ⊆ (Z : Set G) \ ({1} : Set G) := by
    intro a ha
    have haU : a ∈ U := ha
    rw [hU] at ha
    refine ⟨?_, ?_⟩
    · exact Subgroup.subset_closure haU
    · intro ha1
      rw [Set.mem_singleton_iff] at ha1
      rw [ha1] at ha
      have hx1 : x = 1 := isConj_one_left.mp ha.2
      have h1 : orderOf x = 1 := by rw [hx1, orderOf_one]
      omega
  have hZcard : (Z : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq (Z : Set G)]
    simpa using h4Z
  have hZdiff : ((Z : Set G) \ ({1} : Set G)).ncard = 3 := by
    rw [Set.ncard_sdiff (s := ({1} : Set G)) (t := (Z : Set G)) (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Z.one_mem)]
    rw [hZcard, Set.ncard_singleton]
  have hUcardle : U.ncard ≤ 3 := by
    calc U.ncard ≤ ((Z : Set G) \ ({1} : Set G)).ncard :=
          Set.ncard_le_ncard hUsub
      _ = 3 := hZdiff
  have hU1 : U.ncard ≠ 1 := by
    intro hUcard1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hUcard1
    have hxEqA : x = a := by
      have hxmem : x ∈ ({a} : Set G) := by
        rw [ha] at hxU
        exact hxU
      exact Set.mem_singleton_iff.mp hxmem
    have hUx : U = ({x} : Set G) := by
      rw [ha]
      have : a = x := hxEqA.symm
      rw [this]
    have h4U : Nat.card ↥(Subgroup.closure U) = 4 := by
      simpa [hZ] using h4Z
    have hcard2 : Nat.card ↥(Subgroup.closure U) = 2 := by
      rw [hUx, ← Subgroup.zpowers_eq_closure x, Nat.card_zpowers, hx2]
    omega
  have hUcard3 : U.ncard = 3 := by
    have hne0 : U.ncard ≠ 0 := by
      intro h0
      exact hUnot (by rw [h0]; exact dvd_zero 2)
    have hne2 : U.ncard ≠ 2 := by
      intro h2
      exact hUnot (by rw [h2])
    omega
  have hUeq : U = (Z : Set G) \ ({1} : Set G) :=
    Set.eq_of_subset_of_ncard_le hUsub (by rw [hZdiff, hUcard3])
  have hconjAll : ∀ z ∈ Z, z ≠ 1 → IsConj x z := by
    intro z hzZ hz1
    have hzU : z ∈ U := by
      rw [hUeq]
      exact ⟨hzZ, by simpa [Set.mem_singleton_iff] using hz1⟩
    rw [hU] at hzU
    exact hzU.2
  constructor
  · exact hconjAll
  · intro z hzZ g hgT
    by_cases hz1 : z = 1
    · rw [hz1]
      simp
    · have hzConj : IsConj z (g⁻¹ * z * g) := by
        refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
        simp
      have hxConj : IsConj x (g⁻¹ * z * g) :=
        (hconjAll z hzZ hz1).trans hzConj
      rw [hZ]
      exact Subgroup.subset_closure (by
        rw [hU]
        exact ⟨hgT, hxConj⟩)

end CFSG.GH74.GLS.NT44

end
