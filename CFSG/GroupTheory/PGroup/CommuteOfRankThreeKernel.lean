module

import CFSG.Quasithin.Background.A1cRank
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPCover
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open

theorem commute_of_pow_three_of_commutator_mem_ker {G : Type*} [Group G] [Finite G]
    {P J K E : Subgroup G} (hP : IsPGroup 3 P) (hJP : J ≤ P) (hKP : K ≤ P)
    (hJn : P ≤ normalizer (J : Set G)) (hKn : P ≤ normalizer (K : Set G))
    (hJK : J ⊓ K = ⊥) (hEJ : E ≤ J) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 9)
    (hrank : CFSG.Open.pRank 3 P ≤ 3)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x ^ 3 = 1 → y ^ 3 = 1 → x * y * x⁻¹ * y⁻¹ ∈ K)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) :
    x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm_of : ∀ {a b : G}, a * b * a⁻¹ * b⁻¹ = 1 → a * b = b * a := fun {a b} h => by
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  have hJKc : ∀ w ∈ P, ∀ e ∈ J, w * e * w⁻¹ * e⁻¹ ∈ K → e * w = w * e := by
    intro w hw e he hK'
    have hJ' : w * e * w⁻¹ * e⁻¹ ∈ J :=
      J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hJn hw) e).mp he) (J.inv_mem he)
    have h1 : w * e * w⁻¹ * e⁻¹ ∈ J ⊓ K := ⟨hJ', hK'⟩
    rw [hJK, Subgroup.mem_bot] at h1
    exact (hcomm_of h1).symm
  have hwE : ∀ w ∈ P, w ^ 3 = 1 → ∀ e ∈ E, e * w = w * e := fun w hw hw3 e he =>
    hJKc w hw e (hEJ he) (hcomm w hw e (hJP (hEJ he)) hw3 (hE.2 e he))
  by_contra hxy
  have hc : x * y * x⁻¹ * y⁻¹ ∈ K := hcomm x hx y hy hx3 hy3
  have hc1 : x * y * x⁻¹ * y⁻¹ ≠ 1 := fun h => hxy (hcomm_of h)
  have : (K.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).2 hKn
  have hK' : K.subgroupOf P ≠ ⊥ := by
    intro h0
    have hmem : (⟨_, hKP hc⟩ : ↥P) ∈ K.subgroupOf P := Subgroup.mem_subgroupOf.mpr hc
    rw [h0, Subgroup.mem_bot] at hmem
    exact hc1 (congrArg Subtype.val hmem)
  obtain ⟨w₀, hw₀K, hw₀Z, hw₀3, hw₀1⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.exists_ne_one_mem_inf_center hP
      (K.subgroupOf P) hK'
  set z : G := (w₀ : G)
  have hzP : z ∈ P := w₀.2
  have hzK : z ∈ K := Subgroup.mem_subgroupOf.mp hw₀K
  have hzo : orderOf z = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · have := congrArg Subtype.val hw₀3
      simpa using this
    · intro h
      exact hw₀1 (Subtype.ext h)
  have hzc : ∀ g ∈ P, g * z = z * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hw₀Z ⟨g, hg⟩)
  have hzE : z ∉ E := by
    intro hzE
    have h1 : z ∈ J ⊓ K := ⟨hEJ hzE, hzK⟩
    rw [hJK, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  obtain ⟨hFel, hFcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE hzo
    (fun e he => hzc e (hJP (hEJ he))) hzE
  have hFw : ∀ w ∈ P, w ^ 3 = 1 → ∀ f ∈ E ⊔ Subgroup.zpowers z, Commute f w := by
    intro w hw hw3 f hf
    have hle : E ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer {w} := by
      refine sup_le (fun e he => ?_) ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro u hu
        rw [Set.mem_singleton_iff.mp hu]
        exact (hwE w hw hw3 e he).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro u hu
        rw [Set.mem_singleton_iff.mp hu]
        exact hzc w hw
    exact (Subgroup.mem_centralizer_iff.mp (hle hf) w rfl).symm
  have hxF : x ∈ E ⊔ Subgroup.zpowers z := by
    by_contra hxF
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hxy (by rw [one_mul, mul_one])
    obtain ⟨hF'el, hF'card⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hFel
      (orderOf_eq_prime hx3 hx1) (hFw x hx hx3) hxF
    have hle : E ⊔ Subgroup.zpowers z ⊔ Subgroup.zpowers x ≤ P :=
      sup_le (sup_le (hEJ.trans hJP) (Subgroup.zpowers_le.mpr hzP)) (Subgroup.zpowers_le.mpr hx)
    have h4 := CFSG.SectionRank.le_pRank (k := 4) (by norm_num) hle hF'el
      (by rw [hF'card, hFcard, hEcard] <;> norm_num)
    omega
  exact hxy (hFw y hy hy3 x hxF).eq

end CFSG.GroupTheory
