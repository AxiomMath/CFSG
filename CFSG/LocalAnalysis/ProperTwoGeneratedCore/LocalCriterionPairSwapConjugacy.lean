module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {K : Type u} [Group K]

theorem conjugacyWithin_top_eq_of_index_two
    (D : Subgroup K) (hDindex : D.index = 2)
    (t z : K) (htD : t ∉ D) (hzt : Commute z t) :
    conjugacyWithin (⊤ : Subgroup K) z = conjugacyWithin D z := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    by_cases hgD : (g : K) ∈ D
    · exact ⟨⟨g, hgD⟩, hg⟩
    · have htgd : t * (g : K) ∈ D :=
        (Subgroup.mul_mem_iff_of_index_two hDindex).mpr (iff_of_false htD hgD)
      refine ⟨⟨t * (g : K), htgd⟩, ?_⟩
      have hconj : t⁻¹ * z * t = z := by
        calc
          t⁻¹ * z * t = t⁻¹ * (z * t) := by group
          _ = t⁻¹ * (t * z) := by rw [hzt.eq]
          _ = z := by group
      calc
        (t * (g : K))⁻¹ * z * (t * (g : K)) =
            (g : K)⁻¹ * (t⁻¹ * z * t) * (g : K) := by group
        _ = (g : K)⁻¹ * z * (g : K) := by rw [hconj]
        _ = x := hg
  · rintro ⟨d, hd⟩
    exact ⟨⟨d, Subgroup.mem_top _⟩, hd⟩

theorem swap_conjugacyWithin_disjoint
    (D J : Subgroup K) [J.Normal] (hJodd : Odd (Nat.card J))
    (u t : K) (hu : IsInvolution u)
    (htcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    Disjoint (conjugacyWithin D t) (conjugacyWithin D (u * t)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨d, hd⟩ ⟨e, he⟩
  let q : K →* K ⧸ J := QuotientGroup.mk' J
  have hqconj : ∀ g : K, q (g⁻¹ * t * g) = q t := by
    intro g
    have hcomm : q g * q t = q t * q g :=
      Subgroup.mem_center_iff.mp htcentral (q g)
    calc
      q (g⁻¹ * t * g) = (q g)⁻¹ * q t * q g := by simp
      _ = (q g)⁻¹ * (q g * q t) := by rw [hcomm]; group
      _ = q t := by group
  have huquot : q u = 1 := by
    have heq : q t = (q (e : K))⁻¹ * q u * q t * q (e : K) := by
      calc
        q t = q ((d : K)⁻¹ * t * (d : K)) := (hqconj (d : K)).symm
        _ = q x := congrArg q hd
        _ = q ((e : K)⁻¹ * (u * t) * (e : K)) := congrArg q he.symm
        _ = (q (e : K))⁻¹ * q u * q t * q (e : K) := by simp [mul_assoc]
    have hcomm : q t * q (e : K) = q (e : K) * q t :=
      (Subgroup.mem_center_iff.mp htcentral (q (e : K))).symm
    have hcancel : q t = ((q (e : K))⁻¹ * q u * q (e : K)) * q t := by
      calc
        q t = (q (e : K))⁻¹ * q u * q t * q (e : K) := heq
        _ = (q (e : K))⁻¹ * q u * (q t * q (e : K)) := by group
        _ = (q (e : K))⁻¹ * q u * (q (e : K) * q t) := by rw [hcomm]
        _ = ((q (e : K))⁻¹ * q u * q (e : K)) * q t := by group
    have hconjone : (q (e : K))⁻¹ * q u * q (e : K) = 1 := by
      apply mul_right_cancel (b := q t)
      simpa using hcancel.symm
    calc
      q u = q (e : K) * ((q (e : K))⁻¹ * q u * q (e : K)) * (q (e : K))⁻¹ := by group
      _ = 1 := by rw [hconjone]; group
  have huJ : u ∈ J := (QuotientGroup.eq_one_iff u).mp huquot
  have huorder : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  have htwo : 2 ∣ Nat.card J := huorder ▸ J.orderOf_dvd_natCard huJ
  have hbad : Odd 2 := hJodd.of_dvd_nat htwo
  norm_num at hbad

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap
