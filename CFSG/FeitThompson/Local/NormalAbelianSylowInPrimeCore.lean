module

public import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup
import CFSG.FeitThompson.Local.AbelianGeneratedPrimeCoreConstraint
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
public import Mathlib.GroupTheory.Solvable

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem map_mk'_pComplCore_le_pCore_quotient_of_normal_abelian_sylow [Finite G]
    [Group.IsSolvable G] (hp : p.Prime) (hGodd : Odd (Nat.card G)) (S : Sylow p G)
    {A : Subgroup G} (hAS : A ≤ (S : Subgroup G))
    (hAnormal : (A.subgroupOf (S : Subgroup G)).Normal) (hAcomm : IsMulCommutative A) :
    A.map (QuotientGroup.mk' (pComplCore p G)) ≤ pCore p (G ⧸ pComplCore p G) := by
  have := Fact.mk hp
  have hDnormal : (pComplCore p G).Normal := pComplCore_normal p G
  set f := QuotientGroup.mk' (pComplCore p G) with hf
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hA'p : IsPGroup p (A.map f) := (S.isPGroup'.to_le hAS).map f
  have hA'comm : IsMulCommutative (A.map f) := Subgroup.map_isMulCommutative A f
  have hQnormal : (pCore p (G ⧸ pComplCore p G)).Normal := pCore_normal p _
  have hQp : IsPGroup p (pCore p (G ⧸ pComplCore p G)) := isPGroup_pCore hp _
  have hQS : pCore p (G ⧸ pComplCore p G) ≤ (S : Subgroup G).map f := by
    have := hQp.le_sylow_of_normal (S.mapSurjective hfsurj)
    rwa [S.coe_mapSurjective hfsurj] at this
  have hnorm : pCore p (G ⧸ pComplCore p G) ≤ normalizer ((A.map f : Subgroup (G ⧸ _)) : Set _) :=
    hQS.trans ((Subgroup.map_mono
      (Subgroup.le_normalizer_of_normal_subgroupOf (hK := hAnormal) hAS)).trans
        (Subgroup.le_normalizer_map f))
  exact le_pCore_of_le_sSup_of_inf_pCore_le hp (odd_natCard_quotient _ hGodd)
    (pComplCore_quotient_pComplCore p G) hQp inf_le_left (𝒜 := {A.map f})
    (fun B hB => hB ▸ hA'comm) (fun B hB => hB ▸ hA'p) (fun B hB => hB ▸ hnorm)
    (le_of_eq sSup_singleton.symm)

theorem le_tCore_of_normal_abelian_sylow [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (S : Sylow p G) {A : Subgroup G} (hAS : A ≤ (S : Subgroup G))
    (hAnormal : (A.subgroupOf (S : Subgroup G)).Normal) (hAcomm : IsMulCommutative A) :
    A ≤ tCore p G :=
  le_tCore_iff.2 (map_mk'_pComplCore_le_pCore_quotient_of_normal_abelian_sylow hp hGodd S hAS
    hAnormal hAcomm)

theorem le_tCore_of_normal_abelian_of_natCard_eq [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) {S : Subgroup G}
    (hS : Nat.card S = p ^ (Nat.card G).factorization p) {A : Subgroup G} (hAS : A ≤ S)
    (hAnormal : (A.subgroupOf S).Normal) (hAcomm : IsMulCommutative A) :
    A ≤ tCore p G := by
  have := Fact.mk hp
  have hSyl : ((Sylow.ofCard S hS : Sylow p G) : Subgroup G) = S := Sylow.coe_ofCard S hS
  exact le_tCore_of_normal_abelian_sylow hp hGodd (Sylow.ofCard S hS)
    (by rw [hSyl]; exact hAS) (by rw [hSyl]; exact hAnormal) hAcomm

theorem le_of_normal_abelian_sylow_of_eq_comap [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) {S : Subgroup G}
    (hS : Nat.card S = p ^ (Nat.card G).factorization p) {A : Subgroup G} (hAS : A ≤ S)
    (hAnormal : (A.subgroupOf S).Normal) (hAcomm : IsMulCommutative A)
    {D : Subgroup G} [D.Normal] (hD : D = pComplCore p G)
    {T : Subgroup G} (hT : T = (pCore p (G ⧸ D)).comap (QuotientGroup.mk' D)) :
    A ≤ T := by
  subst hD
  rw [hT, ← tCore_eq_comap]
  exact le_tCore_of_normal_abelian_of_natCard_eq hp hGodd hS hAS hAnormal hAcomm

theorem map_subtype_le_tCore_of_normal_abelian_sylow [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (S : Sylow p G) (A : Subgroup (S : Subgroup G)) [A.Normal]
    [IsMulCommutative A] :
    A.map (S : Subgroup G).subtype ≤ tCore p G := by
  refine le_tCore_of_normal_abelian_sylow hp hGodd S (Subgroup.map_subtype_le A) ?_
    (Subgroup.map_isMulCommutative A _)
  change (Subgroup.comap (S : Subgroup G).subtype (A.map (S : Subgroup G).subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective]
  infer_instance

theorem sylow_le_tCore_of_isMulCommutative [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (S : Sylow p G) (hS : IsMulCommutative (S : Subgroup G)) :
    (S : Subgroup G) ≤ tCore p G :=
  le_tCore_of_normal_abelian_sylow hp hGodd S le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) hS

end

end CFSG.FeitThompson
