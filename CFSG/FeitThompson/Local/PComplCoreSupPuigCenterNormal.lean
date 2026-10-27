module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration
import CFSG.FeitThompson.Local.PuigCenterNormalTrivialPComplCore
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.PuigSeriesIsomorphismInvariance
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.LowRankSmallestPrimeHallReduction
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup Pointwise

variable {G : Type*} [Group G] {p : ℕ}

private theorem map_puigCenter_subtype_of_equiv {X Y : Type*} [Group X] [Group Y] {A : Subgroup X}
    {B : Subgroup Y} (f : X →* Y) (e : A ≃* B) (he : ∀ a : A, ((e a : Y)) = f (a : X)) :
    (puigCenter B).map B.subtype = ((puigCenter A).map A.subtype).map f := by
  rw [← puigCenter_map e, Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun a => he a

theorem map_puigCenter_sylow_mk'_pComplCore [Finite G] (hp : p.Prime) (S : Sylow p G) :
    (puigCenter ↥(((S : Subgroup G) ⊔ pComplCore p G).map (mk' (pComplCore p G)))).map
        (((S : Subgroup G) ⊔ pComplCore p G).map (mk' (pComplCore p G))).subtype
      = ((puigCenter ↥(S : Subgroup G)).map (S : Subgroup G).subtype).map
          (mk' (pComplCore p G)) := by
  have := Fact.mk hp
  have hcop : p.Coprime (Nat.card (pComplCore p G)) :=
    hp.coprime_iff_not_dvd.2 (not_dvd_natCard_pComplCore hp G)
  exact map_puigCenter_subtype_of_equiv (mk' (pComplCore p G))
    (equivMapSup hp hcop S.card_eq_multiplicity) fun a =>
      coe_equivMapSup_apply hp hcop S.card_eq_multiplicity a

theorem normal_pComplCore_sup_map_puigCenter_sylow [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (S : Sylow p G) :
    (pComplCore p G ⊔ (puigCenter ↥(S : Subgroup G)).map (S : Subgroup G).subtype).Normal := by
  have := Fact.mk hp
  set D : Subgroup G := pComplCore p G with hD
  set K : Subgroup G := (puigCenter ↥(S : Subgroup G)).map (S : Subgroup G).subtype
  by_cases hdvd : p ∣ Nat.card G
  ·
    have hpodd : Odd p := Odd.of_dvd_nat hGodd hdvd
    have hcop : p.Coprime (Nat.card D) :=
      hp.coprime_iff_not_dvd.2 (not_dvd_natCard_pComplCore hp G)
    set Sbar : Sylow p (G ⧸ D) :=
      Sylow.ofCard (((S : Subgroup G) ⊔ D).map (mk' D))
        (natCard_map_sup_mk'_eq_pow_factorization hp hcop S.card_eq_multiplicity) with hSbar
    have hSbarcoe : (Sbar : Subgroup (G ⧸ D)) = ((S : Subgroup G) ⊔ D).map (mk' D) :=
      Sylow.coe_ofCard _ _
    have hQodd : Odd (Nat.card (G ⧸ D)) := Odd.of_dvd_nat hGodd (card_quotient_dvd_card D)
    have hQ' : pComplCore p (G ⧸ D) = ⊥ := pComplCore_quotient_pComplCore p G
    have hnorm : ((puigCenter ↥(Sbar : Subgroup (G ⧸ D))).map
        (Sbar : Subgroup (G ⧸ D)).subtype).Normal :=
      normal_map_puigCenter_sylow hp hpodd hQodd hQ' Sbar
    rw [hSbarcoe, map_puigCenter_sylow_mk'_pComplCore hp S] at hnorm
    have hcomap := hnorm.comap (mk' D)
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hcomap
    rw [sup_comm]
    exact hcomap
  ·
    rw [hD, pComplCore_eq_top_of_not_dvd hdvd, top_sup_eq]
    infer_instance

theorem coe_pComplCore_sup_map_puigCenter_sylow [Finite G] (S : Sylow p G) :
    ((pComplCore p G ⊔ (puigCenter ↥(S : Subgroup G)).map (S : Subgroup G).subtype :
        Subgroup G) : Set G)
      = (pComplCore p G : Set G) * ((puigCenter ↥(S : Subgroup G)).map (S : Subgroup G).subtype :
        Set G) :=
  Subgroup.normal_mul _ _

theorem conj_mem_pComplCore_sup_map_puigCenter_sylow [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    (hGodd : Odd (Nat.card G)) (S : Sylow p G) {x : G}
    (hx : x ∈ pComplCore p G ⊔ (puigCenter ↥(S : Subgroup G)).map (S : Subgroup G).subtype)
    (g : G) :
    g * x * g⁻¹ ∈ pComplCore p G ⊔ (puigCenter ↥(S : Subgroup G)).map (S : Subgroup G).subtype :=
  (normal_pComplCore_sup_map_puigCenter_sylow hp hGodd S).conj_mem x hx g

end CFSG.FeitThompson

end
