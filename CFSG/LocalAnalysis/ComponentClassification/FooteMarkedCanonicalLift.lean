module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
import CFSG.GH74.Generic.BProg.Helpers
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem canonicalPerfectLift_eq_ambientCanonicalLift {X : Subgroup G} [Finite X]
    {A : Subgroup (X ⧸ pPrimeCore 2 X)} (hA : IsComponent A) :
    canonicalPerfectLift X A = ambientCanonicalLift X A := by
  classical
  let V : Subgroup X := A.comap (QuotientGroup.mk' (pPrimeCore 2 X))
  let W : Subgroup V := CFSG.perfectResidual V
  have : Group.IsPerfect ↥W :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect (G := V)
  have hWtop : CFSG.GH74.GLS.oPrimeResidual 2 ↥W = ⊤ :=
    CFSG.GH74.Generic.BProg.oPrimeResidual_eq_top_of_isPerfect
  have hWmap : (⊤ : Subgroup ↥W).map W.subtype = W := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hWgen : W ≤ CFSG.GH74.GLS.oPrimeResidual 2 V := by
    have hmap : (CFSG.GH74.GLS.oPrimeResidual 2 ↥W).map W.subtype ≤
        CFSG.GH74.GLS.oPrimeResidual 2 V := by
      rw [CFSG.GH74.GLS.oPrimeResidual, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by simpa using congrArg (fun z : ↥W => (z : V)) hk⟩
    calc W = (⊤ : Subgroup ↥W).map W.subtype := hWmap.symm
      _ = (CFSG.GH74.GLS.oPrimeResidual 2 ↥W).map W.subtype := by rw [hWtop]
      _ ≤ CFSG.GH74.GLS.oPrimeResidual 2 V := hmap
  have hcanon : (CFSG.GH74.GLS.oPrimeResidual 2 V).map V.subtype =
      CatalogueBPrimeJoin.canonicalPrimeLift 2 A := by
    rw [CatalogueBPrimeJoin.canonicalPrimeLift, CFSG.GH74.GLS.oPrimeResidual,
      MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      have hdvd : orderOf (y : V) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨y.2, j, by
        change orderOf (y : X) = 2 ^ j
        rw [Subgroup.orderOf_coe, hj]⟩
    · rintro ⟨hxV, k, hk⟩
      refine ⟨⟨x, hxV⟩, ⟨k, ?_⟩, rfl⟩
      have hord : orderOf (⟨x, hxV⟩ : ↥V) = 2 ^ k := by
        rw [Subgroup.orderOf_mk, hk]
      rw [← hord, pow_orderOf_eq_one]
  have hforward : W.map V.subtype ≤ CatalogueBPrimeJoin.canonicalPrimeLift 2 A :=
    (Subgroup.map_mono hWgen).trans_eq hcanon
  have hreverse : CatalogueBPrimeJoin.canonicalPrimeLift 2 A ≤ W.map V.subtype := by
    change CatalogueBPrimeJoin.canonicalPrimeLift 2 A ≤
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf V
    apply CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
    · exact CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect
        (CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 A hA).1
    · rw [CatalogueBPrimeJoin.canonicalPrimeLift]
      exact (Subgroup.closure_le _).mpr (fun x hx => hx.1)
  have heq : W.map V.subtype = CatalogueBPrimeJoin.canonicalPrimeLift 2 A :=
    le_antisymm hforward hreverse
  rw [canonicalPerfectLift, ambientCanonicalLift, heq]

end CFSG.ComponentClassification.FooteMarked
