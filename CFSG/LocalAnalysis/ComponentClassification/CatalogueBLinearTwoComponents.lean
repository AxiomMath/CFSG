module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateQuotients
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoOdd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2PerfectSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwo

open CFSG.GorensteinWalter
open CatalogueSchreierLinearTwo

theorem perfect_le_normal_of_solvable_quotient {G : Type*} [Group G]
    (N L : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)] [Group.IsPerfect L] :
    L ≤ N := by
  have htrivial := SolvableKernelContainment.hom_eq_one
    ((QuotientGroup.mk' N).comp L.subtype)
  intro member hmember
  apply (QuotientGroup.eq_one_iff _).mp
  exact congrArg (fun homomorphism : L →* G ⧸ N =>
    homomorphism (⟨member, hmember⟩ : L)) htrivial

theorem perfect_subnormal_eq_simple_normal {G : Type*} [Group G]
    (N L : Subgroup G) [N.Normal] [IsSimpleGroup N]
    [Group.IsSolvable (G ⧸ N)] [Group.IsPerfect L] [Nontrivial L]
    (hsubnormal : L.IsSubnormal) : L = N := by
  have hle := perfect_le_normal_of_solvable_quotient N L
  have hrestricted := hsubnormal.subgroupOf (K := N)
  have htop : L.subgroupOf N = ⊤ :=
    (hrestricted.eq_bot_or_top_of_isSimpleGroup (inferInstance : IsSimpleGroup N)).resolve_left
      (by
        intro hbot
        have hmap := Subgroup.map_subgroupOf_eq_of_le hle
        rw [hbot, Subgroup.map_bot] at hmap
        exact L.nontrivial_iff_ne_bot.mp inferInstance hmap.symm)
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

theorem pComponent_eq_simple_normal {G : Type*} [Group G]
    (p : ℕ) (N L : Subgroup G) [N.Normal] [IsSimpleGroup N]
    [Group.IsSolvable (G ⧸ N)] (hL : CFSG.IsPComponent p L) : L = N := by
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  let : Nontrivial L := CatalogueBAlternating.pComponent_nontrivial hL
  exact perfect_subnormal_eq_simple_normal N L hL.choose_spec.2.1

theorem pglPSLRange_quasisimple (K : Type*) [Field K] [Finite K]
    (hcard : 3 < Nat.card K) :
    CFSG.IsQuasisimple (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range := by
  let : Group.IsPerfect (PSL2 K) := psl2_isPerfect_of_card_gt_three K hcard
  let : IsSimpleGroup (PSL2 K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hquasi : CFSG.Open.IsQuasisimple (PSL2 K) := Quasisimple.simple_of_perfect _
  let e : PSL2 K ≃* (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range :=
    MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv e.symm hquasi)

theorem pgl_pComponent_classification (K : Type*) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (PGL2 K)) (hL : CFSG.IsPComponent p L) :
    5 ≤ Nat.card K ∧
      L = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range ∧
      CFSG.IsQuasisimple L := by
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  let : Nontrivial L := CatalogueBAlternating.pComponent_nontrivial hL
  have hprimepower := oddPrimePower_of_odd_card K hodd
  obtain ⟨hcard, hequal⟩ := pgl2_perfect_subnormal_eq_commutator K hprimepower L
    (L.nontrivial_iff_ne_bot.mp inferInstance) inferInstance hL.choose_spec.2.1
  have hrange : L = (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range :=
    hequal.trans (pgl2_commutator_eq_psl2_range_of_card_gt_three K hprimepower hcard)
  have hbound : 5 ≤ Nat.card K := by obtain ⟨n, hn⟩ := hodd; omega
  refine ⟨hbound, hrange, ?_⟩
  rw [hrange]
  exact pglPSLRange_quasisimple K hcard

theorem pgl_three_no_pComponent (K : Type*) [Field K] [Finite K]
    (hcard : Nat.card K = 3) (p : ℕ) [Fact p.Prime] (L : Subgroup (PGL2 K)) :
    ¬ CFSG.IsPComponent p L := by
  intro hL
  have hodd : Odd (Nat.card K) := hcard ▸ (by decide : Odd 3)
  have hbound := (pgl_pComponent_classification K hodd p L hL).1
  omega

theorem coordinateD_perfect_subnormal_classification (K : Type*) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (L : Subgroup (coordinateD K))
    [Group.IsPerfect L] [Nontrivial L] (hsubnormal : L.IsSubnormal) :
    5 ≤ Nat.card K ∧ L = (coordinateG K).subgroupOf (coordinateD K) ∧
      CFSG.IsQuasisimple L := by
  let e := pglEquivCoordinateD K
  let J := L.map e.symm.toMonoidHom
  let restriction : L ≃* J := L.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  let : Nontrivial J := restriction.symm.toEquiv.nontrivial
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := restriction.toMonoidHom) restriction.surjective
  have hJsubnormal : J.IsSubnormal := hsubnormal.map e.symm.surjective
  have hprimepower := oddPrimePower_of_odd_card K hodd
  obtain ⟨hcard, hJ⟩ := pgl2_perfect_subnormal_eq_commutator K hprimepower J
    (J.nontrivial_iff_ne_bot.mp inferInstance) inferInstance hJsubnormal
  have hJrange : J = (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range :=
    hJ.trans (pgl2_commutator_eq_psl2_range_of_card_gt_three K hprimepower hcard)
  have hmap : J.map e.toMonoidHom = L := by
    change (L.map e.symm.toMonoidHom).map e.toMonoidHom = L
    rw [Subgroup.map_map]
    have hinverse : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id (coordinateD K) := by
      apply MonoidHom.ext
      intro member
      exact e.apply_symm_apply member
    rw [hinverse, Subgroup.map_id]
  have hequal : L = (coordinateG K).subgroupOf (coordinateD K) := by
    rw [← hmap, hJrange]
    exact pglPSLRange_map_coordinateD K
  have hquasiJ : CFSG.Open.IsQuasisimple J := by
    rw [hJrange]
    exact CatalogueBAlternating.quasisimple_iff_native.mp (pglPSLRange_quasisimple K hcard)
  have hquasiL := Components.quasisimple_of_equiv restriction hquasiJ
  have hbound : 5 ≤ Nat.card K := by obtain ⟨n, hn⟩ := hodd; omega
  exact ⟨hbound, hequal, CatalogueBAlternating.quasisimple_iff_native.mpr hquasiL⟩

theorem coordinateD_pComponent_classification (K : Type*) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (coordinateD K)) (hL : CFSG.IsPComponent p L) :
    5 ≤ Nat.card K ∧ L = (coordinateG K).subgroupOf (coordinateD K) ∧
      CFSG.IsQuasisimple L := by
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  let : Nontrivial L := CatalogueBAlternating.pComponent_nontrivial hL
  exact coordinateD_perfect_subnormal_classification K hodd L hL.choose_spec.2.1

theorem coordinateD_three_no_pComponent (K : Type*) [Field K] [Finite K]
    (hcard : Nat.card K = 3) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (coordinateD K)) : ¬ CFSG.IsPComponent p L := by
  intro hL
  have hodd : Odd (Nat.card K) := hcard ▸ (by decide : Odd 3)
  have hbound := (coordinateD_pComponent_classification K hodd p L hL).1
  omega

end CFSG.ComponentClassification.CatalogueBLinearTwo
