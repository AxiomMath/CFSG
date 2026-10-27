module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.FieldAutCatalog
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812FieldAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.FieldAutLift
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K7145Comp

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.ComponentClassification CFSG.RankThree.PartTwo.KFacts

section Certified


theorem kFactFieldAutThree_holds
    : KFactFieldAutThree := by
  intro X _ _ hK L hL hLn hr a ha ha' P hP _
  haveI := hLn
  haveI : Group.IsPerfect L := hL.1.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  obtain ⟨Q, rfl⟩ := hP
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, hne⟩ := exists_ne_of_sylow_of_catalog hL.1.2.1 hL.1.2.2
    (CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.isCatalogGroup_quotient_center hK L
      ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩)
    (pRank_quotient_center_eq_one_of_isComponent hL hr)
    (PerfectAutomorphisms.centerQuotientHom L (MulAut.conjNormal a))
    (by rw [← map_pow, ← map_pow, ha3, map_one, map_one]) (not_isInnerAut_centerQuotientHom L ha')
    (Q.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)))
  rw [Sylow.coe_mapSurjective] at hy
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
  apply hne
  have h1 : MulAut.conjNormal a q = q := Subtype.ext (by
    rw [MulAut.conjNormal_apply, hcon (q : X) (Subgroup.mem_map_of_mem L.subtype hq),
      mul_inv_cancel_right])
  exact (PerfectAutomorphisms.onCenterQuotient_apply_mk (MulAut.conjNormal a) q).trans
    (by rw [h1])

theorem kFactFieldAutInvert_holds
    : KFactFieldAutInvert := by
  intro X _ _ hK L hL hLn hr a ha3 ha' A hAL hA3 haA
  haveI := hLn
  haveI : Group.IsPerfect L := hL.1.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : ∀ z ∈ Subgroup.center L, z ^ 3 = 1 → z = 1 := fun z hz hz3 =>
    eq_one_of_mem_center_of_isComponent hL hr.le hz hz3
  haveI : IsCyclic A := isCyclic_of_prime_card hA3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hgord : orderOf g = 3 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hA3
  have hg3 : g ^ 3 = 1 := hgord ▸ pow_orderOf_eq_one g
  obtain ⟨u, hu⟩ : ∃ u : L, (u : X) = g := ⟨⟨g, hAL g.2⟩, rfl⟩
  have hu3 : u ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hu, Subgroup.coe_one, ← Subgroup.coe_pow, hg3, Subgroup.coe_one])
  have hu1 : QuotientGroup.mk' (Subgroup.center L) u ≠ 1 := fun h => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have h2 : g = 1 := Subtype.ext (hu.symm.trans (congrArg Subtype.val (hZ u h hu3)))
    rw [h2, orderOf_one] at hgord
    norm_num at hgord
  have hfix : MulAut.conjNormal a u = u := Subtype.ext (by
    rw [MulAut.conjNormal_apply, hu, haA g g.2, mul_inv_cancel_right])
  obtain ⟨y, hyψ, hyu⟩ := exists_inverting_of_catalog hL.1.2.1 hL.1.2.2
    (CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.isCatalogGroup_quotient_center hK L
      ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩)
    (pRank_quotient_center_eq_one_of_isComponent hL hr)
    (PerfectAutomorphisms.centerQuotientHom L (MulAut.conjNormal a))
    (by rw [← map_pow, ← map_pow, ha3, map_one, map_one]) (not_isInnerAut_centerQuotientHom L ha')
    (QuotientGroup.mk' (Subgroup.center L) u) (by rw [← map_pow, hu3, map_one]) hu1
    ((PerfectAutomorphisms.onCenterQuotient_apply_mk (MulAut.conjNormal a) u).trans
      (by rw [hfix]))
  obtain ⟨t₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) y
  obtain ⟨t, ht, hta⟩ := exists_commute_mk_eq_of_fixed
    (not_three_dvd_card_center_of_isComponent hL hr.le) ha3 t₀ hyψ
  have htu : t * u * t⁻¹ = u⁻¹ := mul_mul_inv_eq_inv_of_mk_center hZ hu3 (by rw [ht]; exact hyu)
  have htg : (t : X) * g * (t : X)⁻¹ = (g : X)⁻¹ := by
    have h := congrArg Subtype.val htu
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hu] at h
  refine ⟨(t : X), t.2, hta, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨z, hz⟩)
  have hz' : (g : X) ^ k = z := by rw [← Subgroup.coe_zpow, hk]
  rw [← hz', ← conj_zpow, htg, inv_zpow]

end Certified

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
