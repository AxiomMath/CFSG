module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.GzCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma gzIrr_gxy_eq_map_centralizer {G : Type} [Group G] {w : G} (y : ↥(Gx w)) :
    Gxy (y : G) w = (Subgroup.centralizer ({y} : Set ↥(Gx w))).map (Gx w).subtype := by
  ext g
  rw [mem_Gxy]
  constructor
  · intro hg
    refine Subgroup.mem_map_of_mem (f := (Gx w).subtype)
      (K := Subgroup.centralizer ({y} : Set ↥(Gx w))) (x := ⟨g, hg.2⟩) ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (mem_Gx.mp hg.1).symm
  · intro hg
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp hg
    have hgval : (u : G) = g := hug
    constructor
    · rw [mem_Gx]
      have hu' := congrArg (fun t : ↥(Gx w) => (t : G))
        (Subgroup.mem_centralizer_singleton_iff.mp hu)
      rw [← hgval]
      exact hu'.symm
    · rw [← hgval]; exact u.2

private noncomputable def gzIrr_gxyMulEquivCentralizer {G : Type} [Group G] {w : G}
    (y : ↥(Gx w)) :
    ↥(Gxy (y : G) w) ≃* ↥(Subgroup.centralizer ({y} : Set ↥(Gx w))) :=
  (MulEquiv.subgroupCongr (gzIrr_gxy_eq_map_centralizer y)).trans
    (Subgroup.equivMapOfInjective _ (Gx w).subtype Subtype.coe_injective).symm

private lemma gzIrr_eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {H : Type*} [Group H] {g h : H}
    (hg : g ^ 2 = 1) (hh : h ∈ Subgroup.zpowers g) : h = 1 ∨ h = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  by_cases hg1 : g = 1
  · left; rw [hg1]; simp
  · have hord : orderOf g = 2 := orderOf_eq_prime hg hg1
    have hk : g ^ (k % 2) = g ^ k := by
      have h := zpow_mod_orderOf g k
      rw [hord] at h
      simpa using h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [← hk, h0]; simp
    · right; rw [← hk, h1]; simp

theorem gz_irreducible (hD : AschbacherDichotomy) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hq : ∃ q : G, q ∈ Qz z ∧ q ≠ 1 ∧ q ≠ z ∧ IsShapeTwoTwoSixS5 ↥(Gxy z q)) :
    ∀ W : Subgroup G, Subgroup.zpowers z ≤ W → W ≤ Qz z →
      (∀ g ∈ derivedOf (Gx z), ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
        W = Subgroup.zpowers z ∨ W = Qz z := by
  obtain ⟨Q, hQ, hQW, hQz⟩ := exists_Qz_eq h.cent_z
  haveI : Q.Normal := hQ
  obtain ⟨q, hqQz, hq1, hqz, hsh⟩ := hq
  have hqQz' : q ∈ Q.map (Gx z).subtype := by rwa [hQz] at hqQz
  obtain ⟨q', hq'Q, hq'eq⟩ := Subgroup.mem_map.mp hqQz'
  have hq'notcent : q' ∉ centerOf Q := by
    rw [centerOf_eq_zpowers h.orderOf_z hQW]
    intro hmem
    have hord : orderOf (GxSelf z) = 2 := by
      change orderOf (⟨z, self_mem_Gx z⟩ : ↥(Gx z)) = 2
      rw [Subgroup.orderOf_mk]
      exact h.orderOf_z
    have hg2 : (GxSelf z) ^ 2 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    rcases gzIrr_eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hg2 hmem with h1 | h1
    · exact hq1 (hq'eq ▸ (by rw [h1]; rfl))
    · exact hqz (hq'eq ▸ (by rw [h1]; rfl))
  have heq : Gxy z q = Gxy (q' : G) z := by
    rw [Gxy_comm z q]
    exact congrArg (fun t : G => Gxy t z) hq'eq.symm
  have hsh' : IsShapeTwoTwoSixS5 ↥(Subgroup.centralizer ({q'} : Set ↥(Gx z))) :=
    IsShapeTwoTwoSixS5.of_mulEquiv
      ((MulEquiv.subgroupCongr heq).trans (gzIrr_gxyMulEquivCentralizer q')) hsh
  exact (cIrreducible_iff h.orderOf_z hQW hQz).mp
    (cIrreducible_of_exists_shape hD hQW hq'Q hq'notcent hsh')

end CFSG.EvenSporadicStandard.HNRecog.Section3
