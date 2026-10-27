module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Cl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem odd_card_oddCore_aux (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem odd_of_mem_oddCore_aux {X : Type*} [Group X] [Finite X] {x : X}
    (hx : x ∈ CFSG.oddCore X) : Odd (orderOf x) := by
  have h1 : orderOf (⟨x, hx⟩ : CFSG.oddCore X) ∣ Nat.card (CFSG.oddCore X) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact (odd_card_oddCore_aux X).of_dvd_nat h1

theorem sec8t84g6_simple_of_lieModel [Finite G] {X : Subgroup G}
    {tag : CFSG.Open.StatedLieTag} {n f : ℕ} (hn : n ≠ 0)
    (hm : LieModel (X ⧸ CFSG.oddCore X) tag n 3 f) :
    IsSimpleGroup (X ⧸ CFSG.oddCore X) :=
  (CFSG.LieType.Simplicity.fam_classical_converse (X ⧸ CFSG.oddCore X)
    ⟨tag, n, 3, f, hm.statedClassicalModel_of_ne_zero hn⟩).2.2

theorem sec8t84g6_simple_of_shape [Finite G] {X : Subgroup G}
    (h : IsOmega5 X ∨ IsOmega6Minus X ∨ IsL29 X ∨ IsL281 X ∨ IsL3Eps3 X) :
    IsSimpleGroup (X ⧸ CFSG.oddCore X) := by
  rcases h with h | h | h | h | h
  · exact sec8t84g6_simple_of_lieModel (by norm_num) h
  · exact sec8t84g6_simple_of_lieModel (by norm_num) h
  · exact sec8t84g6_simple_of_lieModel (by norm_num) h
  · exact sec8t84g6_simple_of_lieModel (by norm_num) h
  · rcases h with h | h
    · exact sec8t84g6_simple_of_lieModel (by norm_num) h
    · exact sec8t84g6_simple_of_lieModel (by norm_num) h

theorem sec8t84g6_center_odd [Finite G] {K : Subgroup G} (hq : IsQuasisimple ↥K)
    (hs : IsSimpleGroup (↥K ⧸ CFSG.oddCore ↥K)) :
    ∀ z ∈ K ⊓ centralizer (K : Set G), Odd (orderOf z) := by
  intro z hz
  have hzcen : (⟨z, hz.1⟩ : ↥K) ∈ center ↥K := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp hz.2 g g.2)
  rw [center_eq_oddCore_of_simple hq hs] at hzcen
  have := odd_of_mem_oddCore_aux hzcen
  rwa [Subgroup.orderOf_mk] at this

theorem sec8t84g6_layerCent_le (L : Subgroup G) (s : G) :
    layerCent L s ≤ L ⊓ centralizer ({s} : Set G) := by
  rw [layerCent, CFSG.inSubgroup]
  exact Subgroup.map_subtype_le _

theorem sec8t84g6_oddCoreIn {L : Subgroup G} [Finite G] (hq : IsQuasisimple ↥L)
    (hs : IsSimpleGroup (↥L ⧸ CFSG.oddCore ↥L)) {n : G} (hn : n ∈ oddCoreIn L) :
    (∀ l ∈ L, l * n = n * l) ∧ Odd (orderOf n) := by
  rw [oddCoreIn, CFSG.inSubgroup] at hn
  obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.mp hn
  have hcen : n' ∈ center ↥L := (center_eq_oddCore_of_simple hq hs).ge hn'
  refine ⟨fun l hl => ?_, ?_⟩
  · exact congrArg Subtype.val (mem_center_iff.mp hcen ⟨l, hl⟩)
  · have := odd_of_mem_oddCore_aux hn'
    rwa [← Subgroup.orderOf_coe] at this

theorem sec8t84g6_inv_mem_K0 [Finite G] (hGi : Sec8T84FactGamInner) {L : Subgroup G}
    (hL : IsOm6M L) {s : G} (hs : s * s = 1) (hout : InducesOutsideGStar L 6 (-1) s) {x : G}
    (hxL : x ∈ L) (hxs : x ∈ centralizer ({s} : Set G)) (hx2 : x * x = 1) :
    x ∈ layerCent L s := by
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.oddCore ↥L) :=
    sec8t84g6_simple_of_lieModel (by norm_num) hL.2
  have hmem : x ∈ layerCent L s ⊔ oddCoreIn L :=
    hGi G L hL s hs hout x ⟨hxL, hxs⟩ (fun y _ => by rw [hx2, one_mul, mul_one])
  have hle : layerCent L s ≤ L := (sec8t84g6_layerCent_le L s).trans inf_le_left
  have hcent : oddCoreIn L ≤ centralizer (layerCent L s : Set G) := fun n hn => by
    rw [mem_centralizer_iff]
    intro k hk
    exact ((sec8t84g6_oddCoreIn hL.1 hsimple hn).1 k (hle hk))
  have hnorm : oddCoreIn L ≤ normalizer (layerCent L s : Set G) := fun n hn =>
    Subgroup.centralizer_le_normalizer _ (hcent hn)
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left (layerCent L s) _ hnorm] at hmem
  obtain ⟨k, hk, n, hn, rfl⟩ := Set.mem_mul.mp hmem
  obtain ⟨hnc, hnodd⟩ := sec8t84g6_oddCoreIn hL.1 hsimple hn
  have hkn : Commute k n := hnc k (hle hk)
  have h1 : (k * n) ^ orderOf n = k * n := sec8t84g6_pow_odd_of_sq hx2 hnodd
  rw [hkn.mul_pow, pow_orderOf_eq_one, mul_one] at h1
  rw [← h1]
  exact Subgroup.pow_mem _ hk _

end CFSG.OddStandard.SmallF3.Omega
