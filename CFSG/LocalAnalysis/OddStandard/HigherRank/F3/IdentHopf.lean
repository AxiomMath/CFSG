module

public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG CFSG.Open CFSG.RankThree.PerfectCover

section Helpers

theorem exists_hopf_cover_package {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S) (π : S →* Y) (M : Subgroup S)
      (_ : griessHopfMultiplier (Y ⧸ center Y) ≃* M),
      Function.Surjective π ∧ Group.IsPerfect S ∧ π.ker ≤ M ∧ M ≤ center S ∧
        (∀ s : S, π s ∈ center Y → s ∈ M) ∧
        Nat.card M = Nat.card π.ker * Nat.card ↥(center Y) := by
  haveI hperfY : Group.IsPerfect Y := hY.1
  haveI hperfQ : Group.IsPerfect (Y ⧸ center Y) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center Y))
      (QuotientGroup.mk'_surjective (center Y))
  haveI hfinQ : Finite (Y ⧸ center Y) :=
    Finite.of_surjective (QuotientGroup.mk' (center Y))
      (QuotientGroup.mk'_surjective (center Y))
  let q : Y →* Y ⧸ center Y := QuotientGroup.mk' (center Y)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective (center Y)
  have hker : q.ker ≤ center Y := le_of_eq (QuotientGroup.ker_mk' (center Y))
  let π : HopfCover (Y ⧸ center Y) →* Y := hopfLift q hq hker
  have hcomp : q.comp π = hopfCoverMap (Y ⧸ center Y) := comp_hopfLift q hq hker
  have hkerM : π.ker ≤ hopfMultiplier (Y ⧸ center Y) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [← hcomp, MonoidHom.comp_apply, hx, map_one]
  have hMlift : ∀ s : HopfCover (Y ⧸ center Y),
      π s ∈ center Y → s ∈ hopfMultiplier (Y ⧸ center Y) := by
    intro s hs
    rw [MonoidHom.mem_ker]
    have hs' : q (π s) = 1 :=
      le_of_eq (QuotientGroup.ker_mk' (center Y)).symm hs
    have hmap : hopfCoverMap (Y ⧸ center Y) s = q (π s) := by
      rw [← hcomp]; rfl
    rw [hmap, hs']
  have hmapM : (hopfMultiplier (Y ⧸ center Y)).map π = center Y := by
    rw [map_hopfMultiplier_hopfLift q hq hker, QuotientGroup.ker_mk']
  have hcard : Nat.card (hopfMultiplier (Y ⧸ center Y)) =
      Nat.card π.ker * Nat.card ↥(center Y) := by
    have hcardφ := Subgroup.card_ker_mul_card_range
      (π.domRestrict (hopfMultiplier (Y ⧸ center Y)))
    have hφker : Nat.card (π.domRestrict (hopfMultiplier (Y ⧸ center Y))).ker =
        Nat.card π.ker := by
      rw [MonoidHom.ker_domRestrict]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerM).toEquiv
    have hφrange : Nat.card (π.domRestrict (hopfMultiplier (Y ⧸ center Y))).range =
        Nat.card ↥(center Y) := by
      rw [MonoidHom.domRestrict_range, hmapM]
    rw [hφker, hφrange] at hcardφ
    exact hcardφ.symm
  exact ⟨HopfCover (Y ⧸ center Y), inferInstance, finite_hopfCover hperfQ, π,
    hopfMultiplier (Y ⧸ center Y), hopfMultiplierEquivGriess (Y ⧸ center Y),
    hopfLift_surjective q hq hker, hopfCover_isPerfect, hkerM,
    hopfMultiplier_le_center, hMlift, hcard⟩

end Helpers

theorem exists_hopf_cover_data {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y)
    {z : Y} (hz : z ∈ center Y) (hz2 : orderOf z = 2)
    (hstar : ∀ x y : griessHopfMultiplier (Y ⧸ center Y),
      orderOf x = 2 → orderOf y = 2 → x = y)
    (hdef : ordProj[2] (Nat.card ↥(center Y)) ≠
      ordProj[2] (Nat.card (griessHopfMultiplier (Y ⧸ center Y)))) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S) (π : S →* Y), Function.Surjective π ∧
      Group.IsPerfect S ∧ π.ker ≤ center S ∧
      ∀ s : S, π s = z → s ∈ center S ∧ s ^ 2 ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, _, _, π, M, e, hπs, hSp, hkerM, hMc, hMlift, hcard⟩ := exists_hopf_cover_package hY
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  refine ⟨S, inferInstance, inferInstance, π, hπs, hSp, hkerM.trans hMc, fun s hs => ?_⟩
  have hsM : s ∈ M := hMlift s (hs ▸ hz)
  refine ⟨hMc hsM, fun hs2 => ?_⟩
  have h2 : 2 ∣ Nat.card π.ker := by
    by_contra h
    apply hdef
    have h1 : Nat.card (griessHopfMultiplier (Y ⧸ center Y)) =
        Nat.card π.ker * Nat.card ↥(center Y) := by
      rw [Nat.card_congr e.toEquiv, hcard]
    rw [h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h, zero_add]
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hdM : (d : S) ∈ M := hkerM d.2
  have hs1 : s ≠ 1 := fun h => hz1 (by rw [← hs, h, map_one])
  have hs2' : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have hxd : orderOf (e.symm ⟨(d : S), hdM⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hd]
  have hxs : orderOf (e.symm ⟨s, hsM⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hs2']
  have hxx := hstar _ _ hxd hxs
  have hds : (d : S) = s := congrArg Subtype.val (e.symm.injective hxx)
  apply hz1
  rw [← hs, ← hds]
  exact MonoidHom.mem_ker.mp d.2

end CFSG.OddStandard.HigherRank.F3.Ident
