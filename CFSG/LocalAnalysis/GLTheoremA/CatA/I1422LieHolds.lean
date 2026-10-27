module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1422Char2Of
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FParQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FParAbs
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123c
public import CFSG.LieType.ChevTwo.Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MClose

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

private theorem eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] (K : Subgroup G)
    (hK : Odd (Nat.card K)) {x : G} (hx : x ∈ K) (h2 : x ^ 2 = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : K) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h2))
  have h2' : orderOf (⟨x, hx⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  have hcop : Nat.Coprime 2 (Nat.card K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Odd.not_two_dvd_nat hK)
  have h3 : orderOf (⟨x, hx⟩ : K) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2'
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)

section Cert

theorem i1422Lie2Fact_holds : I1422Lie2Fact := by
  intro H _ _ β hβ hQ hchev hodd J hJ
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center H with hZdef
  set π : H →* H ⧸ Z := QuotientGroup.mk' Z with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker ≤ Subgroup.center H := by rw [QuotientGroup.ker_mk']
  set βb : MulAut (H ⧸ Z) := QuotientGroup.congr Z Z β (Subgroup.map_center_eq β) with hβbdef
  have hβb : ∀ x : H, βb (π x) = π (β x) := fun x => rfl
  have hαβ : ∀ k : H, π (β k) = βb (π k) := fun k => (hβb k).symm
  have hβb3 : βb ^ 3 = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπs y
    have h1 : (β ^ 3) x = x := by rw [hβ]; rfl
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hβb, hβb, hβb,
      MulAut.one_apply]
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply] at h1
    rw [h1]
  obtain ⟨-, hsimp, hab⟩ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native H).1 hQ
  have hE : IsElemAbelian 3 (Subgroup.zpowers βb) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
      change (a : MulAut (H ⧸ Z)) * b = b * a
      rw [← hm, ← hn]
      exact (Commute.zpow_zpow_self βb m n).eq
    · intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hβb3, one_zpow]
  have hfix : I142.centFix (Subgroup.zpowers βb) = fixSubgroup βb := I142.centFix_zpowers βb
  have hJb : GLAPComponent 3 (fixSubgroup βb) (J.map π) :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup π hker β βb hαβ hπs
      Nat.prime_three hJ
  have hJbperf : ⁅J.map π, J.map π⁆ = J.map π :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJb
  have hPL : J.map π ≤ GLALayer (fixSubgroup βb) := by
    have h := I142.lieSemisimpleCentE_of_residuals I142.residualCyc_holds
      I142M.residualNonCyc_holds (H ⧸ Z) hsimp hab hchev 3 Nat.prime_three (by norm_num)
      (Subgroup.zpowers βb) hE (J.map π) (by rw [hfix]; exact hJb.1) hJbperf
    rwa [hfix] at h
  have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJb hPL).1
  have hJbq : CFSG.Open.IsQuasisimple ↥(J.map π) := hcomp.2.2
  have hperf : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.2 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  have hJq : CFSG.IsQuasisimple ↥J :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_central_cover (π.subgroupMap J)
      (MonoidHom.subgroupMap_surjective π J) hperf
      (CFSG.HardMathSupport.Solomon.Coordinator.ker_subgroupMap_le_center π hker J)
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hJbq)
  refine ⟨(CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hJq,
    ?_⟩
  have hO2 : pCoreOf 2 (fixSubgroup βb) = ⊥ := by
    rw [← hfix, ← I141FPar.autCentralizer_eq_centFix]
    exact CFSG.LieType.ChevTwo.chev2CoreCent_of_leaves _ hsimp hab
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma123.isChevTwo_of_isChevSimple_two hchev)
      3 Nat.prime_three (by norm_num) _ (CFSG.Open.IsElemAbelian.isPGroup hE)
  set M : Subgroup (H ⧸ Z) := ((Subgroup.center ↥J).map J.subtype).map π with hMdef
  have hMP : M ≤ J.map π := Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hMc : ∀ m ∈ M, ∀ x ∈ J.map π, m * x = x * m := by
    intro m hm x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hm
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hc
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hx
    have h := Subgroup.mem_center_iff.1 hc' ⟨j, hj⟩
    have h' : j * (c' : H) = (c' : H) * j := congrArg Subtype.val h
    rw [← map_mul, ← map_mul, Subgroup.coe_subtype, h']
  have hModd : Odd (Nat.card M) :=
    I141FPar.odd_card_of_commute_of_isSubnormal hcomp.2.1 hO2 hMP hMc
  by_contra hev
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
  obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' 2 hev
  set w : H := ((z : ↥J) : H) with hwdef
  have hw2 : w ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hz2] at h1
    have h2 := congrArg (fun t : ↥(Subgroup.center ↥J) => ((t : ↥J) : H)) h1
    simpa using h2
  have hw1 : w ≠ 1 := by
    intro h
    have hz1 : z = 1 := Subtype.ext (Subtype.ext (by simpa [hwdef] using h))
    rw [hz1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hwM : π w ∈ M := ⟨w, ⟨(z : ↥J), z.2, rfl⟩, rfl⟩
  have hπw : π w = 1 :=
    eq_one_of_sq_eq_one_of_odd M hModd hwM (by rw [← map_pow, hw2, map_one])
  have hwZ : w ∈ Z := (QuotientGroup.eq_one_iff w).1 hπw
  exact hw1 (eq_one_of_sq_eq_one_of_odd Z hodd hwZ hw2)

end Cert

end CFSG.LocalAnalysis.GLTheoremA

end
