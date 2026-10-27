module

public import CFSG.ClassicalInvolution.Q3.Q3YSLift
public import CFSG.ClassicalInvolution.Q3.Q3YSInputs
public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3ZTop

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

theorem m11_nonabelian : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M11, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 := isSimpleGroup_m11_kernel
  let _ : CommGroup ↥CFSG.Blueprint.NativeSporadic.M11 :=
    { (inferInstance : Group ↥CFSG.Blueprint.NativeSporadic.M11) with mul_comm := hcon }
  have := IsSimpleGroup.prime_card (α := ↥CFSG.Blueprint.NativeSporadic.M11)
  rw [card_m11_kernel] at this
  exact absurd this (by norm_num)

theorem m11_fourGroup : ∃ F : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11, IsElemAbelian 2 F ∧
    Nat.card F = 4 ∧ F ⊓ Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 = ⊥ := by
  have hs : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 := isSimpleGroup_m11_kernel
  have hfin : Finite ↥CFSG.Blueprint.NativeSporadic.M11 :=
    Nat.finite_of_card_ne_zero (by rw [card_m11_kernel]; norm_num)
  have heven : Even (Nat.card ↥CFSG.Blueprint.NativeSporadic.M11) := by
    rw [card_m11_kernel]
    decide
  obtain ⟨E, hE, hEcard⟩ := Q3Y.exists_fourGroup_of_two_le_twoRank
    (CFSG.Walter.two_le_twoRank _ m11_nonabelian heven)
  exact ⟨E, hE, hEcard, by rw [Q3W.center_m11_eq_bot]; exact inf_bot_eq E⟩

section FourGroup


theorem fourGroup_of_valid (hFour : ModelFourGroup3On fun _ => True) (c : CompData)
    (hv : c.Valid) (hc : c ≠ CompData.sl23) (hc' : c ≠ CompData.model .PSp 2)
    (heven : Even (Nat.card c.G)) :
    ∃ F : Subgroup c.G, IsElemAbelian 2 F ∧ Nat.card F = 4 ∧ F ⊓ Subgroup.center c.G = ⊥ := by
  rcases hv with ⟨t, n, hfund, hadm, rfl⟩ | rfl | rfl
  · refine hFour t n trivial hfund hadm ?_ heven
    rintro ⟨rfl, rfl⟩
    exact hc' rfl
  · exact absurd rfl hc
  · exact m11_fourGroup

end FourGroup

section Comp


theorem zTwo_of_valid (c : CompData) (hv : c.Valid) (hc : c ≠ CompData.sl23) :
    ∀ f : c.G, (∀ m : c.G, ⁅f, m⁆ ∈ Subgroup.center c.G) → f ∈ Subgroup.center c.G := by
  rcases hv with ⟨t, n, hfund, hadm, rfl⟩ | rfl | rfl
  · have hq := ModelFacts.isQuasisimple_modelUniv t n 3 1 Nat.prime_three hfund hadm
    have : Group.IsPerfect (CompData.model t n).G := ⟨hq.1⟩
    exact fun f hf => mem_center_of_commutators_central hf
  · exact absurd rfl hc
  · intro f hf
    have hcen : Subgroup.center CompData.m11.G = ⊥ := Q3W.center_m11_eq_bot
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := hf g
    rw [hcen, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at h1
    exact h1.symm

theorem typeC3Shape_of_inputs (h3 : Q3W.OddThreeFreeInput)
    (hFour : ModelFourGroup3On fun _ => True) (hSp : Sp4KleinQuat3) : Q3Z.TypeC3Shape := by
  intro G _ _ _ hnab K z hz hBelow h3rk h4 hΔ hB _ hS hint
  have hR := Q3W.RouteD3Setup.of_hyps hz hBelow h3rk h4 hΔ hS hint
  have hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z := h3 G K z hR
  obtain ⟨hex, hP1⟩ := hS
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hzY : z ∈ locLayer (conjClass3 K) z := le_centralizingLayer hKz hz.mem
  obtain ⟨ι, hι, ⟨D⟩⟩ := hR.ih {z} (Q3W.not_subset_center_of_ne_one hnab hz.ne_one)
  obtain ⟨zb, hzb⟩ : ∃ zb : locQuot (conjClass3 K) z, zb = QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z)) ⟨z, hzY⟩ := ⟨_, rfl⟩
  have hzb1 : zb ≠ 1 := by
    rw [hzb]
    exact Q3W.mk_involution_ne_one3 (conjClass3 K) hz.orderOf_eq_two hzY
  have hzbc : ∀ w : locQuot (conjClass3 K) z, w * zb = zb * w := by
    intro w
    rw [hzb]
    exact Q3W.mk_involution_central3 (conjClass3 K) z hzY w
  have hzz : z * z = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one z
    rwa [hz.orderOf_eq_two] at this
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← map_mul]
    have : (⟨z, hzY⟩ : ↥(locLayer (conjClass3 K) z)) * ⟨z, hzY⟩ = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hmem : locImg (conjClass3 K) z K ∈ locFamily (conjClass3 K) z :=
    mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  obtain ⟨i₀, R, hRf, hRK⟩ := D.fundamental _ hmem
  have hzbK : zb ∈ locImg (conjClass3 K) z K := by
    rw [hzb]
    exact ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
  have hMFZ : RouteD.Gaps.FundNoncentral 3 := RouteD.Gaps.fundNoncentral 3
  have hk₀ : D.kind i₀ = CompData.sl23 := by
    by_contra hc
    rw [hRK] at hzbK
    obtain ⟨r, hrR, hr⟩ := hzbK
    have hr1 : r = 1 := Q3W.eq_one_of_central_comp3 hMFZ (D.kind i₀) (D.valid i₀) hc (D.hom i₀)
      (D.ker_le_center i₀) hRf hrR fun y => by
        rw [hr]
        exact (hzbc (D.hom i₀ y)).symm
    rw [hr1, map_one] at hr
    exact hzb1 hr.symm
  have hRtop : R = ⊤ := Q3Y.eq_top_of_mem_fund_sl23 hk₀ hRf
  have hrange : locImg (conjClass3 K) z K = (D.hom i₀).range := by
    rw [hRK, hRtop, Subgroup.map_top]
  have hBD : BDLoc D i₀ zb :=
    { ne_one := hzb1
      mul_self := hzb2
      central := hzbc
      mem := by
        intro F hF hcard hFC
        have hc : ∀ f ∈ F, ∀ k ∈ locImg (conjClass3 K) z K, f * k = k * f := by
          intro f hf k hk
          rw [hrange] at hk
          exact (Subgroup.mem_centralizer_iff.mp (hFC hf) k hk).symm
        obtain ⟨_hzY', hmemF⟩ := fourGroup_mem_of_not_bootData3 hex hP1 hO3 hB hK hz hF hcard hc
        rw [hzb]
        exact hmemF }
  have hnot : ∃ i, D.kind i ≠ CompData.sl23 := by
    by_contra hall
    push Not at hall
    have : Nonempty ι := ⟨i₀⟩
    have hpos : 0 < Nat.card ι := Nat.card_pos
    exact Q3W.false_of_all_a1_3 hnab hR hO3
      (⟨ι, hι, D, by omega, i₀, hk₀, fun i _ => hall i⟩ :
        Q3W.LocalShapeC3 (Nat.card ι - 1) CompData.sl23 (conjClass3 K) z)
  obtain ⟨i₁, hsp, hrest, hcard⟩ := shape_of_bdLoc hMFZ D hBD hk₀ hnot
    (fun i hi => zTwo_of_valid (D.kind i) (D.valid i) hi)
    (fun i hi hne he => fourGroup_of_valid hFour (D.kind i) (D.valid i) hi hne he)
    (fun i hi => by
      have key : ∀ c : CompData, c = CompData.model .PSp 2 → ∃ y y' : c.G, KleinQuat c.G y y' := by
        rintro c rfl
        exact hSp
      exact key _ hi)
  exact ⟨ι, hι, D, hcard, i₁, hsp, hrest⟩

end Comp

end CFSG.ClassicalInvolution.Q3.Q3YS
