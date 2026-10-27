module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Local
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups commutatorElement


section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem nonempty_mulEquiv_locImg3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) : Nonempty (locImg Ω x L ≃* SL(2, ZMod 3)) := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hLY := le_centralizingLayer hL
  let e := Subgroup.subgroupOfEquivOfLe hLY
  have hO : classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x)) = ⊥ := by
    have h1 : Subgroup.map e.toMonoidHom
        (classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x))) =
        classicalInvolutionOddCore ↥L :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [hex L hL.1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hinf := inf_oddCore_eq_bot hO
  set ψ : L.subgroupOf (locLayer Ω x) →* locQuot Ω x :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).comp
      (L.subgroupOf (locLayer Ω x)).subtype with hψ
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hker : (a : ↥(locLayer Ω x)) ∈ (L.subgroupOf (locLayer Ω x)) ⊓
        classicalInvolutionOddCore ↥(locLayer Ω x) :=
      ⟨a.2, (QuotientGroup.eq_one_iff _).mp ha⟩
    rw [hinf, Subgroup.mem_bot] at hker
    exact Subtype.ext hker
  have hrange : ψ.range = locImg Ω x L := by
    unfold locImg
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e'⟩ := hz.nonempty_equiv_sl2 (hex L hL.1)
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hinj).symm.trans
    (e.trans e'))⟩

theorem card_center_locImg3_dvd_two (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) :
    Nat.card (Subgroup.center (locImg Ω x L)) ∣ 2 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_locImg3 hΩ hex hL
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact G2D4.card_center_sl2_dvd_two

theorem image_involution_facts3 {N : Subgroup G} {w : G}
    (hN : N ∈ centralizingMembers Ω {x}) (hw : IsClassicalMember3 N w) :
    ∃ hwY : w ∈ locLayer Ω x,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ ∈ locImg Ω x N ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ = 1 ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ ≠ 1 ∧
      ∀ y ∈ locImg Ω x N,
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ * y =
          y * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ := by
  have hwY : w ∈ locLayer Ω x := le_centralizingLayer hN hw.mem
  refine ⟨hwY, ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩, ?_,
    G2D4.mk_ne_one_of_involution hwY hw.orderOf_eq_two, ?_⟩
  · rw [← map_mul]
    have : (⟨w, hwY⟩ : ↥(locLayer Ω x)) * ⟨w, hwY⟩ = 1 := by
      apply Subtype.ext
      have h2 : w ^ 2 = 1 := by rw [← hw.orderOf_eq_two]; exact pow_orderOf_eq_one w
      simpa [pow_two] using h2
    rw [this, map_one]
  · rintro _ ⟨n, hn, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.isSubnormal_le hw.subnormal hnN)
    exact this.symm

theorem mul_self_eq_one_of_isClassicalMember3 {N : Subgroup G} {w : G}
    (hw : IsClassicalMember3 N w) : w * w = 1 := by
  have h2 : w ^ 2 = 1 := by rw [← hw.orderOf_eq_two]; exact pow_orderOf_eq_one w
  simpa [pow_two] using h2

end Members

end CFSG.ClassicalInvolution.Q3.Q3W
