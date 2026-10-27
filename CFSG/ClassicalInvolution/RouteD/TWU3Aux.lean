module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourLift
public import CFSG.ClassicalInvolution.RouteD.TWEB6Layer

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.TWE.B6 CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.Open (classicalInvolutionOddCore)

set_option linter.unusedSectionVars false

section Aux

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}


theorem locElt_congr {y y' : G} (hy : y ∈ locLayer Ω x) (hy' : y' ∈ locLayer Ω x) (h : y = y') :
    locElt Ω x y hy = locElt Ω x y' hy' := by
  subst h
  rfl

theorem commute_of_commutes {A B : Subgroup G} (h : Commutes A B) {a b : G} (ha : a ∈ A)
    (hb : b ∈ B) : Commute a b := h a ha b hb

theorem locElt_eq_one {y : G} (hy : y ∈ locLayer Ω x) (h : y = 1) : locElt Ω x y hy = 1 := by
  subst h
  exact map_one _

theorem eq_of_locElt_eq_of_sq (hP1 : LocalOddCentral Ω {x}) {y y' : G} (hy : y ∈ locLayer Ω x)
    (hy' : y' ∈ locLayer Ω x) (hyy : y * y = 1) (hy'y' : y' * y' = 1)
    (h : locElt Ω x y hy = locElt Ω x y' hy') : y = y' := by
  set Y : ↥(locLayer Ω x) := ⟨y, hy⟩ with hYdef
  set Y' : ↥(locLayer Ω x) := ⟨y', hy'⟩ with hY'def
  have hYY : Y * Y = 1 := Subtype.ext hyy
  have hY'Y' : Y' * Y' = 1 := Subtype.ext hy'y'
  have h1 : Y⁻¹ * Y' ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := QuotientGroup.eq.mp h
  set o : ↥(locLayer Ω x) := Y⁻¹ * Y' with ho
  have hoc : ∀ g, g * o = o * g := fun g => Subgroup.mem_center_iff.mp (hP1 h1) g
  have hY'o : Y' = Y * o := by rw [ho]; group
  have ho2 : o * o = 1 := by
    have h2 : Y' * Y' = (Y * Y) * (o * o) := by
      calc Y' * Y' = (Y * o) * (Y * o) := by rw [← hY'o]
        _ = Y * (o * Y) * o := by group
        _ = Y * (Y * o) * o := by rw [← hoc Y]
        _ = (Y * Y) * (o * o) := by group
    rw [hY'Y', hYY, one_mul] at h2
    exact h2.symm
  have ho1 : o = 1 := by
    set o' : ↥(classicalInvolutionOddCore ↥(locLayer Ω x)) := ⟨o, h1⟩ with ho'
    have h2 : orderOf o' ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      show o ^ 2 = 1
      rw [pow_two, ho2]
    have h3 : orderOf o' ∣ Nat.card ↥(classicalInvolutionOddCore ↥(locLayer Ω x)) :=
      orderOf_dvd_natCard o'
    have h4 : Nat.Coprime 2 (Nat.card ↥(classicalInvolutionOddCore ↥(locLayer Ω x))) :=
      Nat.coprime_two_left.mpr (CFSG.ComponentClassification.OddCore.odd_card _)
    have h5 : orderOf o' ∣ 1 := by
      have := Nat.dvd_gcd h2 h3
      rwa [h4] at this
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5))
  rw [ho1, mul_one] at hY'o
  exact (congrArg Subtype.val hY'o).symm


theorem exists_lift_elt {t : StatedLieTag} {n : ℕ} (e : Layer0 p f Ω x t n) {L : Subgroup G}
    {R : Subgroup (modelUniv t n p f Fact.out).K} (hLR : locImg Ω x L = R.map e.φ)
    {r : (modelUniv t n p f Fact.out).K} (hr : r ∈ R) :
    ∃ (y : G) (hy : y ∈ locLayer Ω x), y ∈ L ∧ locElt Ω x y hy = e.φ r := by
  have hmem : e.φ r ∈ locImg Ω x L := hLR ▸ ⟨r, hr, rfl⟩
  obtain ⟨y', hy', hyr⟩ := hmem
  exact ⟨y', y'.2, Subgroup.mem_subgroupOf.mp hy', hyr⟩

theorem exists_sqrt_member {t : StatedLieTag} {n : ℕ} (e : Layer0 p f Ω x t n) (hY : YData p f t n)
    (hex : ExactMembers Ω) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    {R : Subgroup (modelUniv t n p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hLR : locImg Ω x L = R.map e.φ) {w : G} (hw : IsClassicalMember p f L w)
    {a : (modelUniv t n p f Fact.out).K} (ha : a ∈ R) (hsq : ∀ r ∈ R, orderOf r = 2 → r = a * a) :
    ∃ (A : G) (hA : A ∈ locLayer Ω x), A ∈ L ∧ locElt Ω x A hA = e.φ a ∧ A * A = w := by
  obtain ⟨A, hAY, hAL, hAφ⟩ := exists_lift_elt e hLR ha
  obtain ⟨r, hr, hφr⟩ := e.exists_involution hY hL hR hLR hw
  have hwY : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hAA : A * A ∈ locLayer Ω x := (locLayer Ω x).mul_mem hAY hAY
  have heq : locMk Ω x ⟨A * A, hAA⟩ = locMk Ω x ⟨w, hwY⟩ := by
    have h1 : locElt Ω x (A * A) hAA = locElt Ω x w hwY := by
      rw [← locElt_mul hAY hAY, hAφ, ← map_mul, ← hsq r hr.1 hr.2, hφr]
    exact h1
  refine ⟨A, hAY, hAL, hAφ, ?_⟩
  exact congrArg Subtype.val (Exotic.locMk_inj_of_member hex hL (a := ⟨A * A, hAA⟩)
    (b := ⟨w, hwY⟩) (L.mul_mem hAL hAL) hw.mem heq)

end Aux

end CFSG.ClassicalInvolution.RouteD.TWU
