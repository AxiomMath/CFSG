module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform

section Sec

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem members_sylow_q8 (h : PerpHypS n Y R S t) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup 2) := by
  have hC := CoreData.of_S h.core
  rintro _ ⟨g', rfl⟩
  apply forall_sylow_iso_of_exists
  obtain ⟨P, hP', ⟨e⟩⟩ := hC.datum.exists_sylow_q8 hC.q8
  exact ⟨conjSub g' P, hP'.conj g', ⟨(Subgroup.equivMapOfInjective P (MulAut.conj g').toMonoidHom
    (MulAut.conj g').injective).symm.trans e⟩⟩

theorem p23_q8Section (h : PerpHypS n Y R S t) {c : Y} (hc : c * c = 1) :
    Q8Section (SecQ R c) (TwinDisc.secFam (Om R) c) := by
  have hC := CoreData.of_S h.core
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc
  exact q8Section_secFam hC.hyp hc2
    (TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup))
    (members_sylow_q8 h) hC.aEmpty_all

theorem centralizer_ne_top (h : PerpHypS n Y R S t) {c : Y} (hc1 : c ≠ 1) :
    Subgroup.centralizer ({c} : Set Y) ≠ ⊤ := by
  have hC := CoreData.of_S h.core
  haveI := hC.simple
  have hbot := CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hC.nonab
  intro htop
  apply hc1
  have hcen : c ∈ Subgroup.centralizer (↑(genFittingFStar Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    have : g ∈ Subgroup.centralizer ({c} : Set Y) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rw [hbot] at hcen
  exact Subgroup.mem_bot.mp hcen

theorem secQ_card_lt (h : PerpHypS n Y R S t) {c : Y} (hc1 : c ≠ 1) :
    Nat.card (SecQ R c) < n := by
  have hC := CoreData.of_S h.core
  rw [← hC.card]
  have h1 : Nat.card (SecQ R c) ≤ Nat.card ↥(coreHull (Om R) c) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card ↥(coreHull (Om R) c) ≤ Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) :=
    Subgroup.card_le_card_group _
  have h3 : Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) < Nat.card Y := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq => ?_
    exact centralizer_ne_top h hc1 ((Subgroup.card_eq_iff_eq_top _).mp heq)
  omega

theorem secDecomp_of_noExit (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h : PerpHypS n Y R S t) {c : Y} (hc : c * c = 1) (hc1 : c ≠ 1)
    (hne : (TwinDisc.secFam (Om R) c).Nonempty) (hno : SecNoExit R c) :
    Nonempty (OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) c))) :=
  (lieDecomp_of_noExit hcit hP (secQ_card_lt h hc1) (p23_q8Section h hc) hne hno).2.2.2

end Sec

section Parts

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_yType (hx : P23Y5Exit n) (hi : P23Y5Ident n) (hmem : P23Members n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) :
    YType R u e := by
  by_cases hno : SecNoExit R u
  · have hu1 : u ≠ 1 := hc.data.hu1
    obtain ⟨D⟩ := secDecomp_of_noExit hcit hP hc.std.perp hc.data.hu2 hu1
      (hmem Y R S t K' W u e g hc).2 hno
    rcases hi hcit hP Y R S t K' W u e g hc hno D with h | h
    · exact Or.inr (Or.inl ⟨D, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨D, h⟩))
  · rcases hx hcit hP Y R S t K' W u e g hc hno with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))

end Parts

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
