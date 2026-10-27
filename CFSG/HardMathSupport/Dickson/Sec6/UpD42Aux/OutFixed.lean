module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem UpD42Pumpup.card_d42_dvd_fixed {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : UpD42Pumpup S α) :
    174182400 ∣ Nat.card ↥(fixSubgroup α) := by
  obtain ⟨-, -, I, hI, hD⟩ := h
  have hquot := Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥I)
  rw [card_of_isD42Type hD] at hquot
  exact hquot.trans (Subgroup.card_dvd_of_le hI.1)

theorem UpD42Pumpup.card_d42_dvd {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : UpD42Pumpup S α) : 174182400 ∣ Nat.card S :=
  h.card_d42_dvd_fixed.trans (Subgroup.card_subgroup_dvd_card (fixSubgroup α))

theorem UpD42Pumpup.not_solvable_fixed {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : UpD42Pumpup S α) : ¬ Group.IsSolvable ↥(fixSubgroup α) := by
  obtain ⟨-, -, I, hI, hD⟩ := h
  intro hsol
  haveI : Group.IsSolvable ↥I :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hI.1)
      (Subgroup.inclusion_injective hI.1)
  haveI := (isSimpleGroup_of_isD42Type hD).1
  obtain ⟨a, b, hab⟩ := (isSimpleGroup_of_isD42Type hD).2
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := barOf 3 I)).2 inferInstance a b)

theorem isD42Type_of_upD42Pumpup_of_simple_normal_comm {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : UpD42Pumpup S α) (J : Subgroup S)
    (hJC : J ≤ fixSubgroup α) (hcomm : ⁅fixSubgroup α, fixSubgroup α⁆ ≤ J)
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a) :
    IsCatalogLieIso ↥J IsD42Index := by
  obtain ⟨-, -, I, hI, hD⟩ := h
  haveI := hs
  have hq : CFSG.Open.IsQuasisimple ↥J := Up34Chev2.isQuasisimple_of_simple_up34 hnab
  have hIC : I ≤ fixSubgroup α := hI.1
  have hIJ : I ≤ J := by
    calc I = ⁅I, I⁆ := (glaPComponent_perfect hI).symm
      _ ≤ ⁅fixSubgroup α, fixSubgroup α⁆ := Subgroup.commutator_mono hIC hIC
      _ ≤ J := hcomm
  have hsn : IsSubnormal I J := isSubnormal_of_le_of_le hI.2.1 hIJ hJC
  have hIeq : I = J := eq_of_isSubnormal_of_quasisimple hq hsn
    (glaPComponent_perfect hI) (glaPComponent_ne_bot hI)
  obtain ⟨e⟩ := Up34Chev2.barOf_equiv_of_component_eq hI hIeq hs
  exact IsCatalogLieIso.of_mulEquiv e hD

theorem isD42Type_of_component_of_normal_simple {S : Type} [Group S] [Finite S]
    {D I : Subgroup S} (hI : GLAPComponent 3 D I)
    (hD : IsCatalogLieIso (barOf 3 I) IsD42Index) (J : Subgroup S)
    (hJC : J ≤ D) [(J.subgroupOf D).Normal]
    (hsol : Group.IsSolvable (↥D ⧸ J.subgroupOf D))
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a) :
    IsCatalogLieIso ↥J IsD42Index := by
  haveI := hs
  have hq : CFSG.Open.IsQuasisimple ↥J := Up34Chev2.isQuasisimple_of_simple_up34 hnab
  have hIJ : I ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient
      hJC hsol hI.1 (glaPComponent_perfect hI)
  have hsn : IsSubnormal I J := isSubnormal_of_le_of_le hI.2.1 hIJ hJC
  have hIeq : I = J := eq_of_isSubnormal_of_quasisimple hq hsn
    (glaPComponent_perfect hI) (glaPComponent_ne_bot hI)
  obtain ⟨e⟩ := Up34Chev2.barOf_equiv_of_component_eq hI hIeq hs
  exact IsCatalogLieIso.of_mulEquiv e hD

theorem isD42Type_of_upD42Pumpup_of_fixEquiv_simple {S X : Type}
    [Group S] [Finite S] [Group X] {α : MulAut S} (h : UpD42Pumpup S α)
    (e : ↥(fixSubgroup α) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : IsCatalogLieIso X IsD42Index := by
  haveI := hs
  have hsC : IsSimpleGroup ↥(fixSubgroup α) := e.isSimpleGroup
  have hnabC : ∃ a b : ↥(fixSubgroup α), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun he => hab ?_⟩
    have he' := congrArg e he
    simpa only [map_mul, MulEquiv.apply_symm_apply] using he'
  refine IsCatalogLieIso.of_mulEquiv e
    (isD42Type_of_upD42Pumpup_of_simple_normal_comm h (fixSubgroup α) le_rfl ?_
      hsC hnabC)
  exact Subgroup.commutator_le.2 fun a ha b hb =>
    (fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem ha hb)
      ((fixSubgroup α).inv_mem ha)) ((fixSubgroup α).inv_mem hb)

end CFSG.HardMathSupport.Dickson.Sec6

end
