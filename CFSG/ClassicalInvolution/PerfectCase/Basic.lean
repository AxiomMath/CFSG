module

public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
import CFSG.ClassicalInvolution.SL2Facts
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ComponentClassification
open scoped MatrixGroups

theorem classicalInvolutionWitness_of_quotientEquiv {A B : Type*} [Group A] [Group B]
    {JA : Subgroup A} {JB : Subgroup B}
    (q : (JA ⧸ classicalInvolutionOddCore JA) ≃* (JB ⧸ classicalInvolutionOddCore JB))
    (h : classicalInvolutionWitness JA) : classicalInvolutionWitness JB := by
  have hZ : (Subgroup.center (JA ⧸ classicalInvolutionOddCore JA)).map q.toMonoidHom =
      Subgroup.center (JB ⧸ classicalInvolutionOddCore JB) := Subgroup.map_center_eq q
  rcases h with ⟨p, n, hp, hp2, hn, ⟨φ⟩⟩ | ⟨hqs, hcard, ⟨ψ⟩⟩
  · exact Or.inl ⟨p, n, hp, hp2, hn, ⟨q.symm.trans φ⟩⟩
  · refine Or.inr ⟨Components.quasisimple_of_equiv q.symm hqs, ?_,
      ⟨(QuotientGroup.congr _ _ q hZ).symm.trans ψ⟩⟩
    rw [← hcard, ← hZ]
    exact Subgroup.card_map_of_injective q.injective

theorem isQuasisimple_specialLinearGroup_two {F : Type*} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) : CFSG.Open.IsQuasisimple SL(2, F) :=
  ⟨(sl2_isPerfect h4).commutator_eq_top, Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4⟩

theorem not_isSolvable_of_open_isQuasisimple {P : Type*} [Group P] (h : CFSG.Open.IsQuasisimple P) :
    ¬ Group.IsSolvable P := by
  intro hs
  have hne : Nontrivial P := Quasisimple.nontrivial h
  obtain ⟨n, hn⟩ := (Group.isSolvable_def P).mp hs
  have hperf : ∀ k, derivedSeries P k = ⊤ := by
    intro k
    induction k with
    | zero => exact derivedSeries_zero P
    | succ k ih =>
      rw [derivedSeries_succ, ih, ← commutator_def]
      exact h.1
  rw [hperf n] at hn
  exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup P)).mp
    (inferInstance : Nontrivial (⊤ : Subgroup P)) hn

theorem isQuasisimple_oddCoreQuotient_of_witness {G : Type*} [Group G] [Finite G] {J : Subgroup G}
    (hw : classicalInvolutionWitness J) (hns : ¬ Group.IsSolvable J) :
    CFSG.Open.IsQuasisimple (J ⧸ classicalInvolutionOddCore J) := by
  rcases hw with ⟨p, n, hp, hp2, hn, ⟨φ⟩⟩ | ⟨hqs, -, -⟩
  · have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn.ne'
    have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
    have h3 : 3 ≤ p ^ n := hp3.trans (Nat.le_self_pow hn.ne' p)
    by_cases h : Nat.card (GaloisField p n) = 3
    · exfalso
      apply hns
      have h24 : Nat.card SL(2, GaloisField p n) = 24 := by
        have := Fintype.ofFinite (GaloisField p n)
        rw [Matrix.card_SL_field 2, ← Nat.card_eq_fintype_card, h, Fin.prod_univ_two]
        norm_num
      have hsolv : Group.IsSolvable SL(2, GaloisField p n) :=
        CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)
      have h1 : Group.IsSolvable (J ⧸ classicalInvolutionOddCore J) :=
        Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have h2 : Group.IsSolvable (classicalInvolutionOddCore J) :=
        CFSG.FeitThompson.isSolvable_of_odd_natCard _ (OddCore.odd_card J)
      exact Group.isSolvable_of_subgroup_quotient (classicalInvolutionOddCore J)
    · exact Components.quasisimple_of_equiv φ (isQuasisimple_specialLinearGroup_two (by omega))
  · exact hqs

theorem exists_isTwoComponent_le {Y : Type*} [Group Y] [Finite Y] (M : Subgroup Y)
    (hM : IsSubnormal M ⊤) (hq : CFSG.Open.IsQuasisimple (M ⧸ componentClassificationOddCore M)) :
    ∃ L : Subgroup Y, L ≤ M ∧ TwoComponents.IsTwoComponent L ∧
      L.map (QuotientGroup.mk' (componentClassificationOddCore Y)) =
        M.map (QuotientGroup.mk' (componentClassificationOddCore Y)) := by
  set π := QuotientGroup.mk' (componentClassificationOddCore Y)
  obtain ⟨L, hLM, hmin⟩ := Finite.exists_le_minimal
    (p := fun L : Subgroup Y => L ≤ M ∧ IsSubnormal L ⊤ ∧ L.map π = M.map π)
    (a := M) ⟨le_rfl, hM, rfl⟩
  obtain ⟨hLM', hLsub, hLmap⟩ := hmin.prop
  refine ⟨L, hLM', ⟨hLsub, ?_, ?_⟩, hLmap⟩
  · rw [hLmap]
    exact (Components.quotient_component_iff M hM).mpr hq
  · intro smaller hle hsub hsmaller
    exact ((minimal_iff.mp hmin).2 ⟨hle.trans hLM', hsub, hsmaller.trans hLmap⟩ hle).symm

theorem twoResidual_le_subgroupOf_of_map_eq {Y : Type*} [Group Y] [Finite Y] {L M : Subgroup Y}
    (hLM : L ≤ M) (hL : IsSubnormal L ⊤) (hM : IsSubnormal M ⊤)
    (hmap : L.map (QuotientGroup.mk' (componentClassificationOddCore Y)) =
      M.map (QuotientGroup.mk' (componentClassificationOddCore Y))) :
    TwoResidual.subgroup M ≤ L.subgroupOf M := by
  let quotient := (QuotientGroup.mk' (componentClassificationOddCore Y)).domRestrict M
  let image := M.map (QuotientGroup.mk' (componentClassificationOddCore Y))
  let restriction : M →* image := quotient.codRestrict image
    fun element => Subgroup.mem_map_of_mem _ element.property
  have hsurjective : Function.Surjective restriction := by
    intro element
    obtain ⟨member, hmember, hvalue⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨member, hmember⟩, Subtype.ext hvalue⟩
  have hkernel : restriction.ker = componentClassificationOddCore M := by
    ext element
    change restriction element = 1 ↔ element ∈ componentClassificationOddCore M
    rw [← Components.oddCore_restriction_kernel M hM]
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hcovering : Function.Surjective (restriction.domRestrict (L.subgroupOf M)) := by
    intro element
    have hmem : element.val ∈ L.map (QuotientGroup.mk' (componentClassificationOddCore Y)) := by
      rw [hmap]
      exact element.property
    obtain ⟨member, hmember, hvalue⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨⟨member, hLM hmember⟩, hmember⟩, Subtype.ext hvalue⟩
  have hoddIndex := TwoResidual.odd_index_of_covering restriction hsurjective
    (by rw [hkernel]; exact OddCore.odd_card M) (L.subgroupOf M) hcovering
  have hlocalSubnormal : IsSubnormal (L.subgroupOf M) ⊤ :=
    Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain hL Subgroup.IsSubnormal.top).subgroupOf)
  exact TwoResidual.subnormal_contains_of_odd_index (L.subgroupOf M) hlocalSubnormal hoddIndex

theorem mem_of_orderOf_eq_two_of_map_eq {Y : Type*} [Group Y] [Finite Y] {L M : Subgroup Y}
    (hLM : L ≤ M) (hL : IsSubnormal L ⊤) (hM : IsSubnormal M ⊤)
    (hmap : L.map (QuotientGroup.mk' (componentClassificationOddCore Y)) =
      M.map (QuotientGroup.mk' (componentClassificationOddCore Y)))
    {z : Y} (hzM : z ∈ M) (hz : orderOf z = 2) : z ∈ L := by
  have hP : IsPGroup 2 (Subgroup.zpowers (⟨z, hzM⟩ : M)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz]; simp)
  have hle := TwoResidual.twoSubgroup_le _ hP
  exact twoResidual_le_subgroupOf_of_map_eq hLM hL hM hmap (hle (Subgroup.mem_zpowers _))

theorem nonempty_oddCoreQuotientEquiv_of_map_eq {Y : Type*} [Group Y] [Finite Y] {L M : Subgroup Y}
    (hL : IsSubnormal L ⊤) (hM : IsSubnormal M ⊤)
    (hmap : L.map (QuotientGroup.mk' (componentClassificationOddCore Y)) =
      M.map (QuotientGroup.mk' (componentClassificationOddCore Y))) :
    Nonempty ((L ⧸ componentClassificationOddCore L) ≃* (M ⧸ componentClassificationOddCore M)) :=
  ⟨(Components.oddCore_image_equiv L hL).trans
    ((MulEquiv.subgroupCongr hmap).trans (Components.oddCore_image_equiv M hM).symm)⟩

end CFSG.ClassicalInvolution
