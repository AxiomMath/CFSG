module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Props
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2A6
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqEvenClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqEvenExc

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)


theorem card_statedSp_two_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    Nat.card (StatedSp 2 k) = 720 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hk]
  decide

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} [S.Normal] {t : G}

theorem even_inner_false (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    (ht : t ∈ S) (heven : EvenLieType ↥S) : False := by
  let z : ↥S := ⟨t, ht⟩
  have hz : orderOf z = 2 := (Subgroup.orderOf_mk t ht).trans h.ord
  have hσeq : (MulAut.conjNormal t : MulAut ↥S) = MulAut.conj z := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    simp [MulAut.conjNormal_apply, MulAut.conj_apply, z]
  have hfix : fixedSubgroup (MulAut.conjNormal t : MulAut ↥S) = centralizer ({z} : Set ↥S) := by
    rw [hσeq]
    exact CFSG.SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf z
  obtain ⟨e⟩ := commutator_fixed_equiv h ζ
  obtain ⟨c⟩ := commutator_equiv_of_mulEquiv (MulEquiv.subgroupCongr hfix)
  haveI : (commutator ↥(centralizer ({z} : Set ↥S))).Normal := Subgroup.commutator_normal ⊤ ⊤
  exact CFSG.ComponentClassification.CatLeaf.involutionCentralizersComponentFree_of_evenLieType
    heven z hz _ (isComponent_of_alt6 _ (c.symm.trans e))

theorem even_outer_false (hO : LieOrderFormulasInput)
    (kL4 : HarrisKleinFree .PSL 4 2 1) (kL5 : HarrisKleinFree .PSL 5 2 1)
    (kU4 : HarrisKleinFree .PSU 4 2 1) (kU5 : HarrisKleinFree .PSU 5 2 1)
    (kS4 : HarrisKleinFree .PSp 2 2 2) (kS8 : HarrisKleinFree .PSp 2 2 3)
    (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    (ht : t ∉ S) (heven : EvenLieType ↥S) : False := by
  have hσ : orderOf (MulAut.conjNormal t : MulAut ↥S) = 2 := orderOf_conjNormal h.cent h.ord
  have hout : (MulAut.conjNormal t : MulAut ↥S) ∉ (MulAut.conj : ↥S →* MulAut ↥S).range :=
    fun hin => ht ((conjNormal_mem_range_iff h.cent t).1 hin)
  obtain ⟨hC, hC'⟩ := harris_fixed_data h ζ
  obtain ⟨D, -, hDhyp⟩ := harris_a6Hyp h ζ
  obtain ⟨tag, n, f, hadm, hm⟩ := heven
  have hklein : ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
      Nonempty (↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) ≃* StatedSp 2 k) →
        OuterKlein (MulAut.conjNormal t : MulAut ↥S) := by
    intro k _ _ hk ⟨Φ⟩
    exact outerKlein_of_card_le h ζ (by rw [Nat.card_congr Φ.toEquiv, card_statedSp_two_two hk])
  cases tag
  · refine a6sq_even_PSL_core hO hadm hm hσ hout hC hC' fun hn45 he k _ _ hk hΦ => ?_
    have hKl := hklein k hk hΦ
    subst he
    rcases hn45 with rfl | rfl
    · exact kL4 ↥S hm _ hσ D hDhyp hKl
    · exact kL5 ↥S hm _ hσ D hDhyp hKl
  · refine a6sq_even_PSU_core hO hadm hm hσ hout hC hC' fun hn45 he k _ _ hk hΦ => ?_
    have hKl := hklein k hk hΦ
    subst he
    rcases hn45 with rfl | rfl
    · exact kU4 ↥S hm _ hσ D hDhyp hKl
    · exact kU5 ↥S hm _ hσ D hDhyp hKl
  · refine a6sq_even_PSp_core hO hadm hm hσ hout hC hC' fun hn2 he k _ _ hk hΦ => ?_
    have hKl := hklein k hk hΦ
    subst hn2
    rcases he with rfl | rfl
    · exact kS4 ↥S hm _ hσ D hDhyp hKl
    · exact kS8 ↥S hm _ hσ D hDhyp hKl
  · exact (hadm.2.2.2 rfl).elim
  · exact a6sq_even_Omega_core hO (Or.inl rfl) hadm hm hσ hout hC hC'
  · exact a6sq_even_Omega_core hO (Or.inr rfl) hadm hm hσ hout hC hC'
  · exact a6sq_even_G2 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_F4 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_E6 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_E7_E8 hO (Or.inl rfl) hadm hm hσ hout hC hC'
  · exact a6sq_even_E7_E8 hO (Or.inr rfl) hadm hm hσ hout hC hC'
  · exact a6sq_even_twistedE6 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_trialityD4 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_twistedB2 hadm hm hσ hout
  · exact absurd hadm.2.2.2.1 (by norm_num)
  · exact a6sq_even_twistedF4 hadm hm hσ hout
  · exact a6sq_even_Tits hadm hm hσ hout

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
