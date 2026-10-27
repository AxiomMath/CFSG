module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUAlmostSimple
public import CFSG.Sporadic.SmallOddCore.J2

public section

namespace CFSG.ComponentClassification.CatalogueU

open CFSG.Blueprint Subgroup

@[expose] def SporadicOddCoreFree (s : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup (CFSG.generalizedFitting X) →
    (∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) →
    Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.Carrier s) →
    ∀ t : X, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set X)) = ⊥

@[expose] def HeldUnbalancedOutcome : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    Nonempty (GeneralizedFitting.subgroup X ≃* NativeSporadic.He) →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

theorem sporadicNonJ1Check_of_cases
    (h : ∀ s : TauCeti.SporadicName, s ≠ .J1 → s ≠ .He → SporadicOddCoreFree s)
    (hHe : HeldUnbalancedOutcome) : SporadicNonJ1Check := by
  intro X _ _ hsimple hnonab ⟨s, ⟨e⟩⟩ hJ1 ⟨z, hz2, hcore⟩
  have hF : CFSG.generalizedFitting X = GeneralizedFitting.subgroup X :=
    CFSG.generalizedFitting_eq_componentClassification X
  by_cases hsJ1 : s = .J1
  · subst hsJ1
    exact absurd ⟨e⟩ hJ1
  by_cases hsHe : s = .He
  · subst hsHe
    exact hHe X hsimple hnonab ⟨e⟩ ⟨z, hz2, hcore⟩
  exact absurd (h s hsJ1 hsHe X (hF ▸ hsimple) (hF ▸ hnonab)
    ⟨(MulEquiv.subgroupCongr hF).trans e⟩ z hz2) hcore

theorem sporadicOddCoreFree_M11 : SporadicOddCoreFree .M11 :=
  fun _ _ _ hF hnab hJ t ht => catalog_mathieu_almost_simple_odd_core_vanishing hF hnab (.inl hJ)
    t ht

theorem sporadicOddCoreFree_M12 : SporadicOddCoreFree .M12 :=
  fun _ _ _ hF hnab hJ t ht => catalog_mathieu_almost_simple_odd_core_vanishing hF hnab
    (.inr (.inl hJ)) t ht

theorem sporadicOddCoreFree_M22 : SporadicOddCoreFree .M22 :=
  fun _ _ _ hF hnab hJ t ht => catalog_mathieu_almost_simple_odd_core_vanishing hF hnab
    (.inr (.inr (.inl hJ))) t ht

theorem sporadicOddCoreFree_M23 : SporadicOddCoreFree .M23 :=
  fun _ _ _ hF hnab hJ t ht => catalog_mathieu_almost_simple_odd_core_vanishing hF hnab
    (.inr (.inr (.inr (.inl hJ)))) t ht

theorem sporadicOddCoreFree_M24 : SporadicOddCoreFree .M24 :=
  fun _ _ _ hF hnab hJ t ht => catalog_mathieu_almost_simple_odd_core_vanishing hF hnab
    (.inr (.inr (.inr (.inr hJ)))) t ht

theorem sporadicOddCoreFree_J2 : SporadicOddCoreFree .J2 :=
  fun _ _ _ hF _ hJ t ht =>
    Sporadic.SmallOddCore.ctuc_j2_generalized_fitting_involution_centralizer_odd_core_trivial hF
      hJ t ht

theorem sporadicNonJ1Check_of_remaining
    (hJ3 : SporadicOddCoreFree .J3) (hJ4 : SporadicOddCoreFree .J4)
    (hCo1 : SporadicOddCoreFree .Co1) (hCo2 : SporadicOddCoreFree .Co2)
    (hCo3 : SporadicOddCoreFree .Co3) (hFi22 : SporadicOddCoreFree .Fi22)
    (hFi23 : SporadicOddCoreFree .Fi23) (hFi24 : SporadicOddCoreFree .Fi24Prime)
    (hHS : SporadicOddCoreFree .HS) (hMcL : SporadicOddCoreFree .McL)
    (hRu : SporadicOddCoreFree .Ru) (hSuz : SporadicOddCoreFree .Suz)
    (hON : SporadicOddCoreFree .ONan) (hHN : SporadicOddCoreFree .HN)
    (hLy : SporadicOddCoreFree .Ly) (hTh : SporadicOddCoreFree .Th)
    (hB : SporadicOddCoreFree .B) (hM : SporadicOddCoreFree .M)
    (hHe : HeldUnbalancedOutcome) : SporadicNonJ1Check := by
  refine sporadicNonJ1Check_of_cases (fun s hs1 hs2 => ?_) hHe
  have := sporadicOddCoreFree_M11
  have := sporadicOddCoreFree_M12
  have := sporadicOddCoreFree_M22
  have := sporadicOddCoreFree_M23
  have := sporadicOddCoreFree_M24
  have := sporadicOddCoreFree_J2
  cases s <;> first | assumption | exact absurd rfl hs1 | exact absurd rfl hs2

end CFSG.ComponentClassification.CatalogueU
