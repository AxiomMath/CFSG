module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitBasic

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit

open scoped Pointwise
open CatalogueBOrthogonalSmallFamilyOrbit

universe u

variable {G : Type u} [Group G]

theorem automorphism_family_fixed_of_borel (B D : Subgroup G)
    (hBD : B ≤ D) (hD : IsCoatom D)
    (hB : ∀ alpha : MulAut G, ∃ g : G,
      B.map alpha.toMonoidHom = B.map (MulAut.conj g).toMonoidHom)
    (C : Set (Subgroup G))
    (hC : ∀ M : Subgroup G, IsCoatom M → B ≤ M → M ∈ C)
    (hIndex : ∀ M ∈ C, M.index = D.index → M = D) (alpha : MulAut G) :
    alpha • conjugacyFamily D = conjugacyFamily D := by
  obtain ⟨g, hg⟩ := hB alpha
  have hM : D.map (borelCorrection alpha g).toMonoidHom = D :=
    hIndex _
      (hC _ (borelCorrection_isCoatom D hD alpha g)
        (borelCorrection_overgroup B D hBD alpha g hg))
      (borelCorrection_index D alpha g)
  rw [← borelCorrection_family D alpha g, hM]

theorem familyStabilizer_eq_top_of_borel (B D : Subgroup G)
    (hBD : B ≤ D) (hD : IsCoatom D)
    (hB : ∀ alpha : MulAut G, ∃ g : G,
      B.map alpha.toMonoidHom = B.map (MulAut.conj g).toMonoidHom)
    (C : Set (Subgroup G))
    (hC : ∀ M : Subgroup G, IsCoatom M → B ≤ M → M ∈ C)
    (hIndex : ∀ M ∈ C, M.index = D.index → M = D) :
    familyStabilizer D = ⊤ := by
  apply le_antisymm le_top
  intro alpha _
  exact automorphism_family_fixed_of_borel B D hBD hD hB C hC hIndex alpha

theorem familyOrbit_eq_singleton_of_borel (B D : Subgroup G)
    (hBD : B ≤ D) (hD : IsCoatom D)
    (hB : ∀ alpha : MulAut G, ∃ g : G,
      B.map alpha.toMonoidHom = B.map (MulAut.conj g).toMonoidHom)
    (C : Set (Subgroup G))
    (hC : ∀ M : Subgroup G, IsCoatom M → B ≤ M → M ∈ C)
    (hIndex : ∀ M ∈ C, M.index = D.index → M = D) :
    MulAction.orbit (MulAut G) (conjugacyFamily D) = {conjugacyFamily D} := by
  ext F
  constructor
  · intro hF
    obtain ⟨alpha, rfl⟩ := MulAction.mem_orbit_iff.mp hF
    exact Set.mem_singleton_iff.mpr
      (automorphism_family_fixed_of_borel B D hBD hD hB C hC hIndex alpha)
  · intro hF
    rw [Set.mem_singleton_iff.mp hF]
    exact MulAction.mem_orbit_self _

theorem automorphism_family_three_of_borel (B D X Xstar : Subgroup G)
    (hBD : B ≤ D) (hD : IsCoatom D)
    (hB : ∀ alpha : MulAut G, ∃ g : G,
      B.map alpha.toMonoidHom = B.map (MulAut.conj g).toMonoidHom)
    (C : Set (Subgroup G))
    (hC : ∀ M : Subgroup G, IsCoatom M → B ≤ M → M ∈ C)
    (hIndex : ∀ M ∈ C, M.index = D.index → M = D ∨ M = X ∨ M = Xstar)
    (alpha : MulAut G) :
    alpha • conjugacyFamily D ∈
      ({conjugacyFamily D, conjugacyFamily X, conjugacyFamily Xstar} :
        Set (Set (Subgroup G))) := by
  obtain ⟨g, hg⟩ := hB alpha
  have hM := hIndex (D.map (borelCorrection alpha g).toMonoidHom)
    (hC _ (borelCorrection_isCoatom D hD alpha g)
      (borelCorrection_overgroup B D hBD alpha g hg))
    (borelCorrection_index D alpha g)
  rw [← borelCorrection_family D alpha g]
  rcases hM with hM | hM | hM <;> rw [hM] <;> simp

theorem familyOrbit_subset_three_of_borel (B D X Xstar : Subgroup G)
    (hBD : B ≤ D) (hD : IsCoatom D)
    (hB : ∀ alpha : MulAut G, ∃ g : G,
      B.map alpha.toMonoidHom = B.map (MulAut.conj g).toMonoidHom)
    (C : Set (Subgroup G))
    (hC : ∀ M : Subgroup G, IsCoatom M → B ≤ M → M ∈ C)
    (hIndex : ∀ M ∈ C, M.index = D.index → M = D ∨ M = X ∨ M = Xstar) :
    MulAction.orbit (MulAut G) (conjugacyFamily D) ⊆
      {conjugacyFamily D, conjugacyFamily X, conjugacyFamily Xstar} := by
  intro F hF
  obtain ⟨alpha, rfl⟩ := MulAction.mem_orbit_iff.mp hF
  exact automorphism_family_three_of_borel B D X Xstar hBD hD hB C hC hIndex alpha

theorem three_conjugacy_families_card_le (D X Xstar : Subgroup G) :
    ({conjugacyFamily D, conjugacyFamily X, conjugacyFamily Xstar} :
      Set (Set (Subgroup G))).ncard ≤ 3 := by
  have h1 := Set.ncard_insert_le (conjugacyFamily D)
    ({conjugacyFamily X, conjugacyFamily Xstar} : Set (Set (Subgroup G)))
  have h2 := Set.ncard_insert_le (conjugacyFamily X)
    ({conjugacyFamily Xstar} : Set (Set (Subgroup G)))
  rw [Set.ncard_singleton] at h2
  omega

theorem familyOrbit_card_le_three_of_subset (D X Xstar : Subgroup G)
    (hO : MulAction.orbit (MulAut G) (conjugacyFamily D) ⊆
      {conjugacyFamily D, conjugacyFamily X, conjugacyFamily Xstar}) :
    Nat.card (FamilyOrbit D) ≤ 3 := by
  change (MulAction.orbit (MulAut G) (conjugacyFamily D)).ncard ≤ 3
  exact (Set.ncard_le_ncard hO (by simp)).trans (three_conjugacy_families_card_le D X Xstar)

theorem familyOrbit_card_le_three_of_borel (B D X Xstar : Subgroup G)
    (hBD : B ≤ D) (hD : IsCoatom D)
    (hB : ∀ alpha : MulAut G, ∃ g : G,
      B.map alpha.toMonoidHom = B.map (MulAut.conj g).toMonoidHom)
    (C : Set (Subgroup G))
    (hC : ∀ M : Subgroup G, IsCoatom M → B ≤ M → M ∈ C)
    (hIndex : ∀ M ∈ C, M.index = D.index → M = D ∨ M = X ∨ M = Xstar) :
    Nat.card (FamilyOrbit D) ≤ 3 :=
  familyOrbit_card_le_three_of_subset D X Xstar
    (familyOrbit_subset_three_of_borel B D X Xstar hBD hD hB C hC hIndex)

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
