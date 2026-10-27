module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcBQBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.BQ

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity CFSG.LieType.TitsSimplicity.Levi
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

theorem posUnipotent_le_radicalOff_sup_levi (hdiv : D.divisible = ∅)
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (I : Finset (Fin D.rank)) :
    posUnipotent D ≤ radicalOff D I ⊔ levi D.rootGroup I := by
  refine iSup₂_le fun γ hγ => ?_
  by_cases h : ∃ j ∉ I, γ j ≠ 0
  · obtain ⟨j, hj, hγj⟩ := h
    have hpos : 0 < γ j := lt_of_le_of_ne (coord_nonneg_of_ht_pos hγ.1 hγ.2 j) (Ne.symm hγj)
    exact (rootGroup_le_radical hγ.1 hpos).trans (le_sup_of_le_left
      (le_iSup₂_of_le (f := fun j (_ : j ∈ ((I : Set (Fin D.rank))ᶜ)) => radical D j) j
        (by simpa using hj) le_rfl))
  · push Not at h
    refine le_sup_of_le_right ((rootGroup_le_leviC_of_support (e := I.orderEmbOfFin rfl) hdiv
      hct hγ.1 fun k hk => h k fun hkI => hk ?_).trans (leviC_orderEmbOfFin I).le)
    rw [Finset.range_orderEmbOfFin]
    exact hkI

theorem torus_le_normalizer_levi (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (I : Finset (Fin D.rank)) :
    (⨆ i, H i) ≤ normalizer (levi D.rootGroup I : Set K) := by
  have hα : ∀ j : Fin D.rank, (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := fun j =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  refine iSup_le fun k => CFSG.LieType.Steinberg.le_normalizer_iSup fun j =>
    CFSG.LieType.Steinberg.le_normalizer_iSup fun _ => CFSG.LieType.Steinberg.le_normalizer_sup
      (fun _ hh => mem_normalizer_rootGroup hct hh (hα j))
      (fun _ hh => mem_normalizer_rootGroup hct hh
        ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ (hα j)))

theorem torus_sup_levi_le_normalizer_radicalOff (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (I : Finset (Fin D.rank)) :
    (⨆ i, H i) ⊔ levi D.rootGroup I ≤ normalizer (radicalOff D I : Set K) := by
  refine CFSG.LieType.Steinberg.le_normalizer_iSup fun j =>
    CFSG.LieType.Steinberg.le_normalizer_iSup fun hj => sup_le ?_ ?_
  · exact iSup_le_borel.trans (borel_le_normalizer_radical hct hext j)
  · refine iSup₂_le fun i hi => rankOne_le_normalizer_radical hext ?_
    rintro rfl
    exact (Set.mem_compl_iff _ _).1 hj (Finset.mem_coe.2 hi)

theorem exists_levi_decomposition (hdiv : D.divisible = ∅)
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    {A : Subgroup K} (hBA : borel D H ≤ A) :
    ∃ I : Finset (Fin D.rank), (∀ i, i ∈ I ↔ D.rootGroup (-Pi.single i 1) ≤ A) ∧
      levi D.rootGroup I ≤ A ∧ A ≤ radicalOff D I ⊔ ((⨆ i, H i) ⊔ levi D.rootGroup I) := by
  classical
  set I : Finset (Fin D.rank) := Finset.univ.filter fun i => D.rootGroup (-Pi.single i 1) ≤ A
    with hIdef
  have hI : ∀ i, i ∈ I ↔ D.rootGroup (-Pi.single i 1) ≤ A := fun i => by simp [hIdef]
  refine ⟨I, hI, iSup₂_le fun i hi => sup_le ?_ ((hI i).1 hi), ?_⟩
  · exact (rootGroup_le_borel ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
      (ht_single_pos i)).trans hBA
  · refine (eq_borel_sup_rankOne hct hext hBA).le.trans (sup_le ?_ (iSup₂_le fun i hi => ?_))
    · exact sup_le (le_sup_left.trans le_sup_right)
        ((posUnipotent_le_radicalOff_sup_levi hdiv hct I).trans (sup_le_sup_left le_sup_right _))
    · have hiI : i ∈ I := (hI i).2 (le_sup_right.trans (rankOne_le_of_mem_negIndices hBA hi))
      exact (rankOne_le_levi D.rootGroup hiI).trans (le_sup_right.trans le_sup_right)

theorem card_dvd_of_le_radicalOff_sup [Finite K]
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (I : Finset (Fin D.rank)) {A : Subgroup K}
    (hA : A ≤ radicalOff D I ⊔ ((⨆ i, H i) ⊔ levi D.rootGroup I)) :
    Nat.card A ∣ Nat.card (radicalOff D I) *
      (Nat.card (⨆ i, H i : Subgroup K) * Nat.card (levi D.rootGroup I)) := by
  have hA' : A ≤ ((⨆ i, H i) ⊔ levi D.rootGroup I) ⊔ radicalOff D I :=
    hA.trans (sup_comm _ _).le
  calc Nat.card A ∣ Nat.card ↥(((⨆ i, H i) ⊔ levi D.rootGroup I) ⊔ radicalOff D I) :=
        Subgroup.card_dvd_of_le hA'
    _ ∣ Nat.card ↥((⨆ i, H i) ⊔ levi D.rootGroup I) * Nat.card (radicalOff D I) :=
        card_sup_dvd_mul _ _ (torus_sup_levi_le_normalizer_radicalOff hct hext I)
    _ ∣ (Nat.card (⨆ i, H i : Subgroup K) * Nat.card (levi D.rootGroup I)) *
        Nat.card (radicalOff D I) :=
        mul_dvd_mul_right (card_sup_dvd_mul _ _ (torus_le_normalizer_levi hct I)) _
    _ = _ := mul_comm _ _

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.BQ
