module

public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZ

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

theorem D1Extremal.of_le {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1Extremal p P M H R) {H' : Subgroup G}
    (hH' : GLBIsMaxTwoLocal H') (hRH' : R ≤ H') (hH'M : ¬ H' ≤ M) : D1Extremal p P M H' R := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨T, hT⟩ := (h.isPGroup.comap_subtype (K := H')).exists_le_sylow
  have hRT : R ≤ (T : Subgroup H').map H'.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRH']
    exact Subgroup.map_mono hT
  have hT2 : IsPGroup p ((T : Subgroup H').map H'.subtype) := T.isPGroup'.map _
  have hNR : (T : Subgroup H').map H'.subtype ⊓ Subgroup.normalizer (R : Set G) ≤ R := by
    have hcard := h.extremal H' hH'.1 hH'M
      (h.three_le_pRank.trans
        (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p h.prime (le_inf hRH' h.le_M)))
      _ (le_inf (inf_le_left.trans (Subgroup.map_subtype_le _))
        (inf_le_right.trans h.normalizer_le)) (hT2.to_le inf_le_left)
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hRT Subgroup.le_normalizer) hcard).ge
  have hTR : (T : Subgroup H').map H'.subtype = R := by
    by_contra hne
    obtain ⟨x, hxT, hxR, hxN⟩ :=
      exists_mem_normalizer_not_mem_of_lt_of_isPGroup hT2 (lt_of_le_of_ne hRT (Ne.symm hne))
    exact hxR (hNR ⟨hxT, hxN⟩)
  exact
    { h.toD1Escape with
      maxTwoLocal_H := hH'
      le_H := hRH'
      isSylow := ⟨T, hTR⟩
      not_le := hH'M
      extremal := h.extremal
      extremal3 := h.extremal3 }

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R X : Subgroup G}

theorem D1PhaseThree.pCoreOf_two_primeCore_ne_bot (h : D1PhaseThree p P M H R) (hXR : X ≤ R)
    (hX1 : X ≠ ⊥) : pCoreOf 2 (GLBPrimeCore p (nclIn H X)) ≠ ⊥ :=
  h.toPair.pCoreOf_two_primeCore_ne_bot hXR hX1

structure D1JConfig (p : ℕ) (P : Sylow p G) (M H R X : Subgroup G) : Prop where
  phaseThree : D1PhaseThree p P M H R
  le_R : X ≤ R
  ne_bot : X ≠ ⊥
  normal_sup : ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal
  commutator_le : ⁅GLBPrimeCore p H, X⁆ ≤ pCoreOf 2 M
  centralizer_le : (H ⊓ M) ⊓ Subgroup.centralizer (X : Set G) ≤ X ⊔ GLBPrimeCore p H

@[expose] def D1JCompetitors (p : ℕ) (P : Sylow p G) (M R X : Subgroup G) : Prop :=
  ∀ H : Subgroup G, D1JConfig p P M H R X → ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' →
    nclIn H X ≤ H' → R ≤ H' → D1JConfig p P M H' R X ∧ nclIn H X ≤ nclIn H' X

namespace D1JConfig

theorem commutator_nclIn_le (h : D1JConfig p P M H R X) :
    ⁅GLBPrimeCore p H, nclIn H X⁆ ≤ pCoreOf 2 H :=
  CFSG.AGLEmbedding.commutator_nclIn_le (h.le_R.trans h.phaseThree.le_H)
    (le_normalizer_glbPrimeCore p H) (localGroup_le_normalizer_pCoreOf 2 H)
    (h.commutator_le.trans (h.phaseThree.twoCore_M_le h.phaseThree.twoCore_inf))

theorem exists_max (h : D1JConfig p P M H R X) :
    ∃ H₀ : Subgroup G, D1JConfig p P M H₀ R X ∧ ∀ H' : Subgroup G, D1JConfig p P M H' R X →
      Nat.card (nclIn H' X) ≤ Nat.card (nclIn H₀ X) :=
  Set.exists_max_image {H' : Subgroup G | D1JConfig p P M H' R X}
    (fun H' => Nat.card (nclIn H' X)) (Set.toFinite _) ⟨H, h⟩

theorem eq_of_maxTwoLocal (h : D1JConfig p P M H R X) (hcomp : D1JCompetitors p P M R X)
    (hmax : ∀ H' : Subgroup G, D1JConfig p P M H' R X →
      Nat.card (nclIn H' X) ≤ Nat.card (nclIn H X))
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H X ≤ H') (hRH' : R ≤ H') :
    H' = H := by
  obtain ⟨h', hJJ'⟩ := hcomp H h H' hH' hJH' hRH'
  have heq : nclIn H X = nclIn H' X := Subgroup.eq_of_le_of_card_ge hJJ' (hmax H' h')
  have hJn' : ((nclIn H X).subgroupOf H').Normal := heq ▸ nclIn_normal H' X
  have hAJ : pCoreOf 2 (GLBPrimeCore p (nclIn H X)) ≤ nclIn H X :=
    (pCoreOf_le 2 _).trans (glbPrimeCore_le p _)
  have hNA : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p (nclIn H X)) : Set G) = H :=
    maxTwoLocal_normalizer_eq_of_normal h.phaseThree.maxTwoLocal_H
      (h.phaseThree.pCoreOf_two_primeCore_ne_bot h.le_R h.ne_bot) (pCoreOf_isPGroup 2 _)
      (hAJ.trans (nclIn_le_self H X))
      (normal_pCoreOf_two_glbPrimeCore p (nclIn_le_self H X) (nclIn_normal H X))
  have hH'H : H' ≤ H := hNA ▸ (Subgroup.normal_subgroupOf_iff_le_normalizer (hAJ.trans hJH')).mp
    (normal_pCoreOf_two_glbPrimeCore p hJH' hJn')
  exact (hH'.2 H h.phaseThree.maxTwoLocal_H.1 hH'H).symm

end D1JConfig

theorem false_of_d1JConfig (hcomp : D1JCompetitors p P M R X) (h : D1JConfig p P M H R X)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : False := by
  obtain ⟨H₀, h₀, hmax⟩ := h.exists_max
  exact h₀.phaseThree.false_of_unique_over h₀.le_R h₀.normal_sup h₀.commutator_le
    h₀.centralizer_le h₀.commutator_nclIn_le
    (fun _ hH' hJH' hRH' => h₀.eq_of_maxTwoLocal hcomp hmax hH' hJH' hRH') hCGT hD2

end CFSG.AGLEmbedding
