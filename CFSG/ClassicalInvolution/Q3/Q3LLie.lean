module

public import CFSG.ClassicalInvolution.Q3.OddCentralizerModels
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSimple

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification
open scoped MatrixGroups

theorem CompData.range_isQuasisimple_or_isSolvable (hM : M11Facts) {c : CompData} (hc : c.Valid)
    {P : Type} [Group P] (f : c.G →* P) (hker : f.ker ≤ Subgroup.center c.G) :
    CFSG.Open.IsQuasisimple f.range ∨ Group.IsSolvable f.range := by
  rcases hc with ⟨t, n, hfund, hadm, rfl⟩ | rfl | rfl
  · left
    have hK := ModelFacts.isQuasisimple_modelUniv t n 3 1 Nat.prime_three hfund hadm
    exact isQuasisimple_of_centralQuotient hK f.rangeRestrict f.rangeRestrict_surjective
      ((MonoidHom.ker_rangeRestrict f).le.trans hker)
  · right
    have := isSolvable_sl2Three
    exact Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  · left
    exact isQuasisimple_of_centralQuotient (isQuasisimple_m11 hM) f.rangeRestrict
      f.rangeRestrict_surjective ((MonoidHom.ker_rangeRestrict f).le.trans hker)

theorem LieSystemData3.component_dichotomy (hM : M11Facts) {ι : Type} {P : Type} [Group P]
    [Finite P] {Φ : Set (Subgroup P)} (D : LieSystemData3 ι P Φ) {T : Subgroup P}
    (hT : IsComponentOf T ⊤) {L : Subgroup P} (i₀ : ι) (hL : L ≤ (D.hom i₀).range) :
    L ≤ T ∨ ⁅L, T⁆ = ⊥ := by
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ (D.hom i).range, ∀ y ∈ (D.hom j).range, x * y = y * x := by
    rintro i j hij _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i j hij a b
  have hnorm : ∀ i, ((D.hom i).range).Normal := by
    intro i
    refine ⟨fun n hn g => ?_⟩
    have hle : (⨆ j, (D.hom j).range) ≤
        Subgroup.normalizer (((D.hom i).range : Subgroup P) : Set P) := by
      refine iSup_le fun j => ?_
      by_cases hji : j = i
      · subst hji
        exact Subgroup.le_normalizer
      · intro y hy
        apply Subgroup.centralizer_le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact hcomm i j (Ne.symm hji) x hx y hy
    have hg : g ∈ Subgroup.normalizer (((D.hom i).range : Subgroup P) : Set P) :=
      hle (by rw [D.generate]; exact Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  by_cases hTc : ∀ i, ⁅T, (D.hom i).range⁆ = ⊥
  · exfalso
    have hTz : ∀ t ∈ T, ∀ g : P, t * g = g * t := by
      intro t ht g
      have hg : g ∈ ⨆ j, (D.hom j).range := by rw [D.generate]; exact Subgroup.mem_top g
      refine Subgroup.iSup_induction (fun j => (D.hom j).range) (C := fun g => t * g = g * t)
        hg ?_ ?_ ?_
      · intro j y hy
        have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hTc j)) ht
        exact ((Subgroup.mem_centralizer_iff.mp hc) y hy).symm
      · simp
      · intro x y hx hy
        calc t * (x * y) = x * t * y := by rw [← mul_assoc, hx, mul_assoc]
          _ = x * y * t := by rw [mul_assoc, hy, ← mul_assoc]
    have hcen : Subgroup.center T = ⊤ := by
      rw [eq_top_iff]
      intro a _
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hTz (b : P) b.2 (a : P))
    have hone : ∀ x : T ⧸ Subgroup.center T, x = 1 := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H a => exact (QuotientGroup.eq_one_iff a).mpr (hcen ▸ Subgroup.mem_top a)
    obtain ⟨x, y, hxy⟩ := @exists_pair_ne _ hT.2.2.2.toNontrivial
    exact hxy ((hone x).trans (hone y).symm)
  · push Not at hTc
    obtain ⟨i, hi⟩ := hTc
    have hsub : IsSubnormal (D.hom i).range ⊤ := by
      have := hnorm i
      exact isSubnormal_of_normal_subgroupOf le_top inferInstance
    rcases CompData.range_isQuasisimple_or_isSolvable hM (D.valid i) (D.hom i)
        (D.ker_le_center i) with hq | hs
    · have hHc : IsComponentOf (D.hom i).range ⊤ := ⟨le_top, hsub, hq⟩
      by_cases hTH : T = (D.hom i).range
      · by_cases hii : i = i₀
        · left
          rw [hTH, hii]
          exact hL
        · right
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro l hl
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          exact hcomm i i₀ hii t (hTH ▸ ht) l (hL hl)
      · exact absurd (LocalComponents.commute_of_ne T _ hT hHc hTH) hi
    · exfalso
      apply hi
      exact LocalComponents.commutes_with_solvable_subnormal T (D.hom i).range hT hsub

end CFSG.ClassicalInvolution.Q3
