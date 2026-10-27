module

public import CFSG.ClassicalInvolution.Q3.LieDecomposition
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups commutatorElement


section Abstract

variable {X Yb : Type} [Group X] [Group Yb] {Φ : Set (Subgroup Yb)} {ι : Type}

noncomputable def lieDecomposition3_of_lieSystemData3' (h0 : ModelClauseZero) (hM : M11Facts)
    (D : LieSystemData3 ι Yb Φ) (θ : Yb →* X) (hθ : Function.Injective θ)
    (hnc : ∀ L ∈ Φ, ¬ L ≤ Subgroup.center Yb) :
    LieDecomposition3 (Subgroup.map θ '' Φ) θ.range := by
  let Q : ι → Subgroup X := fun i => (θ.comp (D.hom i)).range
  have hQmap : ∀ i, Q i = (D.hom i).range.map θ := fun i => MonoidHom.range_comp θ (D.hom i)
  have hker : ∀ i, (θ.comp (D.hom i)).ker ≤ Subgroup.center _ := fun i x hx => by
    apply D.ker_le_center i
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hθ (by simpa using hx)
  have hmem : ∀ L ∈ Φ, ∃ j R, R ∈ (D.kind j).fund ∧ L = R.map (D.hom j) :=
    fun L hL => D.fundamental L hL
  have hnt : ∀ i, ∃ x, (θ.comp (D.hom i)) x ≠ 1 := by
    intro i
    obtain ⟨R, -, hmeet⟩ := D.meets i
    have h24 := D.card_eq _ hmeet
    obtain ⟨m, hm, hm1⟩ : ∃ m ∈ R.map (D.hom i), m ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : R.map (D.hom i) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
      rw [hbot, Subgroup.card_bot] at h24
      omega
    obtain ⟨r, -, rfl⟩ := hm
    exact ⟨r, fun h => hm1 (hθ (by simpa using h))⟩
  refine { ι := ι, Q := Q, commute := ?_, iSup_eq := ?_, exists_le := ?_, kind := ?_ }
  · rintro i j hij _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, D.commute i j hij a b]
  · show ⨆ i, Q i = θ.range
    simp_rw [hQmap]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
  · rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, -, rfl⟩ := D.fundamental L hL
    exact ⟨i, (hQmap i).symm ▸ Subgroup.map_mono (Subgroup.map_le_range _ _)⟩
  · intro i
    obtain ⟨t, n, ht, hadm, hc⟩ | hc | hc := D.valid i
    · exact Or.inr (Or.inl (range_model3 h0 ht hadm hc (θ.comp (D.hom i)) (hker i) (hnt i)))
    · left
      have hfund : ∀ R ∈ (D.kind i).fund, R = ⊤ := fund_eq_top_of_sl23 hc
      refine ⟨?_, ?_, isSolvable_range_of_sl23 hc (θ.comp (D.hom i))⟩
      · obtain ⟨R, hR, hmeet⟩ := D.meets i
        rw [hfund R hR, Subgroup.map_top] at hmeet
        exact ⟨(D.hom i).range.map θ, ⟨(D.hom i).range, hmeet, rfl⟩, (hQmap i).symm⟩
      · rintro _ ⟨L₁, hL₁, rfl⟩ hle
        rw [hQmap i] at hle ⊢
        have hle' : L₁ ≤ (D.hom i).range := (Subgroup.map_le_map_iff_of_injective hθ).mp hle
        obtain ⟨j, R', hR', hL₁eq⟩ := hmem L₁ hL₁
        by_cases hji : j = i
        · subst hji
          rw [hfund R' hR', Subgroup.map_top] at hL₁eq
          rw [hL₁eq]
        · refine absurd ?_ (hnc L₁ hL₁)
          have hL₁j : L₁ ≤ (D.hom j).range := hL₁eq ▸ Subgroup.map_le_range _ _
          intro x hx
          have hxi := hle' hx
          have hxj := hL₁j hx
          rw [Subgroup.mem_center_iff]
          intro g
          have hg : g ∈ (⨆ k, (D.hom k).range : Subgroup Yb) := by rw [D.generate]; trivial
          have hcen : ∀ k, (D.hom k).range ≤ Subgroup.centralizer ({x} : Set Yb) := by
            rintro k _ ⟨y, rfl⟩
            rw [Subgroup.mem_centralizer_singleton_iff]
            by_cases hki : k = i
            · subst hki
              obtain ⟨z, rfl⟩ := hxj
              exact (D.commute j k hji z y).symm
            · obtain ⟨z, rfl⟩ := hxi
              exact (D.commute i k (Ne.symm hki) z y).symm
          exact Subgroup.mem_centralizer_singleton_iff.mp ((iSup_le hcen) hg)
    · exact Or.inr (Or.inr (range_m11 hM hc (θ.comp (D.hom i)) (hnt i)))

end Abstract

section Components

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem component_cases (hΩ : InClass3 Ω) {ι : Type}
    (D : LieSystemData3 ι (↥(centralizingLayer Ω {a}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Ω {a})
        (centralizingLayer Ω {a}))))
    {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L) :
    OmegaFreeAt Ω a L ∨ ∃ k, L = ((layerQuotientHom hΩ.conjInvariant a).comp (D.hom k)).range ∧
      D.kind k ≠ CompData.sl23 := by
  have hθ := layerQuotientHom_injective (a := a) hΩ.conjInvariant
  let Dec := lieDecomposition3_of_lieSystemData3' ModelFacts.modelClauseZero m11Facts D
    (layerQuotientHom hΩ.conjInvariant a) hθ
    (by
      rintro _ ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩
      exact not_le_center_of_mem3 hΩ hK)
  have hrange : (layerQuotientHom hΩ.conjInvariant a).range = memberJoin Ω a :=
    range_layerQuotientHom hΩ.conjInvariant
  have hnormal : (layerQuotientHom hΩ.conjInvariant a).range.Normal := by
    rw [hrange]
    exact memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  have hdich : (∃ i, L = Dec.Q i) ∨ Commutes L (layerQuotientHom hΩ.conjInvariant a).range :=
    @LieDecomposition3.eq_or_commutes_of_isComponentOf _ _ _ _ Dec _ hnormal _ hL'
  rcases hdich with ⟨i, hi⟩ | hcomm
  · right
    have hi' : L = ((layerQuotientHom hΩ.conjInvariant a).comp (D.hom i)).range := hi
    refine ⟨i, hi', fun hc => ?_⟩
    have hsolv := isSolvable_range_of_sl23 hc
      ((layerQuotientHom hΩ.conjInvariant a).comp (D.hom i))
    subst hi'
    have hq := hL'.2.2
    have hsimple : IsSimpleGroup (↥((layerQuotientHom hΩ.conjInvariant a).comp (D.hom i)).range ⧸
        Subgroup.center ↥((layerQuotientHom hΩ.conjInvariant a).comp (D.hom i)).range) := hq.2
    have hnt : Nontrivial ↥((layerQuotientHom hΩ.conjInvariant a).comp (D.hom i)).range := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      have : Subsingleton (↥((layerQuotientHom hΩ.conjInvariant a).comp (D.hom i)).range ⧸
          Subgroup.center ↥((layerQuotientHom hΩ.conjInvariant a).comp (D.hom i)).range) :=
        inferInstance
      exact (not_nontrivial_iff_subsingleton.mpr this) hsimple.toNontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne hq.1
  · left
    intro K hKΩ hKC x hx y hy
    have hxY : x ∈ memberJoin Ω a :=
      le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) K
        ⟨hKΩ, hKC⟩ hx
    rw [← hrange] at hxY
    exact (hcomm y hy x hxY).symm

end Components

end CFSG.ClassicalInvolution.Q3.Q3KB
