module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3NFClosure

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NH

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NF
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement


section Normalizes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem normalizesLayer_exactFamily3 (hΦ : SecData3 c (exactFamily3 Ω c)) :
    NormalizesLayer (exactFamily3 Ω c) c := fun _ hn =>
  mem_normalizer_centralizingLayer_of_secData hΦ hn

end Normalizes

section Abstract

variable {X Yb : Type} [Group X] [Group Yb] {Φ : Set (Subgroup Yb)} {ι : Type}

@[expose] noncomputable def explicitDec (h0 : ModelClauseZero) (hM : M11Facts)
    (D : LieSystemData3 ι Yb Φ)
    (θ : Yb →* X) (hθ : Function.Injective θ) (hnc : ∀ L ∈ Φ, ¬ L ≤ Subgroup.center Yb) :
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

theorem explicitDec_Q (h0 : ModelClauseZero) (hM : M11Facts) (D : LieSystemData3 ι Yb Φ)
    (θ : Yb →* X) (hθ : Function.Injective θ) (hnc : ∀ L ∈ Φ, ¬ L ≤ Subgroup.center Yb)
    (i : ι) : (explicitDec h0 hM D θ hθ hnc).Q i = (θ.comp (D.hom i)).range :=
  rfl

end Abstract

section Cases

variable {G : Type} [Group G] [Finite G] {c : G}

theorem localFamily_not_le_center {Φ : Set (Subgroup G)} (hΦ : SecData3 c Φ)
    {M : Subgroup G} (hM : M ∈ Φ) :
    ¬ modOddIn (centralizingLayer Φ {c}) M ≤
      Subgroup.center (↥(centralizingLayer Φ {c}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer Φ {c})) := by
  obtain ⟨z, hz⟩ := hΦ.member M hM
  have hMY : M ≤ centralizingLayer Φ {c} := le_centralizingLayer ⟨hM, hΦ.le M hM⟩
  have hYc : centralizingLayer Φ {c} ≤ Subgroup.centralizer ({c} : Set G) :=
    centralizingLayer_le_centralizer Φ {c}
  exact ((hz.restrict hYc hMY).toIn.2).map_oddQuotient.not_le_center

theorem component_cases_exact {Φ : Set (Subgroup G)} (hΦ : SecData3 c Φ)
    (hN : NormalizesLayer Φ c) {ι : Type}
    (D : LieSystemData3 ι (LocalQuot Φ c) (localFamily Φ c))
    {L : Subgroup (OddQuot c)} (hL : CFSG.IsComponent L) {x y : OddQuot c}
    (hx : x ∈ (sectionQuotientHom hN).range) (hy : y ∈ L) (hxy : x * y ≠ y * x) :
    ∃ k, L = ((sectionQuotientHom hN).comp (D.hom k)).range ∧ D.kind k ≠ CompData.sl23 := by
  have hθ := sectionQuotientHom_injective hN
  let Dec := explicitDec ModelFacts.modelClauseZero m11Facts D (sectionQuotientHom hN) hθ
    (by
      rintro _ ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩
      exact localFamily_not_le_center hΦ hK.1)
  have hrange : (sectionQuotientHom hN).range = memberJoin Φ c := range_sectionQuotientHom hN
  have hnormal : (sectionQuotientHom hN).range.Normal := by
    rw [hrange]
    exact memberJoin_normal_of_normalizes hN
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  have hdich : (∃ i, L = Dec.Q i) ∨ Commutes L (sectionQuotientHom hN).range :=
    @LieDecomposition3.eq_or_commutes_of_isComponentOf _ _ _ _ Dec _ hnormal _ hL'
  rcases hdich with ⟨i, hi⟩ | hcomm
  · have hi' : L = ((sectionQuotientHom hN).comp (D.hom i)).range := hi
    refine ⟨i, hi', fun hc => ?_⟩
    have hsolv := isSolvable_range_of_sl23 hc ((sectionQuotientHom hN).comp (D.hom i))
    subst hi'
    have hq := hL'.2.2
    have hsimple : IsSimpleGroup (↥((sectionQuotientHom hN).comp (D.hom i)).range ⧸
        Subgroup.center ↥((sectionQuotientHom hN).comp (D.hom i)).range) := hq.2
    have hnt : Nontrivial ↥((sectionQuotientHom hN).comp (D.hom i)).range := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      have : Subsingleton (↥((sectionQuotientHom hN).comp (D.hom i)).range ⧸
          Subgroup.center ↥((sectionQuotientHom hN).comp (D.hom i)).range) := inferInstance
      exact (not_nontrivial_iff_subsingleton.mpr this) hsimple.toNontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne hq.1
  · exact absurd (hcomm y hy x hx).symm hxy

end Cases

section Inner

variable {X Yb : Type} [Group X] [Group Yb] {Φ : Set (Subgroup Yb)} {ι : Type}

theorem exists_inner_of_mem_range (D : LieSystemData3 ι Yb Φ) (θ : Yb →* X) (i : ι) {x : X}
    (hx : x ∈ θ.range) :
    ∃ l ∈ (θ.comp (D.hom i)).range, ∀ y ∈ (θ.comp (D.hom i)).range, x * y * x⁻¹ = l * y * l⁻¹ := by
  obtain ⟨u, rfl⟩ := hx
  have hu : u ∈ (⨆ k, (D.hom k).range : Subgroup Yb) := by rw [D.generate]; trivial
  have key : ∃ v ∈ (D.hom i).range, ∀ w ∈ (D.hom i).range, u * w * u⁻¹ = v * w * v⁻¹ := by
    induction hu using Subgroup.iSup_induction' with
    | hp k y hy =>
      by_cases hki : k = i
      · subst hki
        exact ⟨y, hy, fun w _ => rfl⟩
      · refine ⟨1, one_mem _, fun w hw => ?_⟩
        obtain ⟨a, rfl⟩ := hy
        obtain ⟨b, rfl⟩ := hw
        rw [D.commute k i hki a b]
        group
    | h1 => exact ⟨1, one_mem _, fun w _ => by group⟩
    | hmul x y _ _ hx hy =>
      obtain ⟨l₁, hl₁, h₁⟩ := hx
      obtain ⟨l₂, hl₂, h₂⟩ := hy
      refine ⟨l₁ * l₂, mul_mem hl₁ hl₂, fun w hw => ?_⟩
      have e : x * y * w * (x * y)⁻¹ = x * (y * w * y⁻¹) * x⁻¹ := by group
      rw [e, h₂ w hw, h₁ _ (mul_mem (mul_mem hl₂ hw) (inv_mem hl₂))]
      group
  obtain ⟨v, ⟨b, rfl⟩, hvw⟩ := key
  refine ⟨θ (D.hom i b), ⟨b, rfl⟩, ?_⟩
  rintro _ ⟨a, rfl⟩
  have := congrArg θ (hvw (D.hom i a) ⟨a, rfl⟩)
  simpa [map_mul, map_inv] using this

end Inner

end CFSG.ClassicalInvolution.Q3.Q3NH
