module

public import CFSG.ClassicalInvolution.Balance.OddCentralizerFreeLayer
public import CFSG.ClassicalInvolution.Balance.PassTwoLocal

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem lieModel_of_surjective {K L : Type} [Group K] [Group L] (hK : CFSG.Open.IsQuasisimple K)
    (ψ : K →* L) (hψ : Function.Surjective ψ) (hψ1 : ∃ x, ψ x ≠ 1) {t : StatedLieTag}
    {n p f : ℕ} (hmodel : LieModel (K ⧸ Subgroup.center K) t n p f) :
    LieModel (L ⧸ Subgroup.center L) t n p f := by
  have hK' : CFSG.IsQuasisimple K := CatalogueBAlternating.quasisimple_iff_native.mpr hK
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hK' hψ
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hK' hψ1)) hmodel

theorem isOddLieComponentBig_of_surjective {X : Type} [Group X] {L : Subgroup X} {K : Type}
    [Group K] (hK : CFSG.Open.IsQuasisimple K) (ψ : K →* ↥L) (hψ : Function.Surjective ψ)
    (hψ1 : ∃ x, ψ x ≠ 1) {t : StatedLieTag} {n p f : ℕ} (hp : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hn : t = .PSL → 3 ≤ n) (ht : t ∈ classicalTags ∨ t ∈ chevalleyExceptionalTags)
    (hmodel : LieModel (K ⧸ Subgroup.center K) t n p f) : IsOddLieComponentBig L :=
  ⟨t, n, p, f, hp, h5, hn, ht, lieModel_of_surjective hK ψ hψ hψ1 hmodel⟩

theorem five_le_pow_of_ne_three {p f e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (he : e = f ∨ 3 * e = f) (h3 : p ^ e ≠ 3) : 5 ≤ p ^ e := by
  by_contra hlt
  push Not at hlt
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨k, hk⟩ := hodd
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · rcases he with rfl | rfl
    · omega
    · rw [pow_mul' p 3 e, hk] at hq
      omega
  · exact h3 (by omega)

theorem pow_exp_ne_three_of_ne_27 {p f e : ℕ} (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (he : e = f ∨ 3 * e = f) : p ^ e ≠ 3 := by
  intro h3
  rcases he with rfl | rfl
  · omega
  · apply h27
    rw [pow_mul' p 3 e, h3]
    norm_num

theorem exception_of_pow_exp_eq_three {p f e : ℕ} (hp : p.Prime) (hq : 5 ≤ p ^ f)
    (he : e = f ∨ 3 * e = f) (h3 : p ^ e = 3) : 3 * e = f ∧ p = 3 ∧ e = 1 ∧ p ^ f = 27 := by
  rcases he with rfl | h3e
  · omega
  · have he0 : e ≠ 0 := by
      rintro rfl
      simp at h3
    have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (h3 ▸ dvd_pow_self p he0)
    subst hp3
    have he1 : e = 1 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ e = 3 ^ 1 by simpa using h3)
    subst he1
    subst h3e
    exact ⟨rfl, rfl, rfl, by norm_num⟩

@[expose] def LieDecomposition.Big {X : Type} [Group X] {Ψ : Set (Subgroup X)} {Y : Subgroup X}
    (D : LieDecomposition Ψ Y) : Prop :=
  ∀ i, ((∃ L ∈ Ψ, L = D.Q i) ∧ (∀ L ∈ Ψ, L ≤ D.Q i → L = D.Q i)) ∨
    IsOddLieComponentBig (D.Q i)

theorem LieDecomposition.exists_congr {X : Type} [Group X] {Ψ Ψ' : Set (Subgroup X)}
    {Y Y' : Subgroup X} (hΨ : Ψ = Ψ') (hY : Y = Y') (Qs : Set (Subgroup X)) (B : Prop) :
    (∃ D : LieDecomposition Ψ Y, (∀ i, D.Q i ∈ Qs) ∧ (B → D.Big)) →
      ∃ D : LieDecomposition Ψ' Y', (∀ i, D.Q i ∈ Qs) ∧ (B → D.Big) := by
  subst hΨ
  subst hY
  exact id

section Abstract

variable {p f : ℕ} [Fact p.Prime]

theorem lieDecomposition_of_lieSystemData_comp (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) {X Yb : Type} [Group X] [Group Yb]
    {Φ : Set (Subgroup Yb)} (D : LieSystemData p f Yb Φ) (θ : Yb →* X)
    (hθ : Function.Injective θ) (hnc : ∀ L ∈ Φ, ¬ L ≤ Subgroup.center Yb) :
    ∃ D' : LieDecomposition (Subgroup.map θ '' Φ) θ.range,
      (∀ i, D'.Q i ∈ Set.range fun j : Fin D.card => (θ.comp (D.hom j)).range) ∧
        ((∀ i, p ^ D.exp i ≠ 3) → D'.Big) := by
  let Q : Fin D.card → Subgroup X := fun i => (θ.comp (D.hom i)).range
  have hQmap : ∀ i, Q i = (D.hom i).range.map θ := fun i => MonoidHom.range_comp θ (D.hom i)
  have hK : ∀ i, CFSG.Open.IsQuasisimple (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K :=
    fun i => (h0 _ _ _ _ _ (D.isFundTag i) (D.admissible i)).1
  have hker : ∀ i, (θ.comp (D.hom i)).ker ≤ Subgroup.center _ := fun i x hx => by
    apply D.ker_le_center i
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hθ (by simpa using hx)
  have hmem : ∀ L ∈ Φ, ∃ j R, R ∈ fundamentalSubgroups (D.tag j)
      (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D ∧ L = R.map (D.hom j) :=
    fun L hL => D.fundamental L hL
  have hquasi : ∀ i, CFSG.Open.IsQuasisimple (Q i) := by
    intro i
    have hq' := Quasisimple.central_quotient (hK i) (θ.comp (D.hom i)).ker (hker i)
    exact Components.quasisimple_of_equiv
      (QuotientGroup.quotientKerEquivRange (θ.comp (D.hom i))).symm hq'
  have hcomm : ∀ i j, i ≠ j → Commutes (Q i) (Q j) := by
    rintro i j hij _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, D.commute i j hij a b]
  have hsup : ⨆ i, Q i = θ.range := by
    simp_rw [hQmap]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
  have hle : ∀ L ∈ Subgroup.map θ '' Φ, ∃ i, L ≤ Q i := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, -, rfl⟩ := hmem L hL
    exact ⟨i, (hQmap i).symm ▸ Subgroup.map_mono (Subgroup.map_le_range _ _)⟩
  have hA₁ : ∀ i, (D.tag i = .PSL ∧ D.rank i = 2) →
      (∃ L ∈ Subgroup.map θ '' Φ, L = Q i) ∧
        (∀ L ∈ Subgroup.map θ '' Φ, L ≤ Q i → L = Q i) := by
    intro i hr
    have hA := hA1 (D.tag i) (D.rank i) p (D.exp i) Fact.out (D.isFundTag i) (D.admissible i) hr
    refine ⟨⟨(D.hom i).range.map θ, ⟨(D.hom i).range, ?_, rfl⟩, (hQmap i).symm⟩, ?_⟩
    · obtain ⟨R, hR, hmem'⟩ := D.meets i
      rwa [hA R hR, Subgroup.map_top] at hmem'
    · rintro _ ⟨L₁, hL₁, rfl⟩ hle'
      rw [hQmap i] at hle' ⊢
      have hle'' : L₁ ≤ (D.hom i).range := (Subgroup.map_le_map_iff_of_injective hθ).mp hle'
      obtain ⟨j, R', hR', hL₁eq⟩ := hmem L₁ hL₁
      by_cases hji : j = i
      · subst hji
        have hA' := hA1 (D.tag j) (D.rank j) p (D.exp j) Fact.out (D.isFundTag j)
          (D.admissible j) hr
        rw [hA' R' hR', Subgroup.map_top] at hL₁eq
        rw [hL₁eq]
      · refine absurd ?_ (hnc L₁ hL₁)
        have hL₁j : L₁ ≤ (D.hom j).range := hL₁eq ▸ Subgroup.map_le_range _ _
        intro x hx
        have hxi := hle'' hx
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
  have hlie : ∀ i, ¬ (D.tag i = .PSL ∧ D.rank i = 2) →
      IsOddLieComponent (Q i) ∧ (p ^ D.exp i ≠ 3 → IsOddLieComponentBig (Q i)) := by
    intro i hr
    have hadm := D.admissible i
    have hn : D.tag i = .PSL → 3 ≤ D.rank i := by
      intro h
      have h2 : 2 ≤ D.rank i := by
        have := hadm.2.2
        rw [h] at this
        exact this.1
      have h3 : D.rank i ≠ 2 := fun h' => hr ⟨h, h'⟩
      omega
    obtain ⟨-, hmodel⟩ := h0 _ _ _ _ _ (D.isFundTag i) hadm
    have hψ1 : ∃ x, (θ.comp (D.hom i)).rangeRestrict x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ x, x ∈ Subgroup.center
          (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K := fun x => by
        apply hker i
        rw [MonoidHom.mem_ker]
        have := hcon x
        rw [← Subtype.coe_inj] at this
        simpa using this
      have hsimple := (hK i).2
      obtain ⟨a, b, hab⟩ := exists_pair_ne
        ((modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K ⧸ Subgroup.center
          (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K)
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (QuotientGroup.eq.mpr (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hall a'))
        (hall b')) |> fun h => by simpa using h)
    refine ⟨isOddLieComponent_of_surjective (hK i) (θ.comp (D.hom i)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _) hψ1 hp2 hn (isFundTag_mem_tags (D.isFundTag i))
      hmodel, fun h3 => ?_⟩
    have h5 : 5 ≤ p ^ D.exp i :=
      five_le_pow_of_ne_three Fact.out hp2 hq ((D.exp_eq i).imp id And.right) h3
    exact isOddLieComponentBig_of_surjective (hK i) (θ.comp (D.hom i)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _) hψ1 hp2 h5 hn (isFundTag_mem_tags (D.isFundTag i))
      hmodel
  refine ⟨{ ι := Fin D.card
            Q := Q
            quasisimple := hquasi
            commute := hcomm
            iSup_eq := hsup
            exists_le := hle
            rankOne_or_lie := fun i => ?_ }, fun i => ⟨i, rfl⟩, fun hF3 i => ?_⟩
  · by_cases hr : D.tag i = .PSL ∧ D.rank i = 2
    · exact Or.inl (hA₁ i hr)
    · exact Or.inr (hlie i hr).1
  · by_cases hr : D.tag i = .PSL ∧ D.rank i = 2
    · exact Or.inl (hA₁ i hr)
    · exact Or.inr ((hlie i hr).2 (hF3 i))

theorem lieDecomposition_of_lieSystemData_big (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) {X Yb : Type} [Group X] [Group Yb]
    {Φ : Set (Subgroup Yb)} (D : LieSystemData p f Yb Φ) (hF3 : ∀ i, p ^ D.exp i ≠ 3)
    (θ : Yb →* X) (hθ : Function.Injective θ) (hnc : ∀ L ∈ Φ, ¬ L ≤ Subgroup.center Yb) :
    ∃ D' : LieDecomposition (Subgroup.map θ '' Φ) θ.range, D'.Big := by
  obtain ⟨D', -, hbig⟩ := lieDecomposition_of_lieSystemData_comp hp2 h0 hA1 hq D θ hθ hnc
  exact ⟨D', hbig hF3⟩

end Abstract

section Components

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

abbrev LocalLieSystemAt (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (a : G) : Type :=
  LieSystemData p f
    (↥(centralizingLayer Ω {a}) ⧸ classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))
    (oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) (centralizingLayer Ω {a})))

@[expose] def NoComponentOverF3 (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (a : G) : Prop :=
  ∀ D : LocalLieSystemAt p f Ω a, ∀ i, p ^ D.exp i ≠ 3

omit [Finite G] in
theorem NoComponentOverF3.of_ne_27 (a : G) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27) :
    NoComponentOverF3 p f Ω a :=
  fun D i => pow_exp_ne_three_of_ne_27 hq h27 ((D.exp_eq i).imp id And.right)

theorem lieDecomposition_localSystem_comp (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) {a : G}
    (D : LocalLieSystemAt p f Ω a) :
    ∃ D' : LieDecomposition (memberImages Ω a) (memberJoin Ω a),
      (∀ i, D'.Q i ∈ Set.range fun j : Fin D.card =>
        ((layerQuotientHom hΩ.conjInvariant a).comp (D.hom j)).range) ∧
      ((∀ i, p ^ D.exp i ≠ 3) → D'.Big) := by
  have hθ := layerQuotientHom_injective (a := a) hΩ.conjInvariant
  have h := lieDecomposition_of_lieSystemData_comp hp2 h0 hA1 hq D
    (layerQuotientHom hΩ.conjInvariant a) hθ
    (by
      rintro _ ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩
      exact not_le_center_of_mem hΩ hK)
  have hΨ : Subgroup.map (layerQuotientHom hΩ.conjInvariant a) ''
      oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) (centralizingLayer Ω {a})) =
      memberImages Ω a := map_layerQuotientHom_family hΩ.conjInvariant
  exact LieDecomposition.exists_congr hΨ (range_layerQuotientHom hΩ.conjInvariant) _ _ h

theorem lieDecomposition_memberImages_big (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {a : G} (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hF3 : NoComponentOverF3 p f Ω a) :
    ∃ D : LieDecomposition (memberImages Ω a) (memberJoin Ω a), D.Big := by
  obtain ⟨D⟩ := hIH {a} ha
  obtain ⟨D', -, hbig⟩ := lieDecomposition_localSystem_comp hp2 h0 hA1 hq hΩ D
  exact ⟨D', hbig (hF3 D)⟩

theorem omegaFreeAt_or_rankOneAt_or_isOddLieComponentBig (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {a : G} (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hF3 : NoComponentOverF3 p f Ω a) {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L) :
    OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (IsOddLieComponentBig L ∧ L ≤ memberJoin Ω a) := by
  obtain ⟨D, hD⟩ := lieDecomposition_memberImages_big hp2 h0 hA1 hq hΩ hIH ha hF3
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · rcases hD i with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | hbig
    · right
      left
      refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
      obtain ⟨j, hj⟩ := D.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
      by_cases hji : j = i
      · subst hji
        exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
      · exact Or.inr fun x hx y hy => D.commute j i hji x (hj hx) y hy
    · exact Or.inr (Or.inr ⟨hbig, D.le_join i⟩)
  · left
    intro K hKΩ hKC x hx y hy
    have hxY : x ∈ memberJoin Ω a :=
      le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) K
        ⟨hKΩ, hKC⟩ hx
    exact (hcomm y hy x hxY).symm

theorem omegaFreeAt_or_rankOneAt_or_isOddLieComponent_le_join (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {a : G}
    (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) {L : Subgroup (OddQuot a)}
    (hL : CFSG.IsComponent L) :
    OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (IsOddLieComponent L ∧ L ≤ memberJoin Ω a) := by
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 h0 hA1 hΩ hIH ha
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · rcases D.rankOne_or_lie i with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | hlie
    · right
      left
      refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
      obtain ⟨j, hj⟩ := D.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
      by_cases hji : j = i
      · subst hji
        exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
      · exact Or.inr fun x hx y hy => D.commute j i hji x (hj hx) y hy
    · exact Or.inr (Or.inr ⟨hlie, D.le_join i⟩)
  · left
    intro K hKΩ hKC x hx y hy
    have hxY : x ∈ memberJoin Ω a :=
      le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) K
        ⟨hKΩ, hKC⟩ hx
    exact (hcomm y hy x hxY).symm

end Components

end CFSG.ClassicalInvolution.Balance
