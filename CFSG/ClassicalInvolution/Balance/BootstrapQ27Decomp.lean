module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationField

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem lieDecomposition_of_lieSystemData_idx (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) {X Yb : Type} [Group X] [Group Yb]
    {Φ : Set (Subgroup Yb)} (D : LieSystemData p f Yb Φ) (θ : Yb →* X)
    (hθ : Function.Injective θ) (hnc : ∀ L ∈ Φ, ¬ L ≤ Subgroup.center Yb)
    {Ψ' : Set (Subgroup X)} {Y' : Subgroup X} (hΨ : Subgroup.map θ '' Φ = Ψ')
    (hY : θ.range = Y') :
    ∃ D' : LieDecomposition Ψ' Y', ∃ κ : D'.ι → Fin D.card,
      (∀ i, D'.Q i = (θ.comp (D.hom (κ i))).range) ∧
        ∀ i, p ^ D.exp (κ i) ≠ 3 →
          (((∃ L ∈ Ψ', L = D'.Q i) ∧ (∀ L ∈ Ψ', L ≤ D'.Q i → L = D'.Q i)) ∨
            IsOddLieComponentBig (D'.Q i)) := by
  subst hΨ
  subst hY

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
            rankOne_or_lie := fun i => ?_ }, fun i => i, fun i => rfl, fun i hi => ?_⟩
  · by_cases hr : D.tag i = .PSL ∧ D.rank i = 2
    · exact Or.inl (hA₁ i hr)
    · exact Or.inr (hlie i hr).1
  · by_cases hr : D.tag i = .PSL ∧ D.rank i = 2
    · exact Or.inl (hA₁ i hr)
    · exact Or.inr ((hlie i hr).2 hi)


section Local

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem lieDecomposition_localSystem_idx (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) {a : G}
    (D : LocalLieSystemAt p f Ω a) :
    ∃ D' : LieDecomposition (memberImages Ω a) (memberJoin Ω a), ∃ κ : D'.ι → Fin D.card,
      (∀ i, D'.Q i = ((layerQuotientHom hΩ.conjInvariant a).comp (D.hom (κ i))).range) ∧
        ∀ i, p ^ D.exp (κ i) ≠ 3 →
          (((∃ L ∈ memberImages Ω a, L = D'.Q i) ∧
            (∀ L ∈ memberImages Ω a, L ≤ D'.Q i → L = D'.Q i)) ∨
            IsOddLieComponentBig (D'.Q i)) :=
  lieDecomposition_of_lieSystemData_idx hp2 h0 hA1 hq D (layerQuotientHom hΩ.conjInvariant a)
    (layerQuotientHom_injective (a := a) hΩ.conjInvariant)
    (by
      rintro _ ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩
      exact not_le_center_of_mem hΩ hK)
    (map_layerQuotientHom_family hΩ.conjInvariant) (range_layerQuotientHom hΩ.conjInvariant)

end Local

end CFSG.ClassicalInvolution.Balance.Bootstrap
