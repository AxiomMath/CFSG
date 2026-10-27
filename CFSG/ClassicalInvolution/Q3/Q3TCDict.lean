module

public import CFSG.ClassicalInvolution.Q3.Q3WAEDict

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

theorem exists_three_indices3 {ι : Type} [Finite ι] (hc : Nat.card ι = 3) (i₁ : ι) :
    ∃ i₀ i₂ : ι, i₀ ≠ i₁ ∧ i₂ ≠ i₁ ∧ i₀ ≠ i₂ ∧ ∀ i, i = i₀ ∨ i = i₁ ∨ i = i₂ := by
  let e : ι ≃ Fin 3 := Finite.equivFinOfCardEq hc
  obtain ⟨a, b, c, hab, hac, hbc, hall⟩ : ∃ a b c : ι, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∀ i, i = a ∨ i = b ∨ i = c := by
    refine ⟨e.symm 0, e.symm 1, e.symm 2, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · intro i
      have h1 : e i = 0 ∨ e i = 1 ∨ e i = 2 := by
        generalize e i = x
        fin_cases x <;> simp
      rcases h1 with h | h | h
      · left; exact e.injective (by simpa using h)
      · right; left; exact e.injective (by simpa using h)
      · right; right; exact e.injective (by simpa using h)
  rcases hall i₁ with h | h | h
  · exact ⟨b, c, fun e => hab (h ▸ e).symm, fun e => hac (h ▸ e).symm, hbc, fun i => by
      rcases hall i with h' | h' | h'
      · exact Or.inr (Or.inl (h'.trans h.symm))
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')⟩
  · exact ⟨a, c, fun e => hab (h ▸ e), fun e => hbc (h ▸ e.symm), hac, fun i => by
      rcases hall i with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl (h'.trans h.symm))
      · exact Or.inr (Or.inr h')⟩
  · exact ⟨a, b, fun e => hac (h ▸ e), fun e => hbc (h ▸ e), hab, fun i => by
      rcases hall i with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
      · exact Or.inr (Or.inl (h'.trans h.symm))⟩

theorem pow_four_of_mem_center_sl4 {w : SL(4, GaloisField 3 1)}
    (hw : w ∈ Subgroup.center SL(4, GaloisField 3 1)) : w ^ 4 = 1 := by
  obtain ⟨r, hr, hrw⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hw
  have h4 : r ^ 4 = 1 := by simpa using hr
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrw, ← map_pow, h4, map_one,
    Matrix.SpecialLinearGroup.coe_one]

section Dict


theorem range_mem_of_a1_comp3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) (hk : D.kind i = CompData.sl23) :
    (D.hom i).range ∈ Φ := by
  obtain ⟨R, hR, hmem⟩ := D.meets i
  have key : ∀ c : CompData, c = CompData.sl23 → ∀ (φ : c.G →* X) (R' : Subgroup c.G),
      R' ∈ c.fund → R'.map φ ∈ Φ → φ.range ∈ Φ := by
    rintro c rfl φ R' hR' hm
    have : R' = ⊤ := hR'
    rwa [this, Subgroup.map_top] at hm
  exact key _ hk (D.hom i) R hR hmem

theorem LocalShapeC3.nonempty_dictT2 {G : Type} [Group G] [Finite G] {tY : StatedLieTag}
    {nY : ℕ} (hsc : FundamentalSingleClass tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember3 K z) (h : LocalShapeC3 2 (CompData.model tY nY) Ω z) :
    Nonempty (ShapeDictT2 3 1 tY nY Ω z) := by
  obtain ⟨ι, hι, D, hcard, i₁, hk₁, hrest⟩ := h
  obtain ⟨i₀, i₂, h₀, h₂, h₀₂, hall⟩ := exists_three_indices3 (by simpa using hcard) i₁
  obtain ⟨ψ, hker, hrange, hfund⟩ := exists_hom_of_comp3 D i₁ hk₁
  have hk0 : D.kind i₀ = CompData.sl23 := hrest i₀ h₀
  have hk2 : D.kind i₂ = CompData.sl23 := hrest i₂ h₂
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hΦ : ConjInvariant (locFamily Ω z) :=
    conjInvariant_oddQuotientFamily (inClass3_local hΩ {z} ⟨K, hKz⟩).conjInvariant
  have hcardSL : ∀ (i : ι), D.kind i = CompData.sl23 →
      Nat.card (D.hom i).range ≤ Nat.card SL(2, GaloisField 3 1) := by
    intro i hi
    have key : ∀ c : CompData, c = CompData.sl23 → ∀ φ : c.G →* locQuot Ω z,
        Nat.card φ.range ≤ Nat.card SL(2, GaloisField 3 1) := by
      rintro c rfl φ
      rw [card_sl2_gf3, ← natCard_sl2Three]
      exact Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    exact key _ hi (D.hom i)
  refine ⟨{
    ψ := ψ
    ker_le := hker
    Q₀ := (D.hom i₀).range
    Q₁ := (D.hom i₂).range
    comm₀₁ := ?_
    comm₀ := ?_
    comm₁ := ?_
    mem₀ := range_mem_of_a1_comp3 D i₀ hk0
    mem₁ := range_mem_of_a1_comp3 D i₂ hk2
    mem_fam := ?_
    fam_cases := ?_
    card_le₀ := hcardSL i₀ hk0
    card_le₁ := hcardSL i₂ hk2 }⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₂ h₀₂ a b
  · rw [hrange]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₁ h₀ a b
  · rw [hrange]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₂ i₁ h₂ a b
  · intro R hR
    obtain ⟨R', hR', hRR'⟩ := (hfund (R.map ψ)).mpr ⟨R, hR, rfl⟩
    rw [hRR']
    exact map_mem_of_comp3 D hΦ i₁ hk₁ hsc R' hR'
  · intro K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    rcases hall i with rfl | rfl | rfl
    · exact Or.inl (Subgroup.map_le_range _ _)
    · obtain ⟨R', hR', hRR'⟩ := (hfund _).mp ⟨R, hR, rfl⟩
      exact Or.inr (Or.inr ⟨R', hR', hRR'⟩)
    · exact Or.inr (Or.inl (Subgroup.map_le_range _ _))

end Dict

section Facts


theorem rankOne_mem_fund_sl4_three (hadm : StatedLieAdmissible .PSL 4 3 1) (i : Fin 3) :
    rankOne (modelUniv .PSL 4 3 1 Nat.prime_three).D.rootGroup i ∈
      fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D :=
  rankOne_mem_fundamental _
    (ModelFacts.isLongestRoot_single .PSL 4 3 1 Nat.prime_three trivial hadm i trivial)

theorem yData3_sl4 (hadm : StatedLieAdmissible .PSL 4 3 1) : YData3 .PSL 4 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .PSL 4 3 1 hp trivial hadm (by decide) (by decide)
  have hB := rankOne_mem_fund_sl4_three hadm
  obtain ⟨W₁, hW₁⟩ := sl_nodes_pair (GaloisField 3 1) 0 1 rfl
  refine ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc (hB 0) (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc (hB 0) hW₁, std_of_stdPair hsc (hB 0) (hB 1) hW₁, ?_⟩
  intro w hw h3
  exact absurd (h3.trans (orderOf_dvd_of_pow_eq_one (pow_four_of_mem_center_sl4 hw)))
    (by norm_num)

end Facts

end CFSG.ClassicalInvolution.Q3.Q3TC
