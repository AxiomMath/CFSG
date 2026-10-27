module

public import CFSG.ClassicalInvolution.Q3.Q3WShape

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal
open scoped MatrixGroups


theorem exists_psl_hom3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) {k : ℕ} (hk : D.kind i = CompData.model .PSL (k + 1)) :
    ∃ ψ : SL(k + 1, GaloisField 3 1) →* X,
      ψ.ker ≤ Subgroup.center SL(k + 1, GaloisField 3 1) ∧ ψ.range = (D.hom i).range ∧
      ∀ K : Subgroup X, (∃ R ∈ (D.kind i).fund, K = R.map (D.hom i)) ↔
        ∃ R ∈ fundamentalSubgroups .PSL (SpecialLinear.rootDatum k (GaloisField 3 1)),
          K = R.map ψ := by
  have key : ∀ c : CompData, c = CompData.model .PSL (k + 1) →
      ∀ (φ : c.G →* X) (_ : φ.ker ≤ Subgroup.center c.G),
      ∃ ψ : SL(k + 1, GaloisField 3 1) →* X,
        ψ.ker ≤ Subgroup.center SL(k + 1, GaloisField 3 1) ∧ ψ.range = φ.range ∧
        ∀ K : Subgroup X, (∃ R ∈ c.fund, K = R.map φ) ↔
          ∃ R ∈ fundamentalSubgroups .PSL (SpecialLinear.rootDatum k (GaloisField 3 1)),
            K = R.map ψ := by
    rintro c rfl φ hφ
    exact ⟨φ, hφ, rfl, fun K => Iff.rfl⟩
  exact key _ hk (D.hom i) (D.ker_le_center i)

theorem map_mem_of_psl3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (hΦ : ConjInvariant Φ) (i : ι) {k : ℕ}
    (hk : D.kind i = CompData.model .PSL (k + 1)) (hk2 : 2 ≤ k + 1) :
    ∀ R ∈ (D.kind i).fund, R.map (D.hom i) ∈ Φ := by
  have key : ∀ c : CompData, c = CompData.model .PSL (k + 1) → ∀ (φ : c.G →* X),
      (∃ R₀ ∈ c.fund, R₀.map φ ∈ Φ) → ∀ R ∈ c.fund, R.map φ ∈ Φ := by
    rintro c rfl φ ⟨R₀, hR₀, hmem⟩ R hR
    obtain ⟨g, rfl⟩ := fundamentalSingleClass_psl (F := GaloisField 3 1) hk2 R₀ hR₀ R hR
    exact (conjSub_map φ g R₀) ▸ hΦ (φ g) _ hmem
  exact key _ hk (D.hom i) (D.meets i)

theorem LocalShapeC3.nonempty_dict {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember3 K z) (h : LocalShapeC3 1 (CompData.model .PSL (m + 1)) Ω z) :
    Nonempty (ShapeADict 3 1 m Ω z) := by
  obtain ⟨ι, hι, D, hcard, i₁, hk₁, hrest⟩ := h
  have hk : 2 ≤ m + 1 := by omega
  obtain ⟨i₀, hne, hall⟩ : ∃ i₀ : ι, i₀ ≠ i₁ ∧ ∀ i, i = i₀ ∨ i = i₁ := by
    obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp (by simpa using hcard : Nat.card ι = 2)
    have hx : ∀ i, i = x ∨ i = y := fun i => by
      have : i ∈ ({x, y} : Set ι) := by rw [hset]; trivial
      simpa using this
    rcases hx i₁ with h1 | h1
    · refine ⟨y, fun e => hxy (h1 ▸ e.symm), fun i => ?_⟩
      rcases hx i with h2 | h2
      · exact Or.inr (h2.trans h1.symm)
      · exact Or.inl h2
    · refine ⟨x, fun e => hxy (h1 ▸ e), fun i => ?_⟩
      rcases hx i with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (h2.trans h1.symm)
  obtain ⟨ψ₁, hker₁, hrange₁, hfund₁⟩ := exists_psl_hom3 D i₁ hk₁
  have hk0 : D.kind i₀ = CompData.sl23 := hrest i₀ hne
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hΦ : ConjInvariant (locFamily Ω z) :=
    conjInvariant_oddQuotientFamily (inClass3_local hΩ {z} ⟨K, hKz⟩).conjInvariant
  refine ⟨{
    ψ := ψ₁
    ker_le := hker₁
    Q₀ := (D.hom i₀).range
    commutes := ?_
    mem_fam := ?_
    fam_cases := ?_
    card_le := ?_ }⟩
  · rw [hrange₁]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₁ hne a b
  · intro hk' R hR
    obtain ⟨R', hR', hRR'⟩ := (hfund₁ (R.map ψ₁)).mpr
      ⟨R, longRootSet_subset_fundamentalSubgroups_psl hk' hR, rfl⟩
    rw [hRR']
    exact map_mem_of_psl3 D hΦ i₁ hk₁ hk' R' hR'
  · intro hk' K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    rcases hall i with h0 | h1
    · subst h0
      exact Or.inl (Subgroup.map_le_range _ _)
    · subst h1
      obtain ⟨R', hR', hRR'⟩ := (hfund₁ _).mp ⟨R, hR, rfl⟩
      exact Or.inr ⟨R', fundamentalSubgroups_psl_subset hk' hR', hRR'⟩
  · have hF : Nat.card (GaloisField 3 1) = 3 := by
      rw [GaloisField.card 3 1 one_ne_zero]
      norm_num
    have h24 : Nat.card SL(2, GaloisField 3 1) = 24 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
      norm_num
    have key : ∀ c : CompData, c = CompData.sl23 → ∀ φ : c.G →* locQuot Ω z,
        Nat.card φ.range ≤ Nat.card SL(2, GaloisField 3 1) := by
      rintro c rfl φ
      rw [h24, ← natCard_sl2Three]
      exact Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    exact key _ hk0 (D.hom i₀)

end CFSG.ClassicalInvolution.Q3.Q3W
