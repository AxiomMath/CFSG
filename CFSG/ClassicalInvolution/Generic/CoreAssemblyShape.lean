module

public import CFSG.ClassicalInvolution.RouteD.TypeCRecognition
public import CFSG.ClassicalInvolution.RouteD.LocalTwin
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def IsA1Comp {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ)
    (i : Fin D.card) : Prop :=
  D.tag i = .PSL ∧ D.rank i = 2

@[expose] def MultiShape (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x),
    ∃ i j : Fin D.card, i ≠ j ∧ ¬ IsA1Comp D i ∧ ¬ IsA1Comp D j

theorem shape_dichotomy {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (hne : 0 < D.card) :
    (∃ i j : Fin D.card, i ≠ j ∧ ¬ IsA1Comp D i ∧ ¬ IsA1Comp D j) ∨
      ∃ (a : ℕ) (tY : StatedLieTag) (nY : ℕ), D.card = a + 1 ∧ ∃ i₁ : Fin D.card,
        D.tag i₁ = tY ∧ D.rank i₁ = nY ∧ ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2 := by
  by_cases h : ∃ i j : Fin D.card, i ≠ j ∧ ¬ IsA1Comp D i ∧ ¬ IsA1Comp D j
  · exact Or.inl h
  · right
    push Not at h
    by_cases hex : ∃ i, ¬ IsA1Comp D i
    · obtain ⟨i₁, hi₁⟩ := hex
      exact ⟨D.card - 1, D.tag i₁, D.rank i₁, by omega, i₁, rfl, rfl,
        fun i hi => h i₁ i (Ne.symm hi) hi₁⟩
    · push Not at hex
      exact ⟨D.card - 1, D.tag ⟨0, hne⟩, D.rank ⟨0, hne⟩, by omega, ⟨0, hne⟩, rfl, rfl,
        fun i _ => hex i⟩

theorem _root_.CFSG.ClassicalInvolution.RouteD.LocalShapeT.exists_two_components
    {Ω : Set (Subgroup G)} {x : G} {tY : StatedLieTag} {nY : ℕ}
    (h : LocalShapeT p f 1 tY nY Ω x) :
    ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), D.card = 2 ∧
      ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧ D.tag i₁ = tY ∧
        D.rank i₁ = nY := by
  obtain ⟨D, hc, i₁, ht, hr, hrest⟩ := h
  have h2 : D.card = 2 := hc
  refine ⟨D, h2, ?_⟩
  have hlt := i₁.isLt
  let i₀ : Fin D.card := ⟨1 - i₁.val, by omega⟩
  have hne : i₀ ≠ i₁ := by
    intro e
    have : 1 - i₁.val = i₁.val := congrArg Fin.val e
    omega
  exact ⟨i₀, i₁, hne, (hrest i₀ hne).1, (hrest i₀ hne).2, ht, hr⟩

theorem localShapeA_of_T {m : ℕ} {Ω : Set (Subgroup G)} {x : G}
    (h : LocalShapeT p f 1 .PSL (m + 1) Ω x) : LocalShapeA p f m Ω x :=
  h.exists_two_components

theorem localShapeC_of_T {m : ℕ} {Ω : Set (Subgroup G)} {x : G}
    (h : LocalShapeT p f 1 .PSp m Ω x) : LocalShapeC p f m Ω x :=
  h.exists_two_components

theorem card_pos_local {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsClassicalMember p f K z)
    (D : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) : 0 < D.card := by
  have hmem : locImg Ω z K ∈ locFamily Ω z :=
    mem_locFamily_iff.mpr ⟨K, ⟨hK, le_centralizer_of_isClassicalMember hz⟩, rfl⟩
  obtain ⟨i, -⟩ := D.fundamental _ hmem
  exact i.pos

theorem exists_shape_or_multi {Ω : Set (Subgroup G)} (hLL : LocalLieSystems p f Ω) {K : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G) :
    (∃ (a : ℕ) (tY : StatedLieTag) (nY : ℕ), LocalShapeT p f a tY nY Ω z) ∨ MultiShape p f Ω z := by
  obtain ⟨D⟩ := hLL {z} hnc
  have hpos := card_pos_local hK hz D
  rcases shape_dichotomy D hpos with h | ⟨a, tY, nY, hc, i₁, ht, hr, hrest⟩
  · exact Or.inr ⟨D, h⟩
  · exact Or.inl ⟨a, tY, nY, D, hc, i₁, ht, hr, hrest⟩

end CFSG.ClassicalInvolution.Generic.CoreAssembly
