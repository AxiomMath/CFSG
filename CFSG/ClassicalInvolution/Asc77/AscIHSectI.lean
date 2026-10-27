module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectC

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

section Dichotomy

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dConnected_or_transitive {n : ℕ} (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h4 : Thm4Below p f n)
    (hlt : Nat.card X < n) (hΦ : HypOmegaMod p f Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) :
    DConnected Φ ∨ ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L := by
  by_cases htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L
  · exact Or.inr htrans
  left
  push Not at htrans
  obtain ⟨K₀, hK₀, M₀, hM₀, hnc⟩ := htrans
  have hc0 : Commutes K₀ M₀ :=
    h4 hp hq X hlt Φ hΦ hO hA K₀ hK₀ M₀ hM₀ (fun ⟨g, hg⟩ => hnc g hg)
  have hne0 : K₀ ≠ M₀ := fun h => hnc 1 (by rw [conjSub_one, h])
  have hadj0 : dAdj Φ K₀ M₀ := dAdj_of_commutes hM₀ hne0 hc0
  have hjoin : ∀ M ∈ Φ,
      Relation.ReflTransGen (fun A B : Subgroup X => B ∈ Φ ∧ dAdj Φ A B) K₀ M ∧
        Relation.ReflTransGen (fun A B : Subgroup X => B ∈ Φ ∧ dAdj Φ A B) M K₀ := by
    intro M hM
    by_cases hMc : ∃ g : X, conjSub g K₀ = M
    · have hnotM : ¬ ∃ g : X, conjSub g M = M₀ := by
        rintro ⟨g, hg⟩
        obtain ⟨y, rfl⟩ := hMc
        exact hnc (g * y) (by rw [conjSub_mul]; exact hg)
      have hc : Commutes M M₀ := h4 hp hq X hlt Φ hΦ hO hA M hM M₀ hM₀ hnotM
      have hne : M ≠ M₀ := fun h => hnotM ⟨1, by rw [conjSub_one, h]⟩
      have hadj : dAdj Φ M M₀ := dAdj_of_commutes hM₀ hne hc
      exact ⟨(Relation.ReflTransGen.single ⟨hM₀, hadj0⟩).tail ⟨hM, dAdj_symm hadj⟩,
        (Relation.ReflTransGen.single ⟨hM₀, hadj⟩).tail ⟨hK₀, dAdj_symm hadj0⟩⟩
    · push Not at hMc
      have hc : Commutes K₀ M :=
        h4 hp hq X hlt Φ hΦ hO hA K₀ hK₀ M hM (fun ⟨g, hg⟩ => hMc g hg)
      have hne : K₀ ≠ M := fun h => hMc 1 (by rw [conjSub_one, h])
      have hadj : dAdj Φ K₀ M := dAdj_of_commutes hM hne hc
      exact ⟨Relation.ReflTransGen.single ⟨hM, hadj⟩,
        Relation.ReflTransGen.single ⟨hK₀, dAdj_symm hadj⟩⟩
  intro K hK L hL
  exact (hjoin K hK).2.trans (hjoin L hL).1

omit [Finite X] in
theorem eq_of_dConnected_of_dEdgeless (hc : DConnected Φ) (he : DEdgeless Φ) {K L : Subgroup X}
    (hK : K ∈ Φ) (hL : L ∈ Φ) : K = L := by
  rcases (hc K hK L hL).cases_head with h | ⟨c, ⟨hcΦ, hadj⟩, -⟩
  · exact h
  · exact absurd hadj (he K hK c hcΦ)

end Dichotomy

structure GenSection (p f : ℕ) [Fact p.Prime] {X : Type} [Group X] (Φ : Set (Subgroup X)) :
    Prop where
  hyp : HypOmegaMod p f Φ
  oddCore : classicalInvolutionOddCore X = ⊥
  gen : omegaGen Φ = ⊤
  aEmpty : ∀ J ∈ Φ, AEmpty Φ J

theorem TransSection.toGen {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (h : TransSection p f Φ) : GenSection p f Φ :=
  ⟨h.hyp, h.oddCore, h.gen, h.aEmpty⟩

theorem GenSection.toTrans {X : Type} [Group X] {Φ : Set (Subgroup X)} (h : GenSection p f Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) : TransSection p f Φ :=
  ⟨h.hyp, h.oddCore, h.gen, htrans, h.aEmpty⟩

section Dich

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem transSection_or_dConnected {n : ℕ} (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h4 : Thm4Below p f n)
    (hlt : Nat.card X < n) (h : GenSection p f Φ) : DConnected Φ ∨ TransSection p f Φ := by
  rcases dConnected_or_transitive hp hq h4 hlt h.hyp h.oddCore h.aEmpty with hc | ht
  · exact Or.inl hc
  · exact Or.inr (h.toTrans ht)

end Dich

section Statements

variable (p f)

@[expose] def Thm6SectBelow' (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), GenSection p f Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ →
        DEdgeless Φ →
          HasLieType p f Φ .PSL 3 ∨ HasLieType p f Φ .PSU 3 ∨ HasLieType p f Φ .G2 0 ∨
            HasLieType p f Φ .trialityD4 0

@[expose] def Thm8SectBelow' (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), GenSection p f Φ → Φ.Nonempty → ¬ DEdgeless Φ →
        ¬ DConnected Φ → ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthType p f Φ d ε

end Statements

theorem thm6SectBelow'_of {n : ℕ} (h6 : Thm6SectBelow p f n) (h4 : Thm4Below p f n) :
    Thm6SectBelow' p f n := by
  intro hp2 hq X _ _ hlt Φ hG hne htop hDE
  rcases transSection_or_dConnected hp2 hq h4 hlt hG with hc | hT
  · exfalso
    obtain ⟨K, hK⟩ := hne
    apply htop
    have hall : omegaGen Φ = K := by
      refine le_antisymm (iSup₂_le fun L hL => ?_) (le_omegaGen hK)
      rw [eq_of_dConnected_of_dEdgeless hc hDE hL hK]
    rw [← hG.gen, hall]
    exact hK
  · exact h6 hp2 hq X hlt Φ hT hne htop hDE

theorem thm8SectBelow'_of {n : ℕ} (h8 : Thm8SectBelow p f n) (h4 : Thm4Below p f n) :
    Thm8SectBelow' p f n := by
  intro hp2 hq X _ _ hlt Φ hG hne hNE hNC
  rcases transSection_or_dConnected hp2 hq h4 hlt hG with hc | hT
  · exact absurd hc hNC
  · exact h8 hp2 hq X hlt Φ hT hne hNE hNC

theorem thm6SectBelow'_of_citBelow (hP1 : Ih8SmallEdge p) {n : ℕ} (hn : CITBelowU p f n) :
    Thm6SectBelow' p f n :=
  thm6SectBelow'_of (thm6SectBelow_of hP1 hn) (thm4Below_of_citBelow hn)

theorem thm8SectBelow'_of_citBelow (hP4 : Ih8G2D4 p f) {n : ℕ} (hn : CITBelowU p f n) :
    Thm8SectBelow' p f n :=
  thm8SectBelow'_of (thm8SectBelow_of hP4 hn) (thm4Below_of_citBelow hn)

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def layerHull (Ω : Set (Subgroup G)) (Y : Subgroup G) : Subgroup G :=
  ⨆ L ∈ Ω, ⨆ (_ : L ≤ Y), L

omit [Finite G] in
theorem le_layerHull {Y L : Subgroup G} (hL : L ∈ Ω) (hLY : L ≤ Y) : L ≤ layerHull Ω Y :=
  le_iSup₂_of_le L hL (le_iSup_of_le hLY le_rfl)

omit [Finite G] in
theorem omegaGen_restrictFamily_layerHull (Y : Subgroup G) :
    omegaGen (restrictFamily Ω (layerHull Ω Y)) = ⊤ := by
  apply Subgroup.map_injective (layerHull Ω Y).subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm (Subgroup.map_subtype_le _) ?_
  refine iSup₂_le fun L hL => iSup_le fun hLY => ?_
  have hLY₀ : L ≤ layerHull Ω Y := le_layerHull hL hLY
  have hmem : L.subgroupOf (layerHull Ω Y) ≤ omegaGen (restrictFamily Ω (layerHull Ω Y)) :=
    le_omegaGen ⟨L, hL, hLY₀, rfl⟩
  calc L = (L.subgroupOf (layerHull Ω Y)).map (layerHull Ω Y).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hLY₀).symm
    _ ≤ _ := Subgroup.map_mono hmem

theorem omegaGen_quotFamily_of_gen {H : Type} [Group H] (Λ : Set (Subgroup H)) (N : Subgroup H)
    [N.Normal] (h : omegaGen Λ = ⊤) : omegaGen (quotFamily Λ N) = ⊤ := by
  have hle : omegaGen Λ ≤ (omegaGen (quotFamily Λ N)).comap (QuotientGroup.mk' N) := by
    refine iSup₂_le fun L hL => ?_
    exact (Subgroup.le_comap_map _ L).trans
      (Subgroup.comap_mono (le_omegaGen (map_mem_quotFamily hL)))
  rw [h, top_le_iff] at hle
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hg : g ∈ (omegaGen (quotFamily Λ N)).comap (QuotientGroup.mk' N) := by
    rw [hle]; exact Subgroup.mem_top g
  exact hg

theorem genSection_layerHull (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) (Y : Subgroup G) :
    GenSection p f (oddQuotientFamily (restrictFamily Ω (layerHull Ω Y))) := by
  set Y₀ := layerHull Ω Y with hY₀
  set N₀ : Subgroup ↥Y₀ := classicalInvolutionOddCore ↥Y₀ with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y₀
  have hΛ : HypOmegaMod p f (restrictFamily Ω Y₀) := hΩ.restrict Y₀
  have hΛ' : HypOmegaMod p f (quotFamily (restrictFamily Ω Y₀) N₀) :=
    oddQuotHyp p f hp hq ↥Y₀ _ hΛ N₀ hN₀odd
  have hΛA : ∀ L ∈ restrictFamily Ω Y₀, AEmpty (restrictFamily Ω Y₀) L := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    exact AEmpty.restrict hp hΩ hLY (hA L hL)
  exact
    { hyp := hΛ'
      oddCore := CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y₀
      gen := omegaGen_quotFamily_of_gen _ N₀ (omegaGen_restrictFamily_layerHull Y)
      aEmpty := aEmpty_quotFamily hp hq hΛ hΛ' hN₀odd hΛA }

theorem sectionLie_of_thm6' {n : ℕ} (h6 : Thm6SectBelow' p f n) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : ∀ L ∈ Ω, AEmpty Ω L) (Y : Subgroup G)
    (hlt : Nat.card (↥(layerHull Ω Y) ⧸ classicalInvolutionOddCore ↥(layerHull Ω Y)) < n)
    (hne : (oddQuotientFamily (restrictFamily Ω (layerHull Ω Y))).Nonempty)
    (htop : (⊤ : Subgroup (↥(layerHull Ω Y) ⧸ classicalInvolutionOddCore ↥(layerHull Ω Y))) ∉
      oddQuotientFamily (restrictFamily Ω (layerHull Ω Y)))
    (hDE : DEdgeless (oddQuotientFamily (restrictFamily Ω (layerHull Ω Y)))) :
    SectionLieType p f Ω (layerHull Ω Y) .PSL 3 ∨ SectionLieType p f Ω (layerHull Ω Y) .PSU 3 ∨
      SectionLieType p f Ω (layerHull Ω Y) .G2 0 ∨
        SectionLieType p f Ω (layerHull Ω Y) .trialityD4 0 := by
  have hS := genSection_layerHull hp hq hΩ hA Y
  rcases h6 hp hq _ hlt _ hS hne htop hDE with h | h | h | h
  · exact Or.inl (sectionLieType_of_hasLieType hS.gen h)
  · exact Or.inr (Or.inl (sectionLieType_of_hasLieType hS.gen h))
  · exact Or.inr (Or.inr (Or.inl (sectionLieType_of_hasLieType hS.gen h)))
  · exact Or.inr (Or.inr (Or.inr (sectionLieType_of_hasLieType hS.gen h)))

theorem sectionOrth_of_thm8' {n : ℕ} (h8 : Thm8SectBelow' p f n) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : ∀ L ∈ Ω, AEmpty Ω L) (Y : Subgroup G)
    (hlt : Nat.card (↥(layerHull Ω Y) ⧸ classicalInvolutionOddCore ↥(layerHull Ω Y)) < n)
    (hne : (oddQuotientFamily (restrictFamily Ω (layerHull Ω Y))).Nonempty)
    (hNE : ¬ DEdgeless (oddQuotientFamily (restrictFamily Ω (layerHull Ω Y))))
    (hNC : ¬ DConnected (oddQuotientFamily (restrictFamily Ω (layerHull Ω Y)))) :
    ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ SectionOrthType p f Ω (layerHull Ω Y) d ε := by
  have hS := genSection_layerHull hp hq hΩ hA Y
  obtain ⟨d, ε, hd, hd8, h⟩ := h8 hp hq _ hlt _ hS hne hNE hNC
  exact ⟨d, ε, hd, hd8, sectionOrthType_of_hasOrthType hS.gen h⟩

theorem layerSection_dichotomy {n : ℕ} (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h4 : Thm4Below p f n)
    (hΩ : HypOmegaMod p f Ω) (hA : ∀ L ∈ Ω, AEmpty Ω L) (Y : Subgroup G)
    (hlt : Nat.card (↥(layerHull Ω Y) ⧸ classicalInvolutionOddCore ↥(layerHull Ω Y)) < n) :
    DConnected (oddQuotientFamily (restrictFamily Ω (layerHull Ω Y))) ∨
      TransSection p f (oddQuotientFamily (restrictFamily Ω (layerHull Ω Y))) :=
  transSection_or_dConnected hp hq h4 hlt (genSection_layerHull hp hq hΩ hA Y)

end Layer

end CFSG.ClassicalInvolution.Asc77
