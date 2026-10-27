module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

structure EStand {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W : Subgroup G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  hyp : HypOmegaMod p f Ω
  below : CITBelowU p f (Nat.card G)
  mem : K ∈ Ω
  aEmpty : AEmpty Ω K
  twin : ∃ K' ∈ twinSet Ω K, K' ≠ K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

@[expose] def CentralizersTwinPerp {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K H : Subgroup G) : Prop :=
  ∀ L ∈ twinSet Ω K, ∀ J ∈ KPerp Ω L, ∀ a ∈ L ⊔ J, a ≠ 1 → a * a = 1 →
    Subgroup.centralizer ({a} : Set G) ≤ H

@[expose] def CentralizersSylowPairs {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K H : Subgroup G) : Prop :=
  ∀ L ∈ twinSet Ω K, ∀ J ∈ KPerp Ω L, ∀ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω → R₁ ≤ L →
    R₂ ∈ RSet Ω → R₂ ≤ J → (Commutes R₁ R₂ ∨ R₂ = R₁) → ∀ a ∈ R₁ ⊔ R₂, a ≠ 1 → a * a = 1 →
      Subgroup.centralizer ({a} : Set G) ≤ H

theorem CentralizersTwinPerp.toSylowPairs {G : Type} [Group G] {Ω : Set (Subgroup G)}
    {K H : Subgroup G} (h : CentralizersTwinPerp Ω K H) : CentralizersSylowPairs Ω K H :=
  fun L hL J hJ _ _ _ h₁L _ h₂J _ a ha ha1 ha2 =>
    h L hL J hJ a (sup_le_sup h₁L h₂J ha) ha1 ha2

theorem CentralizersSylowPairs.of_twin {G : Type} [Group G] {Ω : Set (Subgroup G)}
    {K K' H : Subgroup G} (h : CentralizersSylowPairs Ω K H) (hK' : K' ∈ twinSet Ω K) :
    CentralizersSylowPairs Ω K' H := by
  intro L hL
  obtain ⟨hLΩ, z, hz, hzL⟩ := hL
  obtain ⟨-, z', hz', hz'K'⟩ := hK'
  have e : z = z' := hz.eq hz'K'
  exact h L ⟨hLΩ, z', hz', e ▸ hzL⟩

structure EHyp {G : Type} [Group G] (Ω : Set (Subgroup G)) (K W H : Subgroup G) : Prop where
  trans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J
  cent : CentralizersSylowPairs Ω K H

@[expose] def ThmEBelow (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
    ∀ (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G) (R W H : Subgroup G),
      EStand p f Ω K S R W → EHyp Ω K W H → H = ⊤

structure MinCex {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) : Prop where
  stand : EStand p f Ω K S R W
  hyp : EHyp Ω K W H
  proper : H ≠ ⊤
  minimal : ThmEBelow p f (Nat.card G)

@[expose] def ThmEWithSylow : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
      (R W H : Subgroup G), EStand p f Ω K S R W → EHyp Ω K W H → H = ⊤

@[expose] def MinCexFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H → False

theorem thmEWithSylow_of_minCexFalse (h : MinCexFalse p f) : ThmEWithSylow p f := by
  have key : ∀ n, ThmEBelow p f n := by
    intro n
    induction n with
    | zero =>
      intro G _ _ hG
      exact absurd hG (by omega)
    | succ n ih =>
      intro G _ _ hG Ω K S R W H hst hH
      by_cases hn : Nat.card G < n
      · exact ih G hn Ω K S R W H hst hH
      · have hGn : Nat.card G = n := by omega
        by_contra hne
        exact h G Ω K S R W H ⟨hst, hH, hne, hGn ▸ ih⟩
  intro _ _ G _ _ Ω K S R W H hst hH
  exact key (Nat.card G + 1) G (Nat.lt_succ_self _) Ω K S R W H hst hH

@[expose] def E18_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      (∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H) ∧ ∃ J ∈ Ω, J ∉ dstarComp Ω K

@[expose] def E18_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ u ∈ K, orderOf u = 4 → ∀ g : G, g * u * g⁻¹ ∈ H → g ∈ H

@[expose] def E18_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H → ∀ J ∈ Ω, ∃ g : G, conjSub g K = J

@[expose] def E18_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → R' ≤ (S : Subgroup G) →
        ∀ X : Subgroup G, R ⊔ R' ≤ X → X ≠ ⊤ → X ≤ H

@[expose] def E18_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H → (⨆ J ∈ Ω, J) = ⊤

@[expose] def E18_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      classicalInvolutionOddCore G = ⊥ ∧
        ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
          Subgroup.centralizer (F : Set G) = ⊥

@[expose] def E18_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ a : G, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H →
        ∀ g : G, g * a * g⁻¹ ∈ H → ∃ h ∈ H, h * a * h⁻¹ = g * a * g⁻¹

@[expose] def E18_8z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → FixesUniqueCoset z H

@[expose] def E18_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → ∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) →
        h⁻¹ * z * h ≠ z → z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z →
          FixesUniqueCoset (z * (h⁻¹ * z * h)) H

@[expose] def E18_zW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H → ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W

@[expose] def E18_end : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      (∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
        Subgroup.centralizer (F : Set G) = ⊥) →
      ∀ z : G, IsUniqueInvolution K z → FixesUniqueCoset z H →
        (∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) → h⁻¹ * z * h ≠ z →
          z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z → FixesUniqueCoset (z * (h⁻¹ * z * h)) H) →
        False

theorem minCexFalse_of_steps (h6 : E18_6 p f) (h8 : E18_8z p f) (h9 : E18_9 p f)
    (hend : E18_end p f) : MinCexFalse p f := by
  intro G _ _ Ω K S R W H c
  obtain ⟨K', ⟨-, z, hz1, -⟩, -⟩ := c.stand.twin
  obtain ⟨-, hF⟩ := h6 G Ω K S R W H c
  have hzc : FixesUniqueCoset z H := h8 G Ω K S R W H c z hz1
  exact hend G Ω K S R W H c hF z hz1 hzc fun h h1 h2 h3 => h9 G Ω K S R W H c z hz1 h h1 h2 h3

@[expose] def Thm4Below (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
      HypOmegaMod p f Ω → classicalInvolutionOddCore G = ⊥ → (∀ K ∈ Ω, AEmpty Ω K) →
        ∀ K ∈ Ω, ∀ J ∈ Ω, (¬ ∃ g : G, conjSub g K = J) → Commutes K J

@[expose] def Thm2 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      classicalInvolutionOddCore G = ⊥ → (⨆ J ∈ Ω, J) = ⊤ → ∀ K ∈ Ω,
        (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
          ∀ z : G, IsUniqueInvolution K z → (∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ z ∈ N) →
            K.Normal

@[expose] def Thm2Below (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
      HypOmegaMod p f Ω → classicalInvolutionOddCore G = ⊥ → (⨆ J ∈ Ω, J) = ⊤ → ∀ K ∈ Ω,
        (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
          ∀ z : G, IsUniqueInvolution K z → (∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ z ∈ N) →
            K.Normal

@[expose] def IHInterface : Prop :=
  ∀ n : ℕ, CITBelowU p f n → Thm4Below p f n ∧ Thm2Below p f n

end CFSG.ClassicalInvolution.Asc77
