module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm7a

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

structure Hyp22 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' K₃ : Subgroup G)
    (z u₁ u₂ u₃ : G) : Prop where
  std : Std7 p f Ω K K' z
  perp : KPerp Ω K = twinSet Ω K
  hK₃ : K₃ ∈ twinSet Ω K
  hK₃K : K₃ ≠ K
  hK₃K' : K₃ ≠ K'
  hu₁ : u₁ ∈ K ∧ orderOf u₁ = 4
  hu₂ : u₂ ∈ K' ∧ orderOf u₂ = 4
  hu₃ : u₃ ∈ K₃ ∧ orderOf u₃ = 4
  hB : IsElemAbelian2 (Subgroup.closure {u₁ * u₂, z, u₂ * u₃}) 3

@[expose] def C22_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure {u₁ * u₂, z}))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure {u₁ * u₂, z, u₂ * u₃} → IsElemAbelian2 A 2 →
          alphaOf A = alphaOf (Subgroup.closure {u₁ * u₂, z})

@[expose] def C22_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W

@[expose] def C22_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      alphaOf (Subgroup.closure {u₁ * u₂, z}) = ⊥

@[expose] def C22_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      SectionOrthType p f Ω (rLayer Ω (u₁ * u₂)) 6 (piSign p f) ∧
        (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤

@[expose] def C22_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ → ConcOrTF4 G

@[expose] def C22_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Std7 p f Ω K K' z → KPerp Ω K = twinSet Ω K → KPerp Ω K ≠ {K, K'} →
      ∃ (K₃ : Subgroup G) (u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃

@[expose] def C22_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Std7 p f Ω K K' z → KPerp Ω K = twinSet Ω K → KPerp Ω K = {K, K'} ∨ ConcOrTF4 G

variable {p f}

theorem c22_1_of_steps (hsetup : C22_setup p f) (h9 : C22_9 p f) : C22_1 p f := by
  intro G _ _ _ Ω K K' z hs hperp
  by_cases h : KPerp Ω K = {K, K'}
  · exact Or.inl h
  · obtain ⟨K₃, u₁, u₂, u₃, hyp⟩ := hsetup G Ω K K' z hs hperp h
    exact Or.inr (h9 G Ω K K' K₃ z u₁ u₂ u₃ hyp)

variable (p f)

@[expose] def Hyp23 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop :=
  Std7 p f Ω K K' z ∧ KPerp Ω K = {K, K'}

@[expose] def C23_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 p f Ω K K' z → ∀ W ∈ WSet Ω, MuIsoE4 Ω W ∨ MuIsoS4 Ω W

@[expose] def C23_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → ∀ u ∈ K ⊔ K', u ∈ W → u ≠ 1 → u ≠ z →
      u * u = 1 →
      Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤

@[expose] def C23_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥ ∨ ConcOrTF4 G

structure Hyp23b {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (z u e g : G) : Prop where
  std : Hyp23 p f Ω K K' z
  hW : W ∈ WSet Ω
  hS4 : MuIsoS4 Ω W
  hzW : z ∈ W
  hu : u ∈ K ⊔ K'
  huW : u ∈ W
  hu2 : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ z
  he : Subgroup.closure {e} = W ⊓ centerIn (Subgroup.normalizer (W : Set G))
  he1 : e ≠ 1
  he2 : e * e = 1
  hg : g ∈ ⨆ R ∈ DSet Ω W, R
  hgt : g * z * g⁻¹ = u * e

@[expose] def C23_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      rLayer Ω e ≤ oddCoreOf (rLayer Ω e) ⊔ (rLayer Ω e ⊓ Subgroup.normalizer (W : Set G)) ∨
        SectionOrthType p f Ω (rLayer Ω e) 6 (piSign p f)

@[expose] def C23_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      (Odd (Nat.card ↥(alphaOf (Subgroup.closure {u, z}))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure {u * e, u, z} → IsElemAbelian2 A 2 →
          alphaOf A = alphaOf (Subgroup.closure {u, z})) ∧
      (∀ WY ∈ WSet (restrictFamily Ω (rLayer Ω u)), MuIsoE4 (restrictFamily Ω (rLayer Ω u)) WY) ∧
      (u * e ∈ zStarOf (rLayer Ω u) ∨ SectionOrthType p f Ω (rLayer Ω u) 5 true ∨
        SectionOrthType p f Ω (rLayer Ω u) 6 (!piSign p f))

@[expose] def C23_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      ¬ rLayer Ω e ≤ oddCoreOf (rLayer Ω e) ⊔ (rLayer Ω e ⊓ Subgroup.normalizer (W : Set G))

@[expose] def C23_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) ∧
      SectionOrthType p f Ω (rLayer Ω e) 6 (piSign p f) ∧
      (SectionOrthType p f Ω (rLayer Ω u) 5 true ∨
        SectionOrthType p f Ω (rLayer Ω u) 6 (!piSign p f))

@[expose] def C23_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g → ConcOrTF4 G

@[expose] def C23_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 p f Ω K K' z → ∀ W ∈ WSet Ω, MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) ≠ ⊥ → z ∈ W →
        ∃ (u e g : G), Hyp23b p f Ω K K' W z u e g

variable {p f}

theorem c23_3_of_steps (hsetup : C23_setup p f) (h10 : C23_10 p f) : C23_3 p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4
  by_cases h : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥
  · exact Or.inl h
  · obtain ⟨u, e, g, hyp⟩ := hsetup G Ω K K' z hs W hW hS4 h hzW
    exact Or.inr (h10 G Ω K K' W z u e g hyp)

end CFSG.ClassicalInvolution.Asc77
