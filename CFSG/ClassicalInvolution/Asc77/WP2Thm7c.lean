module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm7b

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def rLayerSub {G : Type} [Group G] (Ω : Set (Subgroup G)) (A : Subgroup G) : Subgroup G :=
  ⨆ R ∈ RSet Ω, ⨆ (_ : R ≤ Subgroup.centralizer (A : Set G)), R

@[expose] def IsFAut {G : Type} [Group G] (K : Subgroup G) (a : G) : Prop :=
  a ∈ Subgroup.normalizer (K : Set G) ∧ (∀ k ∈ K, a * a * k = k * (a * a)) ∧
    ∃ Q R : Subgroup G, IsSylow2In Q (K ⊓ Subgroup.centralizer ({a} : Set G)) ∧ IsQuatSub Q ∧
      IsSylow2In R K ∧ Nat.card ↥R = 2 * Nat.card ↥Q

@[expose] def Wz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → ∀ z : G, IsUniqueInvolution K z → ∃ W ∈ WSet Ω, z ∈ W

structure Hyp24 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Prop where
  std : Hyp23 p f Ω K K' z
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  hS4 : MuIsoS4 Ω W
  hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥
  hWS : W ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hR' : R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hu : u ∈ K ⊔ K' ∧ u ∈ W ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z

@[expose] def C24_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 p f Ω K K' W S R R' z u →
      ∃ g ∈ Subgroup.normalizer (W : Set G), g⁻¹ * z * g = u

@[expose] def C24_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 p f Ω K K' W S R R' z u → Nat.card ↥R = 8 →
      ¬ (S : Subgroup G) ≤ MGrp Ω W ∨ ConcOrTF4 G

@[expose] def C24_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 p f Ω K K' W S R R' z u → ∀ g : G, g⁻¹ * z * g = u →
      (Subgroup.centralizer (R : Set G) ⊓ Subgroup.normalizer ((conjSub g⁻¹ K : Subgroup G) : Set G)
          ⊓ (S : Subgroup G)) ⊓ Subgroup.centralizer (R' : Set G) ≠ Subgroup.zpowers z

@[expose] def C24_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 p f Ω K K' W S R R' z u → ∀ g : G, g⁻¹ * z * g = u → ∀ d x : G,
      d ∈ (Subgroup.centralizer (R : Set G) ⊓
        Subgroup.normalizer ((conjSub g⁻¹ K : Subgroup G) : Set G) ⊓ (S : Subgroup G)) ⊓
        Subgroup.centralizer (R' : Set G) → orderOf d = 4 → x ∈ R' ⊓ W → orderOf x = 4 →
        (if piSign p f then SectionLieType p f Ω (rLayer Ω (d * x)) .PSL 3
          else SectionLieType p f Ω (rLayer Ω (d * x)) .PSU 3) ∧
        rLayer Ω (d * x) ⊔ K' = ⊤

@[expose] def C24_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 p f Ω K K' W S R R' z u → 8 < Nat.card ↥R

@[expose] def C24_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 p f Ω K K' W S R R' z u → ConcOrTF4 G

@[expose] def C24_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥ →
        ∃ (S : Sylow 2 G) (R R' : Subgroup G) (u : G), Hyp24 p f Ω K K' W S R R' z u

@[expose] def C24_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥ → ConcOrTF4 G

variable {p f}

theorem c24_1_of_steps (hsetup : C24_setup p f) (h10 : C24_10 p f) : C24_1 p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4 hZ
  obtain ⟨S, R, R', u, hyp⟩ := hsetup G Ω K K' z hs W hW hzW hS4 hZ
  exact h10 G Ω K K' W S R R' z u hyp

variable (p f)

structure Hyp25 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G) : Prop where
  std : Hyp23 p f Ω K K' z
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  hE4 : MuIsoE4 Ω W
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hR' : R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hRS : ∀ X ∈ RSet Ω, X ≤ (S : Subgroup G) → X = R ∨ X = R'
  hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s
  ht : t ∈ (S : Subgroup G) ∧ t ≠ z ∧ ∃ g : G, g * z * g⁻¹ = t
  hu₁ : u₁ ∈ R ∧ orderOf u₁ = 4 ∧ ∀ r ∈ R, r * u₁ * r⁻¹ ∈ Subgroup.zpowers u₁
  hu₂ : u₂ ∈ R' ∧ orderOf u₂ = 4 ∧ ∀ r ∈ R', r * u₂ * r⁻¹ ∈ Subgroup.zpowers u₂

@[expose] def C25_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ g : G, g * z * g⁻¹ = t →
      ∀ x ∈ conjSub g⁻¹ K, orderOf x = 4 → x * z ≠ z * x

@[expose] def C25_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∃ t' ∈ (S : Subgroup G), (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' ∧
        (∃ h : G, h * (t' * z) * h⁻¹ = u₁ * u₂ ∨ h * (t' * z) * h⁻¹ = u₁ * u₂ * z) ∧
        ¬ ∃ h : G, h * (t' * z) * h⁻¹ = z

@[expose] def C25_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ A : Subgroup G, IsElemAbelian2 A 2 → z ∈ A →
      (∀ a ∈ A, a * t = t * a) → ∃ a ∈ A, a ≠ 1 ∧ z ∉ zStarOf (Subgroup.centralizer ({a} : Set G))

@[expose] def C25_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ A : Subgroup G, z ∈ A → A ≤ (S : Subgroup G) →
      (∀ s ∈ (S : Subgroup G), conjSub s A = A) →
      (∀ a ∈ A, a ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))) → A = Subgroup.zpowers z

@[expose] def C25_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) ≤ 4 ∧
        (Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 →
          ∃ a : G, Subgroup.closure {a, z} =
              (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
            z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) ∧
            z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G)))

@[expose] def C25_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
        Subgroup.zpowers z

@[expose] def C25_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G),
      a * a ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) → IsFAut R a →
        ∃ b ∈ (fun r : G => a * r) '' (R : Set G), b * b = 1 ∧ IsFAut R b

@[expose] def C25_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      (S : Subgroup G) ⊓ Subgroup.centralizer (R' : Set G) = R ∨
        (Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (R' : Set G)) = 2 * Nat.card ↥R ∧
          (IsQuatSub ((S : Subgroup G) ⊓ Subgroup.centralizer (R' : Set G)) ∨
            IsSemidihedral ((S : Subgroup G) ⊓ Subgroup.centralizer (R' : Set G))))

@[expose] def C25_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a

@[expose] def C25_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      (∀ s ∈ (S : Subgroup G), conjSub s (R ⊔ R') = R ⊔ R') ∧
        (∀ s ∈ (S : Subgroup G), s * s ∈ R ⊔ R') ∧
        (Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R') ∨
          Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R'))

@[expose] def C25_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') ∨ ConcOrTF4 G

@[expose] def C25_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') → ConcOrTF4 G

@[expose] def C25_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W →
      ∃ (S : Sylow 2 G) (R R' : Subgroup G) (t u₁ u₂ : G), Hyp25 p f Ω K K' W S R R' z t u₁ u₂

@[expose] def C25_E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W → ConcOrTF4 G

variable {p f}

theorem c25_E4_of_steps (hsetup : C25_setup p f) (h19 : C25_19 p f) (h21 : C25_21 p f) :
    C25_E4 p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW hE4
  obtain ⟨S, R, R', t, u₁, u₂, hyp⟩ := hsetup G Ω K K' z hs W hW hzW hE4
  rcases h19 G Ω K K' W S R R' z t u₁ u₂ hyp with h | h
  · exact h21 G Ω K K' W S R R' z t u₁ u₂ hyp h
  · exact h

theorem thm7A_of_steps (hWz : Wz p f) (h21 : C21_2 p f) (h22 : C22_1 p f) (h231 : C23_1 p f)
    (h233 : C23_3 p f) (h24 : C24_1 p f) (h25 : C25_E4 p f) : Thm7A p f := by
  intro G _ _ _ Ω K hs ⟨K', hK'tw, hK'ne⟩ hdisc
  by_cases hc : ConcOrTF4 G
  · exact hc
  obtain ⟨z, hz⟩ := hs.hyp.classical K hs.mem
  have hU := ConnectedA2.isUniqueInvolution_of_isClassicalMember hs.odd hs.five hz
  have hstd : Std7 p f Ω K K' z := ⟨hs, hdisc, hU, hK'tw, hK'ne, hc⟩
  have hperp : KPerp Ω K = twinSet Ω K := h21 G Ω K K' z hstd
  rcases h22 G Ω K K' z hstd hperp with hP | hexit
  · have hyp23 : Hyp23 p f Ω K K' z := ⟨hstd, hP⟩
    obtain ⟨W, hW, hzW⟩ := hWz G Ω K hs z hU
    rcases h231 G Ω K K' z hyp23 W hW with hE4 | hS4
    · exact h25 G Ω K K' z hyp23 W hW hzW hE4
    · rcases h233 G Ω K K' z hyp23 W hW hzW hS4 with hZ | hexit
      · exact h24 G Ω K K' z hyp23 W hW hzW hS4 hZ
      · exact hexit
  · exact hexit

end CFSG.ClassicalInvolution.Asc77
