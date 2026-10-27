module

public import CFSG.ClassicalInvolution.Asc77.WP2Stand

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

structure Std7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStand p f Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  cex : ¬ ConcOrTF4 G

@[expose] def sigmaGen {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) : Subgroup G :=
  ⨆ M ∈ dComp Ω K, M

@[expose] def rLayer {G : Type} [Group G] (Ω : Set (Subgroup G)) (x : G) : Subgroup G :=
  ⨆ R ∈ RSet Ω, ⨆ (_ : R ≤ Subgroup.centralizer ({x} : Set G)), R

structure Hyp21 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G) : Prop where
  std : Std7 p f Ω K K' z
  hu : u ∈ K ⊔ K'
  hu2 : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ z
  hJ : J ∈ omegaOfSet Ω (twinSet Ω K)
  ht : IsUniqueInvolution J t
  htu : t * u = u * t
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  htW : t ∈ W

@[expose] def C21_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure {u, z}))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure {z, u, t} → IsElemAbelian2 A 2 →
          alphaOf A = alphaOf (Subgroup.closure {u, z})

@[expose] def C21_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      (∀ M ∈ dComp Ω K, M ≤ Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)) ∧
        ∀ c ∈ Subgroup.centralizer ({z} : Set G),
          conjSub c (alphaOf (Subgroup.closure {u, z}) ⊔ sigmaGen Ω K) =
            alphaOf (Subgroup.closure {u, z}) ⊔ sigmaGen Ω K

@[expose] def C21_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      dComp Ω K = dstarComp Ω K ∨ MuIsoWylD4 Ω W

@[expose] def C21_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      Subgroup.centralizer ({t * z} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G) ∧
        (rLayer Ω (t * z) ≤ alphaOf (Subgroup.closure {u, z}) ⊔ sigmaGen Ω K ∨
          (MuIsoWylD4 Ω W ∧
            (rLayer Ω (t * z) ≤ oddCoreOf (rLayer Ω (t * z)) ⊔
                (rLayer Ω (t * z) ⊓ Subgroup.normalizer (W : Set G)) ∨
              SectionOrthType p f Ω (rLayer Ω (t * z)) 8 true)))

@[expose] def C21_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      Subgroup.centralizer ({u} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G) ∧
        (rLayer Ω u ≤ alphaOf (Subgroup.closure {u, z}) ⊔ sigmaGen Ω K ∨
          (rLayer Ω u ≤ alphaOf (Subgroup.closure {u, z}) ⊔ rLayer Ω (t * z) ∧ MuIsoWylD4 Ω W ∧
            Subgroup.centralizer ({u} : Set G) ≤
              alphaOf (Subgroup.closure {u, z}) ⊔ Subgroup.centralizer ({t * z} : Set G)))

@[expose] def C21_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        ∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)

@[expose] def C21_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥

@[expose] def C21_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K

@[expose] def C21_E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        (∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) → MuIsoWylD4 Ω W → False

@[expose] def C21_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Std7 p f Ω K K' z → KPerp Ω K ≠ twinSet Ω K →
      ∃ (u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W

@[expose] def C21_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Std7 p f Ω K K' z → KPerp Ω K = twinSet Ω K

variable {p f}

theorem c21_false_of_steps (h13 : C21_13 p f) (h15 : C21_15 p f) (h16 : C21_16 p f)
    (h17 : C21_17 p f) (hE : C21_E p f) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
      (K K' : Subgroup G) (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G),
      Hyp21 p f Ω K K' z u J t W → False := by
  intro G _ _ _ Ω K K' z u J t W h
  have hα := h16 G Ω K K' z u J t W h
  have hD := h17 G Ω K K' z u J t W h
  obtain ⟨-, h13'⟩ := h13 G Ω K K' z u J t W h
  rw [hα, bot_sup_eq] at h13'
  rcases h13' with hle | ⟨hmu, -⟩
  · exact hD hle
  · exact hE G Ω K K' z u J t W h hα hD (h15 G Ω K K' z u J t W h hα hD) hmu

theorem c21_2_of_steps (hsetup : C21_setup p f)
    (hfalse : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
      (K K' : Subgroup G) (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G),
      Hyp21 p f Ω K K' z u J t W → False) : C21_2 p f := by
  intro G _ _ _ Ω K K' z hs
  by_contra hne
  obtain ⟨u, J, t, W, h⟩ := hsetup G Ω K K' z hs hne
  exact hfalse G Ω K K' z u J t W h

end CFSG.ClassicalInvolution.Asc77
