module

public import CFSG.ClassicalInvolution.AschTight.S19BStmt
public import CFSG.ClassicalInvolution.Q3.TL3S8BE2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

structure TightMemStdR (r : ℕ) (K : Subgroup G) (z : G) : Prop where
  three_le : 3 ≤ r
  isUniqueInvolution : IsUniqueInvolution K z
  le_centralizer : K ≤ Subgroup.centralizer ({z} : Set G)
  hypGen : HypOmegaGen (CoreAssembly.conjClass K)
  normEq : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G)
  edgeless : DEdgeless (CoreAssembly.conjClass K)
  natCard_rSet : ∀ {R : Subgroup G}, R ∈ RSet (CoreAssembly.conjClass K) → Nat.card R = 2 ^ r

structure TightSylowDataR (r : ℕ) (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G) : Prop where
  tight : TightMemStdR r K z
  mu : ¬ AllTypeTwo K z
  sylow : ∃ Q₀ : Sylow 2 K, (Q₀ : Subgroup K).map K.subtype ≤ (S : Subgroup G)
  hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)
  hW : W ∈ WSet (CoreAssembly.conjClass K)
  hWS : W ≤ (S : Subgroup G)

structure TightSylowDataTR (r : ℕ) (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G) : Prop extends TightSylowDataR r K z S W where
  memL : L ∈ CoreAssembly.conjClass K
  invL : IsUniqueInvolution L t
  ne : t ≠ z
  memV : V ∈ USet (CoreAssembly.conjClass K)
  leW : V ≤ W
  memT : t ∈ V

structure StdR (r : ℕ) {G : Type} [Group G] [Finite G] (R : Subgroup G) (S : Sylow 2 R) (t : G)
    (T : Sylow 2 G) : Prop where
  datum : TightDatum R S t
  quat : Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))
  three_le : 3 ≤ r
  edgeless : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R))
  notFour : ¬ TwoSubgroupsFourGenerated (genFittingFStar G)
  hST : (S : Subgroup R).map R.subtype ≤ (T : Subgroup G)
  hTt : (T : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G)

@[expose] def TightC19_11bSR (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G) (W L : Subgroup G) (t' : G)
      (V : Subgroup G), StdR r R S t T → TightSylowDataTR r (tightCore R) t T W L t' V →
      (T : Subgroup G) ⊓
          Subgroup.centralizer (((T : Subgroup G) ⊓ tightCore R : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L = ⊥

@[expose] def TightF1SR (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G) (W L : Subgroup G) (t' : G)
      (V : Subgroup G), StdR r R S t T → TightSylowDataTR r (tightCore R) t T W L t' V →
      ∀ x ∈ S19B.sec19BPrime (tightCore R) T W L, x ≠ 1 → ∀ g : G,
        g * t * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) →
          ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * t * c⁻¹ = g * t * g⁻¹

@[expose] def TightEndGameSR (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G), StdR r R S t T →
    ∀ B : Subgroup G, B ≤ (T : Subgroup G) → B ≠ ⊥ →
      fusionStronglyClosed (B : Set G) (T : Subgroup G) → B ≤ centralizerModOdd ⊤ (tightCore R) →
      t ∈ Subgroup.centralizer (B : Set G) →
      (∃ g ∈ Subgroup.centralizer (B : Set G),
        g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹)) → False

structure SylowPartsR (r : ℕ) : Prop where
  bundle : ∀ {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G},
    TightDatum R S t → Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) →
    Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) → ∀ {T : Subgroup G},
    IsSylow2Of T (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)) →
    IsSylow2Of T ⊤ → ∃ T' : Sylow 2 G, (T' : Subgroup G) = T ∧ StdR r R S t T'
  w69 : ∀ {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
    {T : Sylow 2 G}, StdR r R S t T →
    ∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), W ≤ (T : Subgroup G)
  muZ2OrS3 : ∀ {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
    {T : Sylow 2 G}, StdR r R S t T → ∀ {W : Subgroup G},
    W ∈ WSet (CoreAssembly.conjClass (tightCore R)) →
    MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W ∨
      MuIsoS3 (CoreAssembly.conjClass (tightCore R)) W
  not_muIsoZ2 : ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) → GoldschmidtB3Tmp →
    ∀ {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G}, StdR r R S t T →
    ∀ {W : Subgroup G}, W ∈ WSet (CoreAssembly.conjClass (tightCore R)) →
      ¬ MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W
  not_allTypeTwo : ∀ {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
    {T : Sylow 2 G}, StdR r R S t T → ∀ {W : Subgroup G},
    W ∈ WSet (CoreAssembly.conjClass (tightCore R)) →
    MuIsoS3 (CoreAssembly.conjClass (tightCore R)) W → ¬ AllTypeTwo (tightCore R) t
  e2_of_core : TightC19_11bSR r →
    ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G}, StdR r R S t T →
      ¬ AllTypeTwo (tightCore R) t → TightE2Prime (tightCore R) T

end CFSG.CGT.PushingUpLit.SolKNA.R4
