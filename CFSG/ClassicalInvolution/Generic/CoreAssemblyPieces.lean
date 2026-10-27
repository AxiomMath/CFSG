module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyShape
public import CFSG.ClassicalInvolution.SmallCases.Partition
public import CFSG.Timmesfeld.RankTwo.LevisSpin
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyBase
public import CFSG.ClassicalInvolution.Generic.StepQuasisimple

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

structure RouteDSetup (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (K : Subgroup G) (z : G) :
    Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  cls : IsClassicalMember p f K z
  inClass : InClass p f (conjClass K)
  conn : RouteD.DeltaConnected (conjClass K)
  exact : ExactMembers (conjClass K)
  p1 : LocalOddCentral (conjClass K) {z}
  ih : LocalLieSystems p f (conjClass K)
  below : CITBelowU p f (Nat.card G)

theorem mk_routeDSetup [Finite G] [IsSimpleGroup G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hconn : RouteD.DeltaConnected (conjClass K))
    (hex : ExactMembers (conjClass K)) (hp1 : LocalOddCentral (conjClass K) {z}) :
    RouteDSetup p f K z :=
  { odd := hp2, five := hq, cls := hz, inClass := inClass_conjugates hz, conn := hconn,
    exact := hex, p1 := hp1,
    ih := localLieSystems_of_citBelowU (inClass_conjugates hz) hBelow, below := hBelow }

@[expose] def IndepTriple (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) : Prop :=
  ∃ (K : Fin 3 → Subgroup G) (z : Fin 3 → G),
    (∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i)) ∧ (∀ i j, i ≠ j → Commutes (K i) (K j)) ∧
    CFSG.Open.IsElemAbelian 2 (Subgroup.closure (Set.range z)) ∧
    Nat.card (Subgroup.closure (Set.range z)) = 8

@[expose] def BootData (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) : Prop :=
  ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G), L₀ ∈ Ω ∧ IsClassicalMember p f L₀ z₀ ∧
    CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 8 ∧ z₀ ∈ A ∧
    L₀ ≤ Subgroup.centralizer (A : Set G)

@[expose] def BootTriple (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → RouteD.DeltaConnected (conjClass K) →
      IndepTriple p f (conjClass K) →
      ExactMembers (conjClass K) ∧ LocalOddCentral (conjClass K) {z}

@[expose] def BootNoTriple (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → RouteD.DeltaConnected (conjClass K) →
      BootData p f (conjClass K) → ¬ IndepTriple p f (conjClass K) →
      ExactMembers (conjClass K) ∧ LocalOddCentral (conjClass K) {z}

theorem bootData_of_hasEFrameRank4 [Finite G] [IsSimpleGroup G]
    {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (h : HasEFrameRank4 K) : BootData p f (conjClass K) := by
  obtain ⟨E, E₀, L₀, z₀, t, hL₀, hz₀, -, -, -, hE₀, hcard, hz₀E, -, -, -, hcent, -, -, -⟩ :=
    HasEFrameRank4.exists_data h
  rw [conjugateSet_eq_range] at hL₀
  obtain ⟨g, rfl⟩ := hL₀
  have hconj := hz.conj g
  have hzz : g * z * g⁻¹ = z₀ := by
    have hsq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      have h2 := hconj.orderOf_eq_two
      have h3 : (g * z * g⁻¹) ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
      simpa [pow_two] using h3
    rcases hz₀.unique _ (conj_mem_conjSub hz.mem) hsq with h1 | h1
    · exact absurd h1 (fun e => by
        have := hconj.orderOf_eq_two
        rw [e, orderOf_one] at this
        omega)
    · exact h1
  refine ⟨_, z₀, E₀, ⟨g, rfl⟩, ?_, hE₀, hcard, hz₀E, hcent⟩
  rw [← hzz]
  exact hconj

@[expose] def ShapePiece (p f : ℕ) [Fact p.Prime] (a : ℕ) (tY : StatedLieTag) (nY : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f a tY nY (conjClass K) z → LieSystem p f G (conjClass K)

@[expose] def MultiPiece (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      MultiShape p f (conjClass K) z → LieSystem p f G (conjClass K)

@[expose] def RowPiece (p f : ℕ) [Fact p.Prime] (S : ℕ → StatedLieTag → ℕ → Prop) : Prop :=
  ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), S a t n → ShapePiece p f a t n

@[expose] def ShapeSL7 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 1 ∧ t = .PSL ∧ 7 ≤ n
@[expose] def ShapeSL6 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 1 ∧ t = .PSL ∧ n = 6
@[expose] def ShapeSLs (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .PSL ∧ 3 ≤ n ∧ n ≤ 5
@[expose] def ShapeSU7 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 1 ∧ t = .PSU ∧ 7 ≤ n
@[expose] def ShapeSU6 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 1 ∧ t = .PSU ∧ n = 6
@[expose] def ShapeSUs (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .PSU ∧ 3 ≤ n ∧ n ≤ 5
@[expose] def ShapeSp4 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 1 ∧ t = .PSp ∧ 4 ≤ n
@[expose] def ShapeSp3 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 1 ∧ t = .PSp ∧ n = 3
@[expose] def ShapeE7 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .POmegaPlus ∧ n = 6
@[expose] def ShapeE8 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 1 ∧ t = .E7 ∧ n = 0
@[expose] def ShapeTwinD (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 2 ∧ t = .POmegaPlus ∧ 4 ≤ n
@[expose] def ShapeTwinSL4 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 2 ∧ t = .PSL ∧ n = 4
@[expose] def ShapeTwinB (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 2 ∧ t = .POmegaOdd ∧ 3 ≤ n
@[expose] def ShapeTwinSp2 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 2 ∧ t = .PSp ∧ n = 2
@[expose] def ShapeTwinTD (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 2 ∧ t = .POmegaMinus ∧ 4 ≤ n
@[expose] def ShapeTwinSU4 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 2 ∧ t = .PSU ∧ n = 4

@[expose] def ShapeTable (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  ShapeSL7 a t n ∨ ShapeSL6 a t n ∨ ShapeSLs a t n ∨ ShapeSU7 a t n ∨ ShapeSU6 a t n ∨
    ShapeSUs a t n ∨ ShapeSp4 a t n ∨ ShapeSp3 a t n ∨ ShapeE7 a t n ∨ ShapeE8 a t n ∨
    ShapeTwinD a t n ∨ ShapeTwinSL4 a t n ∨ ShapeTwinB a t n ∨ ShapeTwinSp2 a t n ∨
    ShapeTwinTD a t n ∨ ShapeTwinSU4 a t n

@[expose] def ShapeAllA1 (_a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := t = .PSL ∧ n = 2

@[expose] def ShapeNoA1 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 0 ∧ ¬ (t = .PSL ∧ n = 2)

@[expose] def ShapeExotic (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  1 ≤ a ∧ ¬ (t = .PSL ∧ n = 2) ∧ ¬ ShapeTable a t n

@[expose] def ShapeExcluded (p f : ℕ) [Fact p.Prime] : Prop :=
  RowPiece p f fun a t n => ¬ ShapeTable a t n

@[expose] def PieceAllA1 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeAllA1
@[expose] def PieceNoA1 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeNoA1
@[expose] def PieceExotic (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeExotic

theorem shapeExcluded_of_pieces (h1 : PieceAllA1 p f) (h2 : PieceNoA1 p f)
    (h3 : PieceExotic p f) : ShapeExcluded p f := by
  intro a t n hn
  by_cases hA : t = .PSL ∧ n = 2
  · exact h1 a t n hA
  · by_cases ha : a = 0
    · exact h2 a t n ⟨ha, hA⟩
    · exact h3 a t n ⟨by omega, hA, hn⟩

@[expose] def PieceSL7 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeSL7
@[expose] def PieceSL6 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeSL6
@[expose] def PieceSU7 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeSU7
@[expose] def PieceSU6 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeSU6
@[expose] def PieceSUs (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeSUs
@[expose] def PieceSp3 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeSp3
@[expose] def PieceE7 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeE7
@[expose] def PieceE8 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeE8
@[expose] def PieceTwinSL4 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeTwinSL4
@[expose] def PieceTwinB (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeTwinB
@[expose] def PieceTwinSp2 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeTwinSp2
@[expose] def PieceTwinTD (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeTwinTD
@[expose] def PieceTwinSU4 (p f : ℕ) [Fact p.Prime] : Prop := RowPiece p f ShapeTwinSU4

@[expose] def ChainPieceSLs (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, 2 ≤ m → m ≤ 4 →
      LocalShapeA p f m (conjClass K) z →
      ∃ U : Fin (m + 2) → Subgroup G, (∀ i, U i ∈ conjClass K) ∧
        (∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
        ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
          ∃ W, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair (GaloisField p f) W
            (U i) (U j)

@[expose] def ChainPieceTwinD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ n : ℕ, 6 ≤ n →
      LocalShapeT p f 2 .POmegaPlus (n - 2) (conjClass K) z →
      ∃ U : Fin n → Subgroup G, (∀ k, U k ∈ conjClass K) ∧
        (∀ i j : Fin n, i ≠ j → ¬ CFSG.Timmesfeld.edgeD n i j → ¬ CFSG.Timmesfeld.edgeD n j i →
          Commutes (U i) (U j)) ∧
        ∀ i j : Fin n, CFSG.Timmesfeld.edgeD n i j →
          ∃ W, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair (GaloisField p f) W
            (U i) (U j)

@[expose] def PieceSp4P1 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, 4 ≤ m →
      LocalShapeT p f 1 .PSp m (conjClass K) z →
      ∀ x : G, orderOf x = 2 → LocalOddCentral (conjClass K) {x}

@[expose] def PieceSp4NoOther (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, 4 ≤ m →
      LocalShapeT p f 1 .PSp m (conjClass K) z →
      ∀ x : G, orderOf x = 2 →
        ∀ (D : LieSystemData p f (locQuot (conjClass K) x) (locFamily (conjClass K) x))
          (c : Fin D.card), (D.tag c = .PSL ∧ D.rank c = 2) ∨ D.tag c = .PSp

@[expose] def SmallDisconnected (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G → ¬ CFSG.ClassicalInvolution.DeltaConnected K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def SmallConnectedA2 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G → CFSG.ClassicalInvolution.DeltaConnected K →
      ¬ BootData p f (conjClass K) → A2Configuration z K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def SmallTypeC (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G → CFSG.ClassicalInvolution.DeltaConnected K →
      ¬ BootData p f (conjClass K) → ¬ A2Configuration z K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def FrameConnected (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → HasEFrameRank4 K →
      CFSG.ClassicalInvolution.DeltaConnected K

@[expose] def SmallUpgrade (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      (CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11) →
      LieSystem p f G (conjClass K)

end CFSG.ClassicalInvolution.Generic.CoreAssembly
