module

public import CFSG.ClassicalInvolution.Q3.Q3PBranch

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank

theorem not_subset_center_of_ne_one {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : z ≠ 1) :
    ¬ ({z} : Set G) ⊆ Subgroup.center G := by
  intro h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h1
  · exact hz (by simpa [h0] using h (Set.mem_singleton z))
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := by rw [h1]; trivial
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

section Shapes


@[expose] def IsA1Comp3 {ι X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) : Prop :=
  D.kind i = CompData.sl23

@[expose] def MultiShape3 {G : Type} [Group G] (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)),
    ∃ i j : ι, i ≠ j ∧ ¬ IsA1Comp3 D i ∧ ¬ IsA1Comp3 D j

@[expose] def LocalShapeC3 {G : Type} [Group G] (a : ℕ) (c : CompData) (Ω : Set (Subgroup G))
    (x : G) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)),
    Nat.card ι = a + 1 ∧ ∃ i₁ : ι, D.kind i₁ = c ∧ ∀ i, i ≠ i₁ → D.kind i = CompData.sl23

theorem shape_dichotomy3 {ι : Type} [Finite ι] [Nonempty ι] {X : Type} [Group X]
    {Φ : Set (Subgroup X)} (D : LieSystemData3 ι X Φ) :
    (∃ i j : ι, i ≠ j ∧ ¬ IsA1Comp3 D i ∧ ¬ IsA1Comp3 D j) ∨
      ∃ (a : ℕ) (c : CompData), Nat.card ι = a + 1 ∧
        ∃ i₁ : ι, D.kind i₁ = c ∧ ∀ i, i ≠ i₁ → D.kind i = CompData.sl23 := by
  have hpos : 0 < Nat.card ι := Nat.card_pos
  by_cases h : ∃ i j : ι, i ≠ j ∧ ¬ IsA1Comp3 D i ∧ ¬ IsA1Comp3 D j
  · exact Or.inl h
  · right
    push Not at h
    by_cases hex : ∃ i, ¬ IsA1Comp3 D i
    · obtain ⟨i₁, hi₁⟩ := hex
      exact ⟨Nat.card ι - 1, D.kind i₁, by omega, i₁, rfl, fun i hi => by
        have := h i₁ i (Ne.symm hi) hi₁
        simpa [IsA1Comp3] using this⟩
    · push Not at hex
      obtain ⟨i₀⟩ := ‹Nonempty ι›
      exact ⟨Nat.card ι - 1, D.kind i₀, by omega, i₀, rfl, fun i _ => hex i⟩

end Shapes

section Dispatch


structure RouteD3Setup {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  cls : IsClassicalMember3 K z
  inClass : InClass3 (conjClass3 K)
  conn : ClassicalInvolution.DeltaConnected K
  setup : Setup3 K z
  ih : LocalLieSystems3 (conjClass3 K)
  below : CIT3Below (Nat.card G)
  rank : 3 ≤ twoRank G
  large : ¬ TwoSubgroupsFourGenerated G
  intr : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K

theorem RouteD3Setup.of_hyps {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (h3 : 3 ≤ twoRank G) (h4 : ¬ TwoSubgroupsFourGenerated G)
    (hΔ : ClassicalInvolution.DeltaConnected K) (hS : Setup3 K z)
    (hint : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K) : RouteD3Setup K z :=
  { cls := hz
    inClass := inClass3_conjugates hz
    conn := hΔ
    setup := hS
    ih := localLieSystems3_of_cit3Below (inClass3_conjugates hz) hBelow
    below := hBelow
    rank := h3
    large := h4
    intr := hint }

@[expose] def SetupRecognition3I : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → ClassicalInvolution.DeltaConnected K →
      Setup3 K z → Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

theorem exists_shape_or_multi3 {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (hLL : LocalLieSystems3 Ω) {K : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsClassicalMember3 K z) (hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G) :
    (∃ (a : ℕ) (c : CompData), LocalShapeC3 a c Ω z) ∨ MultiShape3 Ω z := by
  obtain ⟨ι, hι, ⟨D⟩⟩ := hLL {z} hnc
  have hmem : locImg Ω z K ∈ locFamily Ω z :=
    mem_locFamily_iff.mpr ⟨K, ⟨hK, isSubnormal_le hz.subnormal⟩, rfl⟩
  obtain ⟨i, -⟩ := D.fundamental _ hmem
  have : Nonempty ι := ⟨i⟩
  rcases shape_dichotomy3 D with h | ⟨a, c, hc, i₁, hk, hrest⟩
  · exact Or.inr ⟨ι, hι, D, h⟩
  · exact Or.inl ⟨a, c, ι, hι, D, hc, i₁, hk, hrest⟩

end Dispatch

section Pieces


@[expose] def ShapePiece3 (a : ℕ) (c : CompData) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → LocalShapeC3 a c (conjClass3 K) z →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def MultiPiece3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → MultiShape3 (conjClass3 K) z →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def RowPiece3 (S : ℕ → StatedLieTag → ℕ → Prop) : Prop :=
  ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), S a t n → ShapePiece3 a (CompData.model t n)

@[expose] def ShapeSp2 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 1 ∧ t = .PSp ∧ n = 2

@[expose] def ShapeTable3 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  CoreAssembly.ShapeTable a t n ∨ ShapeSp2 a t n

@[expose] def Piece3SL7 : Prop := RowPiece3 CoreAssembly.ShapeSL7
@[expose] def Piece3SL6 : Prop := RowPiece3 CoreAssembly.ShapeSL6
@[expose] def Piece3SLs : Prop := RowPiece3 CoreAssembly.ShapeSLs
@[expose] def Piece3SU7 : Prop := RowPiece3 CoreAssembly.ShapeSU7
@[expose] def Piece3SU6 : Prop := RowPiece3 CoreAssembly.ShapeSU6
@[expose] def Piece3SUs : Prop := RowPiece3 CoreAssembly.ShapeSUs
@[expose] def Piece3Sp4 : Prop := RowPiece3 CoreAssembly.ShapeSp4
@[expose] def Piece3Sp3 : Prop := RowPiece3 CoreAssembly.ShapeSp3
@[expose] def Piece3Sp2 : Prop := RowPiece3 ShapeSp2
@[expose] def Piece3E7 : Prop := RowPiece3 CoreAssembly.ShapeE7
@[expose] def Piece3E8 : Prop := RowPiece3 CoreAssembly.ShapeE8
@[expose] def Piece3TwinD : Prop := RowPiece3 CoreAssembly.ShapeTwinD
@[expose] def Piece3TwinSL4 : Prop := RowPiece3 CoreAssembly.ShapeTwinSL4
@[expose] def Piece3TwinB : Prop := RowPiece3 CoreAssembly.ShapeTwinB
@[expose] def Piece3TwinSp2 : Prop := RowPiece3 CoreAssembly.ShapeTwinSp2
@[expose] def Piece3TwinTD : Prop := RowPiece3 CoreAssembly.ShapeTwinTD
@[expose] def Piece3TwinSU4 : Prop := RowPiece3 CoreAssembly.ShapeTwinSU4

@[expose] def PieceAllA1₃ : Prop := ∀ a : ℕ, ShapePiece3 a CompData.sl23

@[expose] def PieceM11₃ : Prop := ∀ a : ℕ, ShapePiece3 a CompData.m11

@[expose] def PieceNoA1₃ : Prop := ∀ (t : StatedLieTag) (n : ℕ), ShapePiece3 0 (CompData.model t n)

@[expose] def PieceExotic₃ : Prop :=
  ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), 1 ≤ a → ¬ ShapeTable3 a t n →
    ShapePiece3 a (CompData.model t n)

theorem shapePiece3_of_setupRecognition3 (h : SetupRecognition3) (a : ℕ) (c : CompData) :
    ShapePiece3 a c :=
  fun G _ _ _ hnab K z hR _ => h G hnab K z hR.cls hR.below hR.rank hR.large hR.conn hR.setup

theorem multiPiece3_of_setupRecognition3 (h : SetupRecognition3) : MultiPiece3 :=
  fun G _ _ _ hnab K z hR _ => h G hnab K z hR.cls hR.below hR.rank hR.large hR.conn hR.setup

end Pieces

section Assembly


theorem setupRecognition3_of_pieces (hrows : RowPiece3 ShapeTable3) (hA1 : PieceAllA1₃)
    (hM11 : PieceM11₃) (hNo : PieceNoA1₃) (hEx : PieceExotic₃) (hmulti : MultiPiece3) :
    SetupRecognition3I := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hS hint
  have hR : RouteD3Setup K z := RouteD3Setup.of_hyps hz hBelow h3 h4 hΔ hS hint
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  rcases exists_shape_or_multi3 hR.ih hK hz (not_subset_center_of_ne_one hnab hz.ne_one) with
    ⟨a, c, hshape⟩ | hmul
  · obtain ⟨ι, hι, D, -, i₁, hk, -⟩ := id hshape
    have hvalid := D.valid i₁
    rw [hk] at hvalid
    rcases hvalid with ⟨t, n, -, -, rfl⟩ | rfl | rfl
    · by_cases ha : a = 0
      · subst ha
        exact hNo t n G hnab K z hR hshape
      · by_cases ht : ShapeTable3 a t n
        · exact hrows a t n ht G hnab K z hR hshape
        · exact hEx a t n (by omega) ht G hnab K z hR hshape
    · exact hA1 a G hnab K z hR hshape
    · exact hM11 a G hnab K z hR hshape
  · exact hmulti G hnab K z hR hmul

theorem rowPiece3_table (h1 : Piece3SL7) (h2 : Piece3SL6) (h3 : Piece3SLs) (h4 : Piece3SU7)
    (h5 : Piece3SU6) (h6 : Piece3SUs) (h7 : Piece3Sp4) (h8 : Piece3Sp3) (h9 : Piece3Sp2)
    (h10 : Piece3E7) (h11 : Piece3E8) (h12 : Piece3TwinD) (h13 : Piece3TwinSL4)
    (h14 : Piece3TwinB) (h15 : Piece3TwinSp2) (h16 : Piece3TwinTD) (h17 : Piece3TwinSU4) :
    RowPiece3 ShapeTable3 := by
  intro a t n h
  rcases h with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | h
  · exact h1 a t n h
  · exact h2 a t n h
  · exact h3 a t n h
  · exact h4 a t n h
  · exact h5 a t n h
  · exact h6 a t n h
  · exact h7 a t n h
  · exact h8 a t n h
  · exact h10 a t n h
  · exact h11 a t n h
  · exact h12 a t n h
  · exact h13 a t n h
  · exact h14 a t n h
  · exact h15 a t n h
  · exact h16 a t n h
  · exact h17 a t n h
  · exact h9 a t n h

theorem setupRecognition3_of_rows (h1 : Piece3SL7) (h2 : Piece3SL6) (h3 : Piece3SLs)
    (h4 : Piece3SU7) (h5 : Piece3SU6) (h6 : Piece3SUs) (h7 : Piece3Sp4) (h8 : Piece3Sp3)
    (h9 : Piece3Sp2) (h10 : Piece3E7) (h11 : Piece3E8) (h12 : Piece3TwinD)
    (h13 : Piece3TwinSL4) (h14 : Piece3TwinB) (h15 : Piece3TwinSp2) (h16 : Piece3TwinTD)
    (h17 : Piece3TwinSU4) (hA1 : PieceAllA1₃) (hM11 : PieceM11₃) (hNo : PieceNoA1₃)
    (hEx : PieceExotic₃) (hmulti : MultiPiece3) : SetupRecognition3I :=
  setupRecognition3_of_pieces (rowPiece3_table h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17) hA1 hM11 hNo hEx hmulti

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3W
