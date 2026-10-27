module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.RouteD.TypeURecognition

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Phan

variable {p f : ℕ} [Fact p.Prime]

@[expose] def PieceSU3Big (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ¬ TwoSubgroupsFourGenerated G →
      LocalShapeT p f 1 .PSU 3 (conjClass K) z → LieSystem p f G (conjClass K)

theorem shapePiece_su3 (hbig : PieceSU3Big p f) (hr2 : CITRankTwo) (hs4 : CITSectionalFour)
    (hup : SmallUpgrade p f) : ShapePiece p f 1 .PSU 3 := by
  intro G _ _ _ hnab K z S hS
  by_cases h4 : TwoSubgroupsFourGenerated G
  · refine hup G hnab S.odd S.five K z S.cls ?_
    by_cases h2 : CFSG.Open.twoRank G ≤ 2
    · exact hr2 G hnab z S.cls.orderOf_eq_two K S.cls.mem S.cls.subnormal
        (witness_of_isClassicalMember S.odd S.five S.cls)
        (not_isSolvable_of_isClassicalMember S.cls) h2
    · exact hs4 G hnab z S.cls.orderOf_eq_two K S.cls.mem S.cls.subnormal
        (witness_of_isClassicalMember S.odd S.five S.cls)
        (not_isSolvable_of_isClassicalMember S.cls) ⟨by omega, h4⟩
  · exact hbig G hnab K z S h4 hS

@[expose] def ChainPieceSUsTwo (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeU p f 2 (conjClass K) z →
      ∃ U : Fin 4 → Subgroup G, (∀ i, U i ∈ conjClass K) ∧
        (∀ i j : Fin 4, (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
        ∀ i j : Fin 4, (j : ℕ) = i + 1 →
          ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)

theorem pieceSU3Big_of_chainTwo (h : ChainPieceSUsTwo p f) : PieceSU3Big p f := by
  intro G _ _ _ hnab K z S _ hS
  have hshape : LocalShapeU p f 2 (conjClass K) z := hS.exists_two_components
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z S hshape
  obtain ⟨D, -, -⟩ := routeD_typeU_of_chain S.odd S.five (m := 2) (by omega) S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls hshape S.p1 U hUΩ hcomm hpair
  exact ⟨D⟩

end CFSG.ClassicalInvolution.RouteD
