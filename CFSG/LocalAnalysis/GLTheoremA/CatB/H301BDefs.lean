module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H1017

@[expose] def MapsOntoType {S : Type} [Group S] (H : Subgroup S)
    (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∃ i, Q i ∧ ∃ f : ↥H →* i.Group, Function.Surjective f

@[expose] def RowKS {S : Type} [Group S] (row : Row) (K : Subgroup S) : Prop :=
  match row with
  | .ly | .fi24 | .fi24h | .suz | .suzh | .th => K = ⊥
  | .co2 => MapsOntoType K isA6
  | .co1 => True
  | .m3 => MapsOntoType K (isU4of 3)
  | .m5 => ∃ f : ↥K →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      Function.Surjective f

@[expose] def I301BRow (row : Row) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S (sporIs row.name) →
    ∀ (B I K R0 R1 : Subgroup (MulAut S)) (y : MulAut S),
      B ≤ (MulAut.conj : S →* MulAut S).range → IsElemAbelian row.prime B →
      Nat.card B = row.prime ^ (row.rank - 1) → y ∈ B → y ≠ 1 →
      I ≤ (MulAut.conj : S →* MulAut S).range → I ≤ cx y → MapsOntoType I row.Iq →
      R0 ≤ cx y → (IsExtraSpec2 R0 ∨ Nat.card R0 = 2) → Nat.card R0 = 2 ^ row.r0exp →
      K ≤ cx y → RowKS row K → K ⊔ B ≤ Subgroup.normalizer (R0 : Set (MulAut S)) →
      IsPGroup 2 R1 → K ⊔ B ≤ Subgroup.normalizer (R1 : Set (MulAut S)) → R0 < R1 →
      IsExtraSpec2 R1

@[expose] def I301BDistinct (row : Row) : Prop :=
  ∀ (H : Type) [Group H], catalogIs H (sporIs row.name) → catalogIs H row.Iq → False

@[expose] def CoverTwoRankAttained (s : TauCeti.SporadicName) (r : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], catalogIs (H ⧸ Subgroup.center H) (sporIs s) →
    Nat.card (Subgroup.center H) = 3 → ∃ E T : Subgroup H, IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ r ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set H)

structure I301BRes : Prop where
  rowLy : I301BRow .ly
  rowCo2 : I301BRow .co2
  rowCo1 : I301BRow .co1
  rowFi24 : I301BRow .fi24
  rowSuz : I301BRow .suz
  rowTh : I301BRow .th
  rowM3 : I301BRow .m3
  rowM5 : I301BRow .m5
  distLy : I301BDistinct .ly
  distCo2 : I301BDistinct .co2
  distCo1 : I301BDistinct .co1
  distFi24 : I301BDistinct .fi24
  distSuz : I301BDistinct .suz
  distTh : I301BDistinct .th
  distM3 : I301BDistinct .m3
  distM5 : I301BDistinct .m5
  witLy : TwoRankAttained 3 .Ly 3
  witCo2 : TwoRankAttained 3 .Co2 3
  witCo1 : TwoRankAttained 3 .Co1 4
  witFi24 : TwoRankAttained 3 .Fi24Prime 5
  witFi24Cover : CoverTwoRankAttained .Fi24Prime 6
  witSuz : TwoRankAttained 3 .Suz 3
  witSuzCover : CoverTwoRankAttained .Suz 4
  witTh : TwoRankAttained 3 .Th 3
  witM3 : TwoRankAttained 3 .M 6
  witM5 : TwoRankAttained 5 .M 3
  leB3 : TwoRankLe 3 .B 5
  leB5 : TwoRankLe 5 .B 2

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
