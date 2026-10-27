module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

structure AFrame (A : Type) [Group A] [Finite A] (zb : A) (Sb Vb : Subgroup A) : Prop where
  core : pPrimeCore 2 A = ⊥
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 Sb ⊤
  card : Nat.card ↥Sb = 2 ^ 8
  rank_lo : 4 ≤ pRank 2 ↥Sb
  rank_hi : pRank 2 A ≤ 4
  zb_ord : orderOf zb = 2
  zb_mem : zb ∈ Sb
  zcen : ∀ u ∈ Sb, (∀ s ∈ Sb, s * u = u * s) → orderOf u = 2 → u = zb
  v3 : IsPGroup 3 ↥Vb
  v_ne : Vb ≠ ⊥
  v_norm : Sb ≤ normalizer (Vb : Set A)
  v_max : ∀ W : Subgroup A, IsPGroup 3 ↥W → Sb ≤ normalizer (W : Set A) → Vb ≤ W → W = Vb
  invsec : ∀ x : A, orderOf x = 2 → ∀ (Y : Type) [Group Y] [IsSimpleGroup Y],
    ¬ Group.IsSolvable Y → IsSection Y ↥(centralizer ({x} : Set A)) → KindFactorAll Kind.ly Y
  four : ∀ U : Subgroup A, IVK.IsFourSubgroup U → ∀ r : ℕ, r.Prime → 5 ≤ r →
    ∀ x ∈ centralizer (U : Set A), orderOf x = r → x ∈ pPrimeCoreOf 2 (centralizer (U : Set A))
  cbar : ∀ t : A, orderOf t = 2 → ∀ R : Subgroup A, R ≤ centralizer ({t} : Set A) →
    ∃ (n : ℕ) (K : Type) (_ : Group K) (R' : Subgroup K), (n = 10 ∨ n = 11) ∧
      IsDoubleCoverOfAlt K n ∧ Nonempty ((↥R ⧸ pPrimeCore 2 ↥R) ≃* (↥R' ⧸ pPrimeCore 2 ↥R'))

@[expose] def CellAbs (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (zb : A) (Sb Vb J : Subgroup A), AFrame A zb Sb Vb →
    IsComponent J → ¬ Vb ≤ centralizer (J : Set A) → F (↥J ⧸ center ↥J) →
    (IsDoubleCoverOfAlt A 11 ∨ NativeSporadic.IsSporadic A .Ly)

structure CellsAbs : Prop where
  alt : CellAbs FAlt
  spor : CellAbs FSpor
  mcly : CellAbs FMcLy
  two : CellAbs FTwo
  l2 : CellAbs FL2
  l3 : CellAbs FL3
  u3 : CellAbs FU3
  sp4 : CellAbs FSp4
  g2 : CellAbs FG2
  d4 : CellAbs FD4
  l4 : CellAbs FL4
  u4 : CellAbs FU4
  l5 : CellAbs FL5
  u5 : CellAbs FU5
  ree : CellAbs FRee

@[expose] def AFrameThm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.ly S →
    ∀ H : Subgroup G, H ≠ ⊤ → S ≤ H → ∀ V : Subgroup G, MaxSInv 3 S H V → ¬ V ≤ pPrimeCoreOf 2 H →
      ∃ zb : HBar H, AFrame (HBar H) zb (barIn H S) (barIn H V)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
