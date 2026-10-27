module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Basic
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

structure S8Ctx (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  ctx : S3Ctx G p
  stage3 : Stage3 G p
  stage4o : Stage4Order G p
  stage4 : Stage4 G p
  stage5 : Stage5 G p
  stage6 : Stage6 G p
  stage7 : Stage7 G p

theorem S8Ctx.of_ctx {G : Type} [Group G] [Finite G] {m : ℕ} (hctx : ThmACtx G m) {p : ℕ}
    (hp : p ∈ Mu G m) (h3 : Stage3 G p) (h4o : Stage4Order G p) (h4 : Stage4 G p)
    (h5 : Stage5 G p) (h6 : Stage6 G p) (h7 : Stage7 G p) : S8Ctx G p :=
  ⟨S3Ctx.of_ctx hctx hp, h3, h4o, h4, h5, h6, h7⟩

namespace S8

variable {G : Type} [Group G]

abbrev cx (x : G) : Subgroup G := Subgroup.centralizer ({x} : Set G)

@[expose] def centerOf (H : Subgroup G) : Subgroup G := (Subgroup.center ↥H).map H.subtype

@[expose] def IsMaxInvTwo (A X R : Subgroup G) : Prop :=
  R ≤ X ∧ IsPGroup 2 R ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
    ∀ R' : Subgroup G, R' ≤ X → IsPGroup 2 R' → A ≤ Subgroup.normalizer (R' : Set G) → R ≤ R' →
      R' = R

@[expose] def IsExtraSpec2 (R : Subgroup G) : Prop := timmesfeldIsExtraspecial ↥R

@[expose] def oPrimeRes (p : ℕ) (H : Type*) [Group H] : Subgroup H :=
  Subgroup.normalClosure {g : H | ∃ k : ℕ, g ^ (p ^ k) = 1}

@[expose] def IsTypeWithCenter [Finite G] (p : ℕ) (J : Subgroup G) (Q : TauCeti.CFSGIndex → Prop)
    (z : ℕ) : Prop :=
  catalogIs (PSimple p J) Q ∧ Nat.card (Subgroup.center (PQuot p J)) = z

@[expose] def sporIs (s : TauCeti.SporadicName) (i : TauCeti.CFSGIndex) : Prop := i = .sporadic s

@[expose] def isSporIndex : TauCeti.CFSGIndex → Prop
  | .sporadic _ => True
  | _ => False

@[expose] def isU4of (r : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .twistedA 3 q => q.card = r
    | _ => False

@[expose] def isPSp43 (i : TauCeti.CFSGIndex) : Prop :=
  isU4of 2 i ∨ onLie (fun | .B 2 q => q.card = 3 | _ => False) i

@[expose] def isD4of (r : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .D 4 q => q.card = r
    | _ => False

@[expose] def isG2of (r : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .G2 q => q.card = r
    | _ => False

@[expose] def isA6 (i : TauCeti.CFSGIndex) : Prop :=
  (match i with | .alternating n _ => n = 6 | _ => False) ∨
    onLie (fun | .A 1 q => q.card = 9 | _ => False) i

inductive Row where
  | ly | co2 | co1 | fi24 | fi24h | suz | suzh | th | m3 | m5
  deriving DecidableEq

namespace Row

@[expose] def prime : Row → ℕ
  | m5 => 5
  | _ => 3

@[expose] def name : Row → TauCeti.SporadicName
  | ly => .Ly
  | co2 => .Co2
  | co1 => .Co1
  | fi24 | fi24h => .Fi24Prime
  | suz | suzh => .Suz
  | th => .Th
  | m3 | m5 => .M

@[expose] def center : Row → ℕ
  | fi24h | suzh => 3
  | _ => 1

@[expose] def rank : Row → ℕ
  | ly | co2 | suz | suzh | th | m5 => 4
  | co1 => 5
  | fi24 | fi24h => 6
  | m3 => 7

@[expose] def rexp : Row → ℕ
  | ly => 5
  | co2 | co1 | th => 9
  | fi24 | fi24h => 13
  | suz | suzh => 7
  | m3 | m5 => 25

@[expose] def r0exp : Row → ℕ
  | ly | suz | suzh | th => 5
  | co2 => 1
  | co1 => 7
  | fi24 | fi24h => 9
  | m3 => 13
  | m5 => 9

@[expose] def Iq : Row → TauCeti.CFSGIndex → Prop
  | ly => sporIs .McL
  | co2 => isPSp43
  | co1 => sporIs .Suz
  | fi24 | fi24h => isD4of 3
  | suz | suzh => isU4of 3
  | th => isG2of 3
  | m3 => sporIs .Fi24Prime
  | m5 => sporIs .HN

@[expose] def Iz : Row → ℕ
  | ly | co1 | suz | m3 => 3
  | suzh => 9
  | co2 | fi24 | fi24h | th | m5 => 1

end Row

@[expose] def RowL [Finite G] (row : Row) (p : ℕ) (L : Subgroup G) : Prop :=
  p = row.prime ∧ IsTypeWithCenter p L (sporIs row.name) row.center

@[expose] def RowI [Finite G] (row : Row) (p : ℕ) (I : Subgroup G) : Prop :=
  IsTypeWithCenter p I row.Iq row.Iz

@[expose] def RowK [Finite G] (row : Row) (p : ℕ) (K : Subgroup G) : Prop :=
  match row with
  | .ly | .fi24 | .fi24h | .suz | .suzh | .th => K = ⊥
  | .co2 => IsTypeWithCenter p K isA6 1
  | .co1 => IsTypeWithCenter p K isPSp43 1
  | .m3 => IsTypeWithCenter p K (isU4of 3) 9
  | .m5 => Nonempty (PQuot p K ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))

@[expose] def RowData [Finite G] (row : Row) (p : ℕ) (Bs I K R0 : Subgroup G) : Prop :=
  p = row.prime ∧ Nat.card Bs = p ^ row.rank ∧ RowI row p I ∧ RowK row p K ∧
    Nat.card R0 = 2 ^ row.r0exp

@[expose] def cfgN (x : G) (R : Subgroup G) : Subgroup G := cx x ⊓ Subgroup.normalizer (R : Set G)

@[expose] def cfgI [Finite G] (p : ℕ) (L D : Subgroup G) : Subgroup G :=
  GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G))

@[expose] def cfgK [Finite G] (p : ℕ) (x : G) (L D R : Subgroup G) : Subgroup G :=
  GLAPLayer p (cfgI p L D ⊓ cfgN x R)

@[expose] def cfgR0 (R D : Subgroup G) : Subgroup G := R ⊓ Subgroup.centralizer (D : Set G)

@[expose] def LayerModCore [Finite G] (p : ℕ) (K Λ : Subgroup G) : Prop :=
  K ≤ Λ ∧ Λ ≤ K ⊔ GLAPPrimeCoreOf p Λ

structure SporCfg (G : Type) [Group G] [Finite G] (p : ℕ) (x : G) (L : Subgroup G) (row : Row) where
  Bs : Subgroup G
  R : Subgroup G
  D : Subgroup G
  hBs : GLAIsBmax p Bs
  hBsCard : Nat.card Bs = p ^ row.rank
  hRL : R ≤ L
  hR : IsExtraSpec2 R ∧ Nat.card R = 2 ^ row.rexp
  hBsN : Bs ≤ cfgN x R
  hRN : R = pCoreOf 2 (cfgN x R)
  hD : D ≤ Bs ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ x ∈ D
  hData : RowData row p Bs (cfgI p L D) (cfgK p x L D R) (cfgR0 R D)
  hMax : IsMaxInvTwo (cfgK p x L D R ⊔ Bs) (cx x) R
  hR0 : IsExtraSpec2 (cfgR0 R D) ∨ Nat.card (cfgR0 R D) = 2
  hK6 : row = .ly ∨ LayerModCore p (cfgK p x L D R)
    (GLAPLayer p (Subgroup.centralizer (D : Set G) ⊓
      Subgroup.centralizer (centerOf (cfgR0 R D) : Set G)))
  hNL : row = .m5 → ∃ J₀ : Subgroup G, GLAPComponent 5 (L ⊓ cfgN x R) J₀ ∧
    catalogIs (PSimple 5 J₀) (sporIs .Co1)

end S8

end CFSG.LocalAnalysis.GLTheoremA
