module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis


inductive TwClass
  | f4Six | e6Six | e8Ten | e8Twelve
  deriving DecidableEq

namespace TwClass

@[expose] def tag : TwClass → Tag
  | f4Six => .F4
  | e6Six => .E6
  | e8Ten => .E8
  | e8Twelve => .E8

@[expose] def e : TwClass → ℕ
  | f4Six => 6
  | e6Six => 6
  | e8Ten => 10
  | e8Twelve => 12

@[expose] def minQ : TwClass → ℕ
  | f4Six => 3
  | e6Six => 3
  | e8Ten => 2
  | e8Twelve => 2

@[expose] def J₂ : TwClass → Finset ℕ
  | f4Six => {2, 3}
  | e6Six => {0, 2, 4, 5}
  | e8Ten => {0, 1, 2, 3}
  | e8Twelve => {1, 2, 3, 4}

@[expose] def S₂ (c : TwClass) : Set (Fin c.tag.rank → ℤ) :=
  {α | IsRoot c.tag α ∧ ∀ i : Fin c.tag.rank, i.val ∉ c.J₂ → α i = 0}

@[expose] def S₁ (c : TwClass) : Set (Fin c.tag.rank → ℤ) :=
  {β | IsRoot c.tag β ∧ ∀ α ∈ c.S₂, CFSG.LieType.Steinberg.Adjoint.iform β α = 0}

@[expose] def wordF4 : List (Fin Tag.F4.rank) := [1, 2, 3, 1, 2, 1]

@[expose] def wordE6 : List (Fin Tag.E6.rank) := [3, 4, 5, 2, 3, 4, 0, 2, 3]

@[expose] def wordE8Ten : List (Fin Tag.E8.rank) :=
  [4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2,
    3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4]

@[expose] def wordE8Twelve : List (Fin Tag.E8.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]

@[expose] def w : (c : TwClass) → WeylGroup c.tag
  | f4Six => (coxeterSystem Tag.F4).wordProd wordF4
  | e6Six => (coxeterSystem Tag.E6).wordProd wordE6
  | e8Ten => (coxeterSystem Tag.E8).wordProd wordE8Ten
  | e8Twelve => (coxeterSystem Tag.E8).wordProd wordE8Twelve


end TwClass

variable (τ : Tag) (K : Type) [Field K] [Finite K]

structure LangLevi (w : WeylGroup τ) where
  L : Type
  [field : Field L]
  [algebra : Algebra K L]
  [isAlgClosure : IsAlgClosure K L]
  Fr : L →+* L
  hFr : ∀ c, Fr c = c ^ Nat.card K
  g : ModGL τ L
  g_mem : g ∈ Lθ τ L
  lang : Units.map (entrywiseHom Fr) g = g * canonicalRep (coxeterSystem τ) L w

namespace LangLevi

variable {τ K} {w : WeylGroup τ} (D : LangLevi τ K w)

attribute [instance] LangLevi.field LangLevi.algebra LangLevi.isAlgClosure

@[expose] def frame (S : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ K) :=
  adjointGroup τ K ⊓ (rootSpan τ D.L S).comap
    ((MulAut.conj D.g⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K D.L)))

end LangLevi

@[expose] def TwClass.X₁ (c : TwClass) {K : Type} [Field K] [Finite K]
    (D : LangLevi c.tag K c.w) : Subgroup (ModGL c.tag K) :=
  D.frame c.S₁

@[expose] def TwClass.X₂ (c : TwClass) {K : Type} [Field K] [Finite K]
    (D : LangLevi c.tag K c.w) : Subgroup (ModGL c.tag K) :=
  D.frame c.S₂

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
