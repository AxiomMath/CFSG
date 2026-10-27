module

public import Mathlib
public import CFSG.Open.GeneratedCore
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.Delta

public section

open Lean Elab Term Meta in
elab "gl83_local% " t:term : term <= ty => withoutExporting do
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let e ← deltaExpand e fun n => (`CFSG.Assembly.GL83Local).isPrefixOf n
  Core.betaReduce e

namespace CFSG.Assembly.GL83Local

universe u

noncomputable section

@[expose] noncomputable def twoLocalRank (p : ℕ) (G : Type u) [Group G] [Finite G] : ℕ :=
  CFSG.Open.twoLocalPrimeRank p G

@[expose] def beta (TLR : ∀ (p : ℕ) (G : Type u) [Group G] [Finite G], ℕ)
    (k : ℕ) (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ k ≤ TLR p G}

@[expose] def isBmax {G : Type u} [Group G] [Finite G]
    (TLR : ∀ (p : ℕ) (G : Type u) [Group G] [Finite G], ℕ) (p : ℕ) (B : Subgroup G) : Prop :=
  CFSG.Open.IsElemAbelian p B ∧ Nat.card B = p ^ TLR p G ∧
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G)

@[expose] def pPrimeCoreOf (PC : ℕ → ∀ (H : Type u) [Group H], Subgroup H)
    {G : Type u} [Group G] (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (PC p H).map H.subtype

@[expose] noncomputable def weakCore {G : Type u} [Group G] [Finite G] (p : ℕ) (P : Subgroup G) :
    Subgroup G :=
  CFSG.Open.rankThreeAschCore 2 p P

@[expose] def weakCoreLocal (G : Type u) [Group G] [Finite G]
    (WC : ℕ → Subgroup G → Subgroup G) (p : ℕ) : Prop :=
  3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) ∧
    ∀ P : Sylow p G, ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧ WC p (P : Subgroup G) ≤ H

@[expose] def isMaxTwoLocal {G : Type u} [Group G] (M : Subgroup G) : Prop :=
  CFSG.Open.IsMaxTwoLocalSubgroup M

@[expose] def gf2Type (G : Type u) [Group G] [Finite G]
    (IML : Subgroup G → Prop) (Symp : ∀ {M : Type u} [Group M], Subgroup M → Prop)
    (Bmax : ∀ {M : Type u} [Group M] [Finite M], ℕ → Subgroup M → Prop) : Prop :=
  ∃ M : Subgroup G, IML M ∧ Symp (CFSG.Open.pCoreOf 2 M) ∧ ∃ B : Subgroup G, Bmax 3 B ∧ B ≤ M

section Local

variable {G : Type u} [Group G]

@[expose] def layer (IC : ∀ {M : Type u} [Group M], Subgroup M → Subgroup M → Prop)
    (H : Subgroup G) : Subgroup G :=
  sSup {K | IC K H}

@[expose] def pComponent (IC : ∀ {M : Type u} [Group M], Subgroup M → Subgroup M → Prop)
    (IS : ∀ {M : Type u} [Group M], Subgroup M → Subgroup M → Prop)
    (PC : ℕ → ∀ (H : Type u) [Group H], Subgroup H)
    [∀ (p : ℕ) (H : Type u) [Group H], (PC p H).Normal] (p : ℕ) (X L : Subgroup G) : Prop :=
  L ≤ X ∧ IS L X ∧
    IC ((L.subgroupOf X).map (QuotientGroup.mk' (PC p X))) ⊤ ∧
    ∀ J : Subgroup G, J < L → IS J X →
      (J.subgroupOf X).map (QuotientGroup.mk' (PC p X)) ≠
        (L.subgroupOf X).map (QuotientGroup.mk' (PC p X))

@[expose] def pLayer (PComp : ℕ → Subgroup G → Subgroup G → Prop) (p : ℕ) (X : Subgroup G) :
    Subgroup G :=
  sSup {L | PComp p X L}

@[expose] def sStar (IC : ∀ {M : Type u} [Group M], Subgroup M → Subgroup M → Prop)
    (Bmax : ∀ {M : Type u} [Group M] [Finite M], ℕ → Subgroup M → Prop) [Finite G]
    (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  Bmax p B ∧ x ∈ B ∧ x ≠ 1 ∧ IC L (Subgroup.centralizer ({x} : Set G)) ∧
    ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S

@[expose] def sHat (Bmax : ∀ {M : Type u} [Group M] [Finite M], ℕ → Subgroup M → Prop)
    (PComp : ℕ → Subgroup G → Subgroup G → Prop) (PCOf : ℕ → Subgroup G → Subgroup G) [Finite G]
    (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  Bmax p B ∧ x ∈ B ∧ x ≠ 1 ∧ L ≤ Subgroup.centralizer ({x} : Set G) ∧
    PComp p (Subgroup.centralizer ({x} : Set G)) L ∧
    ∀ b : G, (b ∈ B ∧ b ∈ Subgroup.normalizer (L : Set G) ∧
        (⁅L, Subgroup.zpowers b⁆ : Subgroup G) ≤ PCOf p L) ↔ b ∈ Subgroup.zpowers x

@[expose] def stdSubPre (IC : ∀ {M : Type u} [Group M], Subgroup M → Subgroup M → Prop)
    (Layer : Subgroup G → Subgroup G) (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) :
    Prop :=
  D ≤ B ∧ CFSG.Open.IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ x ∈ D ∧
    K = Layer (L ⊓ Subgroup.centralizer (D : Set G)) ∧
    IC K (L ⊓ Subgroup.centralizer (D : Set G)) ∧
    D = B ⊓ Subgroup.centralizer (K : Set G)

@[expose] def stdSub (Pre : ℕ → Subgroup G → G → Subgroup G → Subgroup G → Subgroup G → Prop)
    (Small : Subgroup G → Prop) (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) : Prop :=
  Pre p B x L D K ∧
    ((p = 3 ∧ ∃ D₁ K₁ : Subgroup G, Pre p B x L D₁ K₁ ∧ ¬ Small K₁) → ¬ Small K)

@[expose] def neighbor (PLayer : ℕ → Subgroup G → Subgroup G)
    (PCOf : ℕ → Subgroup G → Subgroup G) (p : ℕ) (x y : G) (J D K : Subgroup G) : Prop :=
  D = Subgroup.closure {x, y} ∧
    J ≤ ⨆ (a : G) (_ : a ∈ PLayer p (Subgroup.centralizer ({y} : Set G))),
      K.map (MulAut.conj a⁻¹).toMonoidHom ∧
    ¬ (⁅J, Subgroup.zpowers x⁆ : Subgroup G) ≤ PCOf p J

@[expose] def isNeighborOf (SHat : G → Subgroup G → Prop) (StdSub : Subgroup G → Subgroup G → Prop)
    (Neighbor : G → Subgroup G → Subgroup G → Subgroup G → Prop) (y : G) (J : Subgroup G) :
    Prop :=
  SHat y J ∧ ∃ D K : Subgroup G, StdSub D K ∧ Neighbor y J D K

end Local

end

end CFSG.Assembly.GL83Local
