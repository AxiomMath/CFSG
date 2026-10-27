module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Vocab
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def IsOmega5 (X : Subgroup G) : Prop :=
  LieModel (X ⧸ oddCore X) .PSp 2 3 1

@[expose] def IsOmega6Plus (X : Subgroup G) : Prop :=
  LieModel (X ⧸ oddCore X) .PSL 4 3 1

@[expose] def IsOmega6Minus (X : Subgroup G) : Prop :=
  LieModel (X ⧸ oddCore X) .PSU 4 3 1

@[expose] def IsL29 (X : Subgroup G) : Prop :=
  LieModel (X ⧸ oddCore X) .PSL 2 3 2

@[expose] def IsL281 (X : Subgroup G) : Prop :=
  LieModel (X ⧸ oddCore X) .PSL 2 3 4

@[expose] def IsU33 (X : Subgroup G) : Prop :=
  LieModel (X ⧸ oddCore X) .PSU 3 3 1

@[expose] def layerCent (L : Subgroup G) (s : G) : Subgroup G :=
  CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G))

@[expose] def oddCoreIn (H : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup CFSG.oddCore H

@[expose] def omega1 (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ H ∧ x ^ 2 = 1}

@[expose] def cosetSet (t : G) (B : Subgroup G) : Set G :=
  {x | ∃ b ∈ B, x = t * b}

@[expose] def IsElemAb2 (E : Subgroup G) (k : ℕ) : Prop :=
  CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k

@[expose] def IsNormalE16In (P B : Subgroup G) : Prop :=
  B ≤ P ∧ IsElemAb2 B 4 ∧ (B.subgroupOf P).Normal

@[expose] def QuotEquivTo (H K : Subgroup G) (F : Type) [Group F] : Prop :=
  ∃ φ : ↥H →* F, Function.Surjective φ ∧ φ.ker = K.subgroupOf H

@[expose] def autIn (H Y : Subgroup G) : Subgroup (MulAut ↥Y) :=
  (H.subgroupOf (normalizer (Y : Set G))).map Y.normalizerMonoidHom

@[expose] def ConjTwoTransOn (N : Subgroup G) (T : Set G) : Prop :=
  (∀ n ∈ N, ∀ a ∈ T, n * a * n⁻¹ ∈ T) ∧
    ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T, a ≠ b → c ≠ d →
      ∃ n ∈ N, n * a * n⁻¹ = c ∧ n * b * n⁻¹ = d

@[expose] def Hyp62At (X : Subgroup G) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
    (e : ↥X ⧸ oddCore ↥X ≃* omegaProj hQ),
    Module.finrank (ZMod 3) V = 6 → quadSign Q = 1 →
      ∀ (s : G) (x : ProjSim Q), InducesViaP X (oddCore ↥X) hQ e s x → SimInGStar x →
        SimInOmegaStar hQ x

@[expose] def Asc82Hyp62 (G : Type) [Group G] : Prop :=
  ∀ X : Subgroup G, InC X → IsOmega6Plus X → Hyp62At X

end CFSG.OddStandard.SmallF3.Omega
