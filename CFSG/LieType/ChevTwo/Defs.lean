module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.GLTheoremB.BlockDefs
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.UniqStatements

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB (IsOmegaTwo HasFixedPointFreeOrder IsTransvection)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

@[expose] def autCentralizer {S : Type} [Group S] (R : Subgroup (MulAut S)) : Subgroup S where
  carrier := {s | ∀ α ∈ R, α s = s}
  one_mem' := fun α _ => map_one α
  mul_mem' := fun {a b} ha hb α hα => by rw [map_mul, ha α hα, hb α hα]
  inv_mem' := fun {a} ha α hα => by rw [map_inv, ha α hα]

@[expose] def OutTwoNilpConcl (S : Type) [Group S] : Prop :=
  ∃ N : Subgroup (MulAut S), N.Normal ∧ inner S ≤ N ∧ Odd ((inner S).relIndex N) ∧
    ∀ α : MulAut S, ∃ k : ℕ, α ^ (2 ^ k) ∈ N

@[expose] def Chev2OutTwoNilp : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevTwo S → OutTwoNilpConcl S

@[expose] def Chev2CoreCent : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevTwo S → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut S), IsPGroup p R →
      pCoreOf 2 (autCentralizer R) = ⊥

@[expose] def Chev2RankTwoInverts : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevTwo S → (¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) →
    ∀ A : Subgroup (MulAut S), IsElemAbelian 2 A → Nat.card A = 4 → A ⊓ inner S = ⊥ →
      ∃ a ∈ A, a ≠ 1 ∧ ∃ x : S, Odd (orderOf x) ∧ 5 < orderOf x ∧ a x = x⁻¹

@[expose] def Chev2KDOut : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevTwo S → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P T : Subgroup (MulAut S), IsPGroup p P →
      IsPGroup 2 T → P ≤ Subgroup.normalizer (T : Set (MulAut S)) → ⁅T, P⁆ ≤ inner S

@[expose] def IsExcIndexTwo : TauCeti.LieTypeIndex → Prop
  | .E6 q | .E7 q | .E8 q | .F4 q | .twistedE6 q | .trialityD4 q => q.p = 2
  | .suzuki _ | .reeF4 _ | .tits => True
  | _ => False

@[expose] def IsChevTwoExc (Y : Type) [Group Y] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsExcIndexTwo d.1 ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def OppositeFixed (K : Type) [Group K] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut K), IsPGroup p R →
    ∀ Q : Subgroup K, Q ≠ ⊥ → IsPGroup 2 Q →
      pCoreOf 2 (Subgroup.normalizer (Q : Set K)) = Q → Subgroup.normalizer (Q : Set K) ≠ ⊤ →
        (∀ α ∈ R, Q.map α.toMonoidHom = Q) →
          autCentralizer R ≤ Subgroup.normalizer (Q : Set K) → autCentralizer R ⊓ Q = ⊥

@[expose] def OmegaTwoAutTwoPart : Prop :=
  ∀ (ε : Bool) (n : ℕ), 1 ≤ n → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    IsOmegaTwo ε (n + 1) K → ∀ T : Subgroup (MulAut K), IsPGroup 2 T → T ⊓ inner K = ⊥ →
      Nat.card T ≤ 2

@[expose] def isoGrp {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2) :
    Subgroup (GL ι (ZMod 2)) where
  carrier := {g | ∀ x, Q (Matrix.mulVec (g : Matrix ι ι (ZMod 2)) x) = Q x}
  one_mem' := fun x => by simp
  mul_mem' := fun {a b} ha hb x => by
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]; rw [ha, hb]
  inv_mem' := fun {a} ha x => by
    have := ha (Matrix.mulVec ((a⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) x)
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

@[expose] def InducedByIso {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (α : MulAut ↥(StatedOmega Q)) : Prop :=
  ∃ g ∈ isoGrp Q, ∀ x : ↥(StatedOmega Q),
    ((α x : ↥(StatedOmega Q)) : GL ι (ZMod 2)) = g * (x : GL ι (ZMod 2)) * g⁻¹

@[expose] def OmegaTwoAutInduced {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ZMod 2) → ZMod 2) : Prop :=
  ∀ α : MulAut ↥(StatedOmega Q), InducedByIso Q α

@[expose] def OmegaPlusEightInvolutions : Prop :=
  ∀ α : MulAut ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))), α ^ 2 = 1 →
    ∃ τ : MulAut ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))),
      InducedByIso (StatedQuadPlus 4 (ZMod 2)) (τ * α * τ⁻¹)

@[expose] def OrthOddCentCore {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ZMod 2) → ZMod 2) (ε : Bool) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ d ∈ isoGrp Q, d ≠ 1 → d ^ p = 1 →
    ∀ N : Subgroup (GL ι (ZMod 2)),
      N ≤ isoGrp Q ⊓ Subgroup.centralizer ({d} : Set (GL ι (ZMod 2))) →
      (N.subgroupOf (isoGrp Q ⊓ Subgroup.centralizer ({d} : Set (GL ι (ZMod 2))))).Normal →
      IsPGroup 2 N → N ⊓ StatedOmega Q = ⊥ → N ≠ ⊥ →
        (∃ t ∈ N, IsTransvection t ∧ N = Subgroup.zpowers t) ∧ HasFixedPointFreeOrder ε n p

end CFSG.LieType.ChevTwo
