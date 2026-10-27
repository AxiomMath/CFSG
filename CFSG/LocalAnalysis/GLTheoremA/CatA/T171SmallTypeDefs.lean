module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)
open scoped commutatorElement

@[expose] def TwoLocal {G : Type} [Group G] (E : Subgroup G) : Prop :=
  ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≠ ⊥ ∧ E ≤ Subgroup.normalizer (P : Set G)

@[expose] def StdAt {G₀ : Type} [Group G₀] (Bb : Subgroup G₀) (y : G₀) : Prop :=
  IsComponentOf (GLALayer (Subgroup.centralizer ({y} : Set G₀)))
      (Subgroup.centralizer ({y} : Set G₀)) ∧
    Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer ({y} : Set G₀)) : Set G₀) =
      Subgroup.zpowers y

structure SmallModel (G₀ : Type) [Group G₀] (Bb : Subgroup G₀) : Prop where
  elem : IsElemAbelian 3 Bb
  card_ge : 27 ≤ Nat.card Bb
  card_le : Nat.card Bb ≤ 81
  twoLocal : TwoLocal Bb
  max : ∀ E : Subgroup G₀, IsElemAbelian 3 E → TwoLocal E → Nat.card E ≤ Nat.card Bb
  std : ∃ d ∈ Bb, d ≠ 1 ∧ StdAt Bb d
  small : ∀ y ∈ Bb, y ≠ 1 → StdAt Bb y →
    HStdExcl.SmallOrd (GLALayer (Subgroup.centralizer ({y} : Set G₀)))

@[expose] def NoSmallModel (G₀ : Type) [Group G₀] : Prop :=
  ∀ Bb : Subgroup G₀, ¬ SmallModel G₀ Bb

@[expose] def ModelRed : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω),
    CFSG.Open.IsKGroup Ω → S171.Cfg Ω 3 B x L → L.Normal → S171.MaxG 3 B →
    (∃ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K) →
    (∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K) →
    (∃ T : Subgroup Ω, T ≤ Subgroup.normalizer (L : Set Ω) ∧
      T ≤ Subgroup.centralizer ({x} : Set Ω) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set Ω) ∧ (⁅T, B⁆ : Subgroup Ω) ≠ ⊥) →
    ∀ (G₀ : Type) [Group G₀] [Finite G₀], AutThreePowInner G₀ →
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* G₀) → ¬ 3 ∣ Nat.card (Subgroup.center ↥L) →
      ∃ Bb : Subgroup G₀, SmallModel G₀ Bb

@[expose] def AlphaRed : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω),
    CFSG.Open.IsKGroup Ω → S171.Cfg Ω 3 B x L → L.Normal → S171.MaxG 3 B →
    (∃ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K) →
    (∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ α : MulAut (TauCeti.CFSGIndex.lie d).Group, α ^ 3 = 1 ∧ α ≠ 1 ∧
        (d.1 ≠ .tits → α ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group) ∧
        ∃ J : Subgroup (TauCeti.CFSGIndex.lie d).Group,
          GLAPComponent 3 (fixSubgroup α) J ∧ IsComponentOf J (fixSubgroup α) ∧
          (catalogIs (PSimple 3 J) S9.isU4two ∨ catalogIs (PSimple 3 J) S10.isA6) ∧
          HStdExcl.SmallOrd J

@[expose] def BCardLe : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω),
    S171.Cfg Ω 3 B x L → (∃ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K) →
    (∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K) → Nat.card B ≤ 3 ^ 5

@[expose] def A6Pumpup (S : Type) [Group S] (α : MulAut S) : Prop :=
  α ^ 3 = 1 ∧ α ≠ 1 ∧ ∃ J : Subgroup S, GLAPComponent 3 (fixSubgroup α) J ∧
    catalogIs (PSimple 3 J) S10.isA6

@[expose] def A6InnField : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∈ innAutDerived S → A6Pumpup S α → KD264Lie.fieldSize d.1 = 2

@[expose] def ExcTwo : TauCeti.LieTypeIndex → Prop
  | .E6 q | .E7 q | .E8 q | .F4 q | .twistedE6 q | .trialityD4 q => q.card = 2
  | .tits => True
  | _ => False

@[expose] def ExcNoSmall : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, ExcTwo d.1 → HStdExcl.NoSmall (TauCeti.CFSGIndex.lie d).Group

@[expose] def Wit5 (Y : Type) [Group Y] : Prop :=
  ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ E ⊓ Subgroup.center Y = ⊥ ∧
    TwoLocal E

@[expose] def UniHighWit : Prop :=
  ∀ (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid),
    q.card = 2 → 6 ≤ n → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
      Nonempty (Y ⧸ Subgroup.center Y ≃*
        (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group) → Wit5 Y

@[expose] def Wit5False : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω),
    S171.Cfg Ω 3 B x L → S171.MaxG 3 B → Nat.card B ≤ 3 ^ 5 → Wit5 ↥L → False

@[expose] def FamLin : Prop :=
  ∀ (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A n q).Valid),
    q.card = 2 → 4 ≤ n → NoSmallModel (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group

@[expose] def FamU4 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid),
    q.card = 2 → NoSmallModel (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group

@[expose] def FamSp : Prop :=
  ∀ (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B n q).Valid),
    q.card = 2 → 3 ≤ n → NoSmallModel (TauCeti.CFSGIndex.lie ⟨.B n q, hv⟩).Group

@[expose] def FamOmP : Prop :=
  ∀ (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D n q).Valid),
    q.card = 2 → 5 ≤ n → NoSmallModel (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group

@[expose] def FamOmM : Prop :=
  ∀ (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedD n q).Valid),
    q.card = 2 → 4 ≤ n → NoSmallModel (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
