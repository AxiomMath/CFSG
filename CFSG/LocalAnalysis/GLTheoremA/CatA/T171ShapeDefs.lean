module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I171Facts
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

structure Setup {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  qs : CFSG.Open.IsQuasisimple ↥L
  chev2 : IsChevSimple 2 (PSimple p L)
  elem : IsElemAbelian p A
  idiag : InnerDiagMarking A L
  faithful : A ⊓ Subgroup.centralizer (L : Set G) = ⊥
  d_mem : d ∈ A
  d_ne : d ≠ 1
  b_mem : b ∈ A
  comp : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
    GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J
  pcomp : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) J
  chevJ : IsChevSimple 2 (PSimple p J)
  b_norm : b ∈ Subgroup.normalizer (J : Set G)
  nonID : ¬ InnDiagOn p (Subgroup.zpowers b) J

@[expose] def FieldType {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) : Prop :=
  ∃ (M : GL (Fin 6) K) (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)) (l : Kˣ),
    M ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) l ∧ (∀ c : Kˣ, c ^ 3 ≠ l) ∧
      a = TableB.projConj (unitarySU 2 n K 6)
        ⟨M, TableBUE.gu_subset_normalizer (d := 6) h hM⟩

@[expose] def U6Marking : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ),
    Setup 3 L J A d b → catalogIs (PSimple 3 L) (S10.isU6n n) → Odd n →
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData 2 n K)
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K 6)),
      ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ n)),
        LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ

@[expose] def U6SizeModel : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData 2 n K), 3 ∣ 2 ^ n + 1 →
    ∀ Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6))), IsElemAbelian 3 Ab →
      (∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) →
      (∃ a ∈ Ab, FieldType h a) → Nat.card Ab ≤ 3 ^ 3

@[expose] def U6NoActModel : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData 2 n K), 3 ∣ 2 ^ n + 1 →
    ∀ Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6))),
      IsElemAbelian 3 Ab → Ab ≤ InndiagSU.inndiagU (d := 6) h (by norm_num) →
      3 ^ 3 ≤ Nat.card Ab → (∃ a ∈ Ab, FieldType h a) →
      ∀ V : Subgroup (LargeEvenProj (unitarySU 2 n K 6)), IsPGroup 2 V →
        (∀ φ ∈ Ab, ∀ v ∈ V, φ v ∈ V) → V = ⊥

@[expose] def U6Type9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ) (K : Type)
    [Field K] [Finite K] (h : UnitaryFieldData 2 n K)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K 6)),
    Setup 3 L J A d b → 3 ∣ 2 ^ n + 1 →
    (∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ) →
    ∀ φ, LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d) φ → FieldType h φ

@[expose] def Shape15On (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G),
    Setup p L J A d b → catalogIs (PSimple p L) (onLie F) → I171.I171LieShapeAt p L

@[expose] def LinUniBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N : ℕ),
    Setup p L J A d b → catalogIs (PSimple p L) (onLie fun i => ∃ q,
      (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧ I171.I171LieShape p i) →
    Nat.card A ≤ p ^ (1 + N / p)

@[expose] def E6Bound (tw : Bool) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G),
    Setup 3 L J A d b →
    catalogIs (PSimple 3 L) (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧
      (if tw then i = .twistedE6 q else i = .E6 q)) → Nat.card A ≤ 3 ^ 4

@[expose] def LowerUni : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (p N : ℕ), p.Prime → p ≠ 2 → 3 ≤ N →
    CFSG.Open.IsQuasisimple ↥L →
    catalogIs (PSimple p L) (onLie fun i => ∃ q, i = .twistedA (N - 1) q ∧
      q.p = 2 ∧ p ∣ q.card + 1) →
    ∃ E U : Subgroup G, E ≤ L ∧ U ≤ L ∧ IsElemAbelian p E ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧
      p ^ (N - 3) * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E

@[expose] def LowerLin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (p N : ℕ), p.Prime → p ≠ 2 → 3 ≤ N →
    CFSG.Open.IsQuasisimple ↥L →
    catalogIs (PSimple p L) (onLie fun i => ∃ q, i = .A (N - 1) q ∧
      q.p = 2 ∧ p ∣ q.card - 1) →
    ∃ E U : Subgroup G, E ≤ L ∧ U ≤ L ∧ IsElemAbelian p E ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧
      p ^ (N - 2) * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E

@[expose] def LowerE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    CFSG.Open.IsQuasisimple ↥L →
    catalogIs (PSimple 3 L) (onLie fun i => ∃ q, i = .E6 q ∧
      q.p = 2 ∧ 3 ∣ q.card - 1) →
    ∃ E U : Subgroup G, E ≤ L ∧ U ≤ L ∧ IsElemAbelian 3 E ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧
      3 ^ 5 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E

@[expose] def TwE6NoAct : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L D K : Subgroup Ω)
    (β : Ω) (n : ℕ),
    CFSG.Open.IsKGroup Ω → S171.Cfg Ω p B x L → S171.MaxG p B → L.Normal →
    GLAStdSubPre p B x L D K → GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set Ω)) K →
    IsChevSimple 2 (PSimple p K) → β ∈ B → β ∉ D →
    ¬ InnDiagOn p (Subgroup.zpowers β) K → S171.ExtremalType p L →
    catalogIs (PSimple p L) (S10.isTE6n n) → Odd n →
    ∀ T : Subgroup Ω, T ≤ Subgroup.normalizer (L : Set Ω) →
      T ≤ Subgroup.centralizer ({x} : Set Ω) → IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set Ω) →
      (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (L : Set Ω)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
