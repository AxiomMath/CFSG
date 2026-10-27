module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.GroupTheory.SylowIntersectionControl.CharPair
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (fixV commV IsElemAbelian2 ffJ autOn conjAct IsSylowIn BinaryNaturalSL
  FFModel omegaOneCenterOf)
open CFSG.Open (pCoreOf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet O2Trivial)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

variable {W : Type} [CommGroup W]

@[expose] def gomiOset (Y : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  {A | A ≤ Y ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧ Nat.card W ≤ Nat.card A * Nat.card (fixV A)}

@[expose] def gomiP0Set (Y : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  {A | A ∈ Pset Y ∧ A ≤ CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y}

@[expose] def gomiPstar0Set (Y : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  {A | A ∈ PstarSet Y ∧ A ≤ CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y}

@[expose] def gomiPstar1Set (Y : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  PstarSet Y \ gomiPstar0Set Y

@[expose] def gomiGstar0 (Y : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  sSup (gomiPstar0Set Y)

@[expose] def gomiGstar1 (Y : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  sSup (gomiPstar1Set Y)

@[expose] def gomiG0 (Y : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  sSup (gomiP0Set Y)

@[expose] def gomiWXKer (X : Subgroup (MulAut W)) : Subgroup W :=
  commV X ⊓ fixV X

@[expose] def IsGomiQuad (X A K : Subgroup (MulAut W)) : Prop :=
  A ∈ gomiOset X ∧ K ≤ X ∧ (K.subgroupOf X).Normal ∧ CFSG.IsQuasisimple ↥K ∧
    CFSG.pCore 2 ↥K = ⊥ ∧
    X ⊓ Subgroup.centralizer (K : Set (MulAut W)) = (Subgroup.center ↥K).map K.subtype ∧
    X = K ⊔ A

@[expose] def GomiInQ (K : Type) [Group K] : Prop :=
  ∃ (W : Type) (_ : CommGroup W) (_ : Finite W), (∀ w : W, w ^ 2 = 1) ∧
    ∃ X A K₀ : Subgroup (MulAut W), IsGomiQuad X A K₀ ∧ Nonempty (K ≃* ↥K₀)

@[expose] def gomiOrbitSpan (Y A : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  ⨆ g ∈ gomiGstar0 Y, A.map (MulAut.conj g).toMonoidHom

@[expose] def gomiNSet (Y : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  {N | ∃ A ∈ gomiPstar0Set Y, N = gomiOrbitSpan Y A}

@[expose] def GomiFact31 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ Y : Subgroup (MulAut W),
    (gomiPstar0Set Y).Nonempty → O2Trivial (gomiGstar0 Y) →
    ((∀ N ∈ gomiNSet Y, IsSLn ↥N 2 1) ∧ sSupIndep (gomiNSet Y) ∧
        (gomiNSet Y).Pairwise (fun N N' => ∀ x ∈ N, ∀ y ∈ N', x * y = y * x) ∧
        sSup (gomiNSet Y) = gomiGstar0 Y) ∧
      ((∀ N ∈ gomiNSet Y, BinaryNaturalSL N (commV N) ⊥ 2 1) ∧
        iSupIndep (fun N : ↥(gomiNSet Y) => commV (N : Subgroup (MulAut W))) ∧
        ⨆ N : ↥(gomiNSet Y), commV (N : Subgroup (MulAut W)) = commV (gomiGstar0 Y)) ∧
      commV (gomiGstar0 Y) ⊔ fixV (gomiGstar0 Y) = ⊤ ∧
        Disjoint (commV (gomiGstar0 Y)) (fixV (gomiGstar0 Y))

@[expose] def GomiFact32 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ Y : Subgroup (MulAut W),
    O2Trivial (gomiGstar0 Y) → gomiG0 Y = gomiGstar0 Y

@[expose] def GomiFact33 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ Y : Subgroup (MulAut W),
    (gomiPstar1Set Y).Nonempty → O2Trivial (gomiGstar1 Y) →
      CFSG.layer ↥(gomiGstar1 Y) ≠ ⊥ ∧
      Subgroup.centralizer (CFSG.layer ↥(gomiGstar1 Y) : Set ↥(gomiGstar1 Y)) =
        CFSG.pPrimeCore 2 ↥(gomiGstar1 Y) ∧
      CFSG.pPrimeCore 2 ↥(gomiGstar1 Y) = Subgroup.center ↥(gomiGstar1 Y)

@[expose] def GomiFact34 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ Y L : Subgroup (MulAut W),
    L ≤ Y → CFSG.IsComponent (L.subgroupOf Y) → CFSG.pCore 2 ↥L = ⊥ →
    ¬ ffJ Y ≤ Subgroup.centralizer (L : Set (MulAut W)) →
    ∃ (W' : Type) (_ : CommGroup W') (_ : Finite W'), (∀ w : W', w ^ 2 = 1) ∧
      ∃ X A K : Subgroup (MulAut W'), IsGomiQuad X A K ∧
        ∃ f : ↥L →* ↥K, Function.Surjective f

@[expose] def GomiFact35 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y : Subgroup (MulAut W)) (m : ℕ), 1 ≤ m → IsSLn ↥Y 2 m → ∀ A ∈ gomiOset Y,
      BinaryNaturalSL Y ⊤ (fixV Y) 2 m ∧ Nat.card A = 2 ^ m ∧
        Nat.card W = 2 ^ m * Nat.card (fixV A)

@[expose] def GomiFact36 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y S L : Subgroup (MulAut W), IsSylowIn 2 S Y → L ≤ Y →
      CFSG.IsComponent (L.subgroupOf Y) → ⁅L, sSup (PstarSet S)⁆ ≠ ⊥ →
      ¬ fixV S ≤ fixV L → IsGomiChevTwo ↥L →
      (IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L)) →
      ¬ IsGomiParabolicSwap S L

@[expose] def gomiCSP (S L : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  S ⊓ fixingSubgroup (MulAut W) ((commV L ⊓ fixV (ffJ S) : Subgroup W) : Set W)

@[expose] def GomiFact37Hyp (Y S L : Subgroup (MulAut W)) : Prop :=
  (Pset Y).Nonempty ∧ IsSylowIn 2 S Y ∧ L ≤ Y ∧ (L.subgroupOf Y).IsSubnormal ∧
    ((∃ m : ℕ, 2 ≤ m ∧ (IsSLn ↥L 2 m ∨ IsAlt ↥L (2 * m - 1))) ∨
      (CFSG.IsQuasisimple ↥L ∧ Nat.card (Subgroup.center ↥L) = 3 ∧
        IsAlt (↥L ⧸ Subgroup.center ↥L) 7)) ∧
    (IsAlt ↥L 3 → Nat.card (commV L) = 4)

@[expose] def GomiFact37OneCSP : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y S L : Subgroup (MulAut W), GomiFact37Hyp Y S L → ⁅L, ffJ Y⁆ ≠ ⊥ →
      ((∃ m : ℕ, 2 ≤ m ∧ IsSLn ↥L 2 m ∧ BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m) ∨
        ∃ m : ℕ, 2 ≤ m ∧ IsAlt ↥L (2 * m - 1) ∧
          (FFModel.altDn (2 * m - 1)).Realizes L (commV L) (gomiWXKer L)) →
      gomiCSP S L ≤ Subgroup.normalizer (L : Set (MulAut W))

@[expose] def GomiFact37Two : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y S L : Subgroup (MulAut W), GomiFact37Hyp Y S L → ⁅L, sSup (PstarSet Y)⁆ ≠ ⊥ →
      (∃ m : ℕ, 2 ≤ m ∧ IsSLn ↥L 2 m ∧ BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m) ∨
      (∃ m : ℕ, 2 ≤ m ∧ IsAlt ↥L (2 * m - 1) ∧
        (FFModel.altDn (2 * m - 1)).Realizes L (commV L) (gomiWXKer L)) ∨
      (IsAlt ↥L 7 ∧ Nat.card (commV L) = 16)

@[expose] def GomiFact37Three : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y S L : Subgroup (MulAut W)) (m : ℕ), 1 ≤ m → (Pset Y).Nonempty → IsSylowIn 2 S Y →
      L ≤ Y → (L.subgroupOf Y).IsSubnormal → IsSLn ↥L 2 m →
      Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥ →
      BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m →
      gomiCSP S L = S ⊓ L

@[expose] def GomiFact37Four : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y S L : Subgroup (MulAut W)) (m : ℕ), 3 ≤ m → (Pset Y).Nonempty → IsSylowIn 2 S Y →
      L ≤ Y → (L.subgroupOf Y).IsSubnormal → IsAlt ↥L (2 * m - 1) →
      Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥ →
      (FFModel.altDn (2 * m - 1)).Realizes L (commV L) (gomiWXKer L) →
      ∃ φ : ↥Y ≃* Equiv.Perm (Fin (2 * m - 1)),
        gomiCSP S L = Subgroup.closure {s | ∃ hs : s ∈ Y, s ∈ S ∧ (φ ⟨s, hs⟩).IsSwap}

theorem gomi_moduleSetting {Ω : Type} [Group Ω] {H U : Subgroup Ω}
    (hU : CFSG.Open.IsElemAbelian 2 U) (hHU : H ≤ Subgroup.normalizer (U : Set Ω)) :
    (∀ u : ↥U, u ^ 2 = 1) ∧ ∃ φ : ↥H →* ↥(autOn H U), Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (U : Set Ω)).subgroupOf H := by
  refine ⟨fun u => Subtype.ext (hU.2 u u.2), ?_⟩
  let ψ : ↥H →* MulAut ↥U := (conjAct U).comp (Subgroup.inclusion hHU)
  have hψ : ∀ h : ↥H, ψ h ∈ autOn H U := fun h =>
    CFSG.Quasithin.AutOn.conjAct_mem_autOn (Subgroup.inclusion hHU h) h.2
  refine ⟨ψ.codRestrict (autOn H U) hψ, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    obtain ⟨n, hn, rfl⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.1 ha
    exact ⟨⟨n, hn⟩, rfl⟩
  · ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    refine Iff.trans ?_ (CFSG.Quasithin.AutOn.conjAct_eq_one_iff (Subgroup.inclusion hHU h))
    exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩

theorem gomiV_moduleSetting {Ω : Type} [Group Ω] (M : Subgroup Ω) :
    CFSG.Open.IsElemAbelian 2 (gomiV M) ∧ M ≤ Subgroup.normalizer (gomiV M : Set Ω) :=
  ⟨CFSG.Quasithin.B2F.isElemAbelian_omegaOneCenterOf _,
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M).trans
      (CFSG.Quasithin.normalizer_le_normalizer_of_map_mulEquiv
        CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv _)⟩

instance isMulCommutative_gomiV {Ω : Type} [Group Ω] (G : Subgroup Ω) :
    IsMulCommutative ↥(gomiV G) :=
  (gomiV_moduleSetting G).1.1

end CFSG.GroupTheory

end
