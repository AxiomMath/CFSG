module

public import CFSG.ClassicalInvolution.Asc77.AscIHLie
public import CFSG.ClassicalInvolution.SmallCases.DSplitDefs
public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

@[expose] def CITBelowAll (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ e : ℕ, 5 ≤ p ^ e → CITBelowU p e n

section Notation

variable {G : Type} [Group G]

@[expose] def MuIso (Ω : Set (Subgroup G)) (W : Subgroup G) (X : Type) [Group X] : Prop :=
  Nonempty (↥(muGroup Ω W) ≃* X)

@[expose] def MuIsoZ2 (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop :=
  MuIso Ω W (Multiplicative (ZMod 2))

@[expose] def MuIsoS3 (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop :=
  MuIso Ω W (Equiv.Perm (Fin 3))

@[expose] def MuIsoE4 (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop :=
  MuIso Ω W (Multiplicative (ZMod 2 × ZMod 2))

@[expose] def MuIsoS4 (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop :=
  MuIso Ω W (Equiv.Perm (Fin 4))

@[expose] def coxeterD4 : CoxeterMatrix (Fin 4) where
  M := !![1, 3, 2, 2; 3, 1, 3, 3; 2, 3, 1, 2; 2, 3, 2, 1]
  isSymm := by decide
  diagonal := by decide
  off_diagonal := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

@[expose] def MuIsoWylD4 (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop :=
  MuIso Ω W coxeterD4.Group

@[expose] def IsElemAbelian2 (A : Subgroup G) (k : ℕ) : Prop :=
  Nat.card ↥A = 2 ^ k ∧ ∀ x ∈ A, x * x = 1

@[expose] def alphaOf (A : Subgroup G) : Subgroup G :=
  (⨆ a ∈ A, ⨆ (_ : a ≠ 1), ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) ⊔
    ⨅ a ∈ A, ⨅ (_ : a ≠ 1), oddCoreOf (Subgroup.centralizer ({a} : Set G))

@[expose] def gamma2 (B H : Subgroup G) : Subgroup G :=
  ⨆ A ∈ {A : Subgroup G | A ≤ B ∧ IsElemAbelian2 A 2}, H ⊓ Subgroup.centralizer (A : Set G)

@[expose] def zStarOf (H : Subgroup G) : Subgroup G :=
  ((Subgroup.center (↥H ⧸ classicalInvolutionOddCore ↥H)).comap
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥H))).map H.subtype

@[expose] def WeaklyClosedIn (A S : Subgroup G) : Prop :=
  ∀ g : G, conjSub g A ≤ S → conjSub g A = A

@[expose] def StronglyClosedIn (A S : Subgroup G) : Prop :=
  A ≤ S ∧ ∀ a ∈ A, ∀ g : G, g * a * g⁻¹ ∈ S → g * a * g⁻¹ ∈ A

@[expose] def oddTwoCoreOf (Y : Subgroup G) : Subgroup G :=
  ((sSup {N : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y) | N.Normal ∧ IsPGroup 2 N}).comap
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))).map Y.subtype

@[expose] def oTwoCore (H : Subgroup G) : Subgroup G :=
  (sSup {N : Subgroup ↥H | N.Normal ∧ IsPGroup 2 N}).map H.subtype

@[expose] def centralizerModOdd (H L : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ H ∧ x ∈ Subgroup.normalizer (L : Set G) ∧
    x ∈ Subgroup.normalizer (oddCoreOf L : Set G) ∧ ∀ l ∈ L, ⁅x, l⁆ ∈ oddCoreOf L}
  one_mem' := by
    refine ⟨H.one_mem, Subgroup.one_mem _, Subgroup.one_mem _, fun l _ => ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨hxH, hxL, hxO, hx⟩ ⟨hyH, hyL, hyO, hy⟩
    refine ⟨H.mul_mem hxH hyH, Subgroup.mul_mem _ hxL hyL, Subgroup.mul_mem _ hxO hyO,
      fun l hl => ?_⟩
    have key : ⁅x * y, l⁆ = (x * ⁅y, l⁆ * x⁻¹) * ⁅x, l⁆ := by
      simp only [commutatorElement_def]; group
    rw [key]
    refine (oddCoreOf L).mul_mem ?_ (hx l hl)
    exact (Subgroup.mem_normalizer_iff.mp hxO _).mp (hy l hl)
  inv_mem' := by
    rintro x ⟨hxH, hxL, hxO, hx⟩
    refine ⟨H.inv_mem hxH, Subgroup.inv_mem _ hxL, Subgroup.inv_mem _ hxO, fun l hl => ?_⟩
    have key : ⁅x⁻¹, l⁆ = x⁻¹ * ⁅x, l⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [key]
    have h1 : ⁅x, l⁆⁻¹ ∈ oddCoreOf L := (oddCoreOf L).inv_mem (hx l hl)
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxO) _).mp h1
    simpa using this

@[expose] def omegaOfSet (Ω : Set (Subgroup G)) (Δ : Set (Subgroup G)) : Set (Subgroup G) :=
  {J | J ∈ Ω ∧ ∀ K ∈ Δ, J ∈ omegaNbr Ω K}

@[expose] def dComp (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K J}

end Notation

@[expose] def HasLieType (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∃ D : OmegaLie p f Ω, D.card = 1 ∧ ∃ i : Fin D.card, D.tag i = t ∧ D.rank i = n

@[expose] def IsOrthTag (d : ℕ) (ε : Bool) (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) :
    Prop :=
  (d = 5 ∧ t = .PSp ∧ n = 2) ∨
  (d = 6 ∧ ε = true ∧ t = .PSL ∧ n = 4) ∨ (d = 6 ∧ ε = false ∧ t = .PSU ∧ n = 4) ∨
  (7 ≤ d ∧ d % 2 = 1 ∧ t = .POmegaOdd ∧ 2 * n + 1 = d) ∨
  (8 ≤ d ∧ d % 2 = 0 ∧ ε = true ∧ t = .POmegaPlus ∧ 2 * n = d) ∨
  (8 ≤ d ∧ d % 2 = 0 ∧ ε = false ∧ t = .POmegaMinus ∧ 2 * n = d)

@[expose] def HasOrthType (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (d : ℕ) (ε : Bool) : Prop :=
  ∃ t n, IsOrthTag d ε t n ∧ HasLieType p f Ω t n

@[expose] def SectionLieType (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (Y : Subgroup G) (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∃ D : LieSystemData p f (↥Y ⧸ classicalInvolutionOddCore ↥Y)
    (oddQuotientFamily (restrictFamily Ω Y)),
    D.card = 1 ∧ ∃ i : Fin D.card, D.tag i = t ∧ D.rank i = n

@[expose] def SectionOrthType (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (Y : Subgroup G) (d : ℕ) (ε : Bool) : Prop :=
  ∃ t n, IsOrthTag d ε t n ∧ SectionLieType p f Ω Y t n

@[expose] def piSign (p f : ℕ) : Bool := decide (p ^ f % 4 = 1)

@[expose] def signMul (a b : Bool) : Bool := decide (a = b)

end CFSG.ClassicalInvolution.Asc77
