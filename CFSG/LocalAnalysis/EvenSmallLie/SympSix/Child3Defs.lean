module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public noncomputable section

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open scoped Pointwise

structure Setting {G : Type} [Group G] [Finite G] (L : Subgroup G)
    (T : Sylow 2 (centralizer (L : Set G))) (z : G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ x y : G, x * y ≠ y * x
  kProper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G
  oddCore_eq : CFSG.oddCore G = ⊥
  standard : CFSG.Assembly.ComponentType.IsStandardSubgroup L
  not_normal : ¬ L.Normal
  center_eq : center L = ⊥
  model : CFSG.Blueprint.LieModel L .PSp 3 2 1
  core : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥
  cyclic : IsCyclic (T : Subgroup (centralizer (L : Set G)))
  mem : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
  order : orderOf z = 2
  core_z : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥

section Layer

variable {G : Type} [Group G] (C : Subgroup G) (z : G) (lev : GL (Fin 3) (ZMod 2) →* G)

@[expose] def layX : Subgroup G := normalizer (C : Set G)

instance layC_normal : (C.subgroupOf (layX C)).Normal := Subgroup.normal_in_normalizer

abbrev LayF : Type := ↥(layX C) ⧸ C.subgroupOf (layX C)

@[expose] def layπ : layX C →* LayF C := QuotientGroup.mk' _

open Classical in
@[expose] def laya : LayF C := if h : z ∈ layX C then layπ C ⟨z, h⟩ else 1

@[expose] def layJL : Subgroup (LayF C) := ((lev.range).subgroupOf (layX C)).map (layπ C)

@[expose] def layRo : Subgroup (LayF C) := CFSG.pPrimeCore 2 (LayF C)

instance layRo_normal : (layRo C).Normal := CFSG.pPrimeCore_normal

abbrev LayY : Type := LayF C ⧸ layRo C

@[expose] def layθ : LayF C →* LayY C := QuotientGroup.mk' _

@[expose] def layaBar : LayY C := layθ C (laya C z)

@[expose] def layJLBar : Subgroup (LayY C) := (layJL C lev).map (layθ C)

@[expose] def layDstar : Subgroup (LayY C) := normalClosure (layJLBar C lev : Set (LayY C))

@[expose] def LayerSimple : Prop :=
  IsSimpleGroup (layDstar C lev) ∧ (∃ x y : layDstar C lev, x * y ≠ y * x) ∧
    layJLBar C lev < layDstar C lev ∧
    ∃ d ∈ layDstar C lev, (layaBar C z)⁻¹ * d * layaBar C z ≠ d

end Layer

section AltEight

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (z : G)

@[expose] def alt8C₂ : Subgroup G :=
  Classical.epsilon fun C : Subgroup G =>
    C ≤ sp6D₂ φ e z ∧ IsMulCommutative C ∧ Nat.card C = 512

end AltEight

@[expose] def Sector (D : Type) [Group D] : Prop :=
  (∃ n f : ℕ, 2 ≤ n ∧ 1 ≤ f ∧ ∃ (k : Type) (_ : Field k), Nat.card k = 2 ^ f ∧
      Nonempty (D ≃* LinearFlag.projectiveSL n k)) ∨
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ CFSG.Blueprint.LieModel D .PSL 2 p f) ∨
    (∃ p f : ℕ, CFSG.Blueprint.SuzukiModel D p f) ∨
    (∃ n f : ℕ, 3 ≤ n ∧ 1 ≤ f ∧ CFSG.Blueprint.LieModel D .PSU n 2 f) ∨
    (∃ r f : ℕ, 2 ≤ r ∧ 1 ≤ f ∧ CFSG.Blueprint.LieModel D .PSp r 2 f) ∨
    (∃ ℓ f : ℕ, CFSG.Blueprint.LieModel D .twistedG2 0 ℓ f) ∨
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (D ≃* alternatingGroup (Fin n)))

@[expose] def GapEpsilonOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (T : Sylow 2 (centralizer (L : Set G)))
    (z : G), Setting L T z →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : BilinForm (ZMod 2) V), b.IsAlt → b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G) →
    IsElementaryAbelian 2 (sp6C₂ φ he z)

@[expose] def GapLagrangianSelector : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (T : Sylow 2 (centralizer (L : Set G)))
    (z : G), Setting L T z →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : BilinForm (ZMod 2) V), b.IsAlt → b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G) →
    IsElementaryAbelian 2 (sp6C₂ φ he z) → Sp6LayerSimple φ he z →
    Sector (sp6Dstar φ he z)

@[expose] def GapAltEight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (T : Sylow 2 (centralizer (L : Set G)))
    (z : G), Setting L T z →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : BilinForm (ZMod 2) V), b.IsAlt → b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (sp6N₂ φ e z) z = z • tauSet φ e (fun B => ∀ i, B i i = 0) →
    ¬ LayerSimple (alt8C₂ φ e z) z (leviHom φ he)

@[expose] def InputTwoFactor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (T : Sylow 2 (centralizer (L : Set G)))
    (z : G), Setting L T z →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : BilinForm (ZMod 2) V), b.IsAlt → b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G) →
    IsElementaryAbelian 2 (sp6C₂ φ he z) → Sp6LayerSimple φ he z

@[expose] def InputSmallRee : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (T : Sylow 2 (centralizer (L : Set G)))
    (z : G), Setting L T z →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : BilinForm (ZMod 2) V), b.IsAlt → b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G) →
    IsElementaryAbelian 2 (sp6C₂ φ he z) → IsSimpleGroup (sp6Dstar φ he z) →
    (∃ x y : sp6Dstar φ he z, x * y ≠ y * x) →
    ∀ ℓ f : ℕ, ¬ CFSG.Blueprint.LieModel (sp6Dstar φ he z) .twistedG2 0 ℓ f

@[expose] def InputAltEightTwoFactor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (T : Sylow 2 (centralizer (L : Set G)))
    (z : G), Setting L T z →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : BilinForm (ZMod 2) V), b.IsAlt → b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (sp6N₂ φ e z) z = z • tauSet φ e (fun B => ∀ i, B i i = 0) →
    LayerSimple (alt8C₂ φ e z) z (leviHom φ he)

end CFSG.EvenSmallLie.Child3
