module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Assembly.LowTwoRank (StatedSL StatedProj)

variable {X : Type} [Group X]

abbrev Bar (L : Subgroup X) : Type := ↥L ⧸ pPrimeCore 2 ↥L

abbrev twoPart (H : Subgroup X) : ℕ := 2 ^ (Nat.card H).factorization 2

@[expose] def SectionalRankLeFour (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup X, IsPGroup 2 P → ∃ s : Finset X, s.card ≤ 4 ∧ Subgroup.closure (s : Set X) = P

structure Config (t : X) (L : Subgroup X) (p f : ℕ) : Prop where
  orderOf_eq : orderOf t = 2
  le_centralizer : L ≤ centralizer ({t} : Set X)
  isPComponent : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X)))
  prime : p.Prime
  ne_two : p ≠ 2
  one_le : 1 ≤ f
  five_le : 5 ≤ p ^ f
  lieModel : Blueprint.LieModel (Bar L) .PSL 2 p f
  isCyclic : ∀ P : Sylow 2 ↥(centralizer ({t} : Set X) ⊓ coreActionKernel L),
    IsCyclic (P : Subgroup ↥(centralizer ({t} : Set X) ⊓ coreActionKernel L))

@[expose] def TheoremOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ), Config t L p f → Blueprint.Catalog X

@[expose] def IsInducedAut (L : Subgroup X) (s : X) (φ : Bar L ≃* Bar L) : Prop :=
  ∀ l l' : L, (l' : X) = s⁻¹ * l * s →
    φ (QuotientGroup.mk l : Bar L) = (QuotientGroup.mk l' : Bar L)

@[expose] def IsFieldAutPSL2 {Y : Type} [Group Y] (φ : Y ≃* Y) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : Y ≃* StatedProj (StatedSL 2 F)) (σ : F ≃+* F),
    orderOf σ = 2 ∧ ∀ M N : StatedSL 2 F,
      (N : GL (Fin 2) F) = Matrix.GeneralLinearGroup.map σ.toRingHom (M : GL (Fin 2) F) →
        e (φ (e.symm (QuotientGroup.mk M))) = QuotientGroup.mk N

@[expose] def ActsAsFieldAut (L : Subgroup X) (s : X) : Prop :=
  ∃ φ : Bar L ≃* Bar L, IsInducedAut L s φ ∧ IsFieldAutPSL2 φ

structure DihedralStructure (t : X) (L : Subgroup X) : Prop where
  card_sylow : ∀ P : Sylow 2 ↥(coreActionKernel L),
    Nat.card (P : Subgroup ↥(coreActionKernel L)) = 2
  residual : (perfectResidual ↥(centralizer ({t} : Set X))).map
    (centralizer ({t} : Set X)).subtype = L
  normalizer_eq : normalizer (L : Set X) =
    (pPrimeCore 2 ↥(normalizer (L : Set X))).map (normalizer (L : Set X)).subtype ⊔
      centralizer ({t} : Set X)
  kernel_eq : centralizer ({t} : Set X) ⊓ coreActionKernel L =
    (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype ⊔
      zpowers t
  even : ∀ p f : ℕ, p.Prime → p ≠ 2 → Blueprint.LieModel (Bar L) .PSL 2 p f → Even f
  field : ∀ S : Sylow 2 ↥(centralizer ({t} : Set X)),
    ∃ s ∈ (S : Subgroup ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype,
      orderOf s = 2 ∧ ActsAsFieldAut L s

@[expose] def HarrisSolomonDihedralInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectionalRankLeFour X → ∀ (t : X) (L : Subgroup X) (p f : ℕ), Config t L p f →
      DihedralStructure t L

@[expose] def SectionFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X → ¬ SectionalRankLeFour X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ), Config t L p f →
      (∀ (t' : X) (L' : Subgroup X) (p' f' : ℕ), Config t' L' p' f' →
        twoPart (centralizer ({t'} : Set X)) ≤ twoPart (centralizer ({t} : Set X))) →
      DihedralStructure t L → 16 ∣ p ^ f - 1 → False

end CFSG.ComponentClassification.HarrisLit
