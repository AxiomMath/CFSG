module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G]

structure L34SuzOddPairData (t u : G) (V P E₁ : Subgroup G) (a : G) : Prop where
  le_centralizer : P ≤ centralizer ({u} : Set G)
  isPComponent : IsPComponent 2 (P.subgroupOf (centralizer ({u} : Set G)))
  map_ne : P.map (MulAut.conj t).toMonoidHom ≠ P
  le_sup : E₁ ≤ V ⊔ zpowers t
  card_eq : Nat.card E₁ = 4
  le_normalizer : E₁ ≤ normalizer (P : Set G)
  commutator_mem : ∀ e ∈ E₁, ∀ l ∈ P, e * l * e⁻¹ * l⁻¹ ∈ oddIn P
  mem : a ∈ P
  mul_self : a * a = 1
  commute_of_mem : ∀ e ∈ E₁, a * e = e * a
  commute_conj : a * (t * a * t⁻¹) = t * a * t⁻¹ * a
  card_sup : Nat.card ↥(E₁ ⊔ closure ({a, t * a * t⁻¹} : Set G)) = 16

end CFSG.ComponentClassification.GrSLit.L34Sec5S
