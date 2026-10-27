module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G]

structure SgMore (S F : Subgroup G) (g : G) : Prop where
  normF : ∀ s ∈ S, ∀ f ∈ F, s * f * s⁻¹ ∈ F
  cls : ∀ f ∈ F, ∃ s ∈ S, s * g * s⁻¹ = f * g
  ab16 : ∀ E : Subgroup G, E ≤ S ⊔ zpowers g → IsMulCommutative E → Nat.card E ≤ 16
  uniq16 : ∀ E : Subgroup G, E ≤ S ⊔ zpowers g → IsElemAbelian 2 E → Nat.card E = 16 →
    E = F ⊔ zpowers g

structure NtTwo (t g : G) (P U S F M : Subgroup G) : Prop where
  wr : Wr7 t P U
  cent : centEl P t = S
  sg : SgFacts S F g
  more : SgMore S F g
  tg : t * g = g * t
  gU : ∀ u ∈ U, g * u * g⁻¹ ∈ U
  M_card : Nat.card M = 2 ^ 6
  M_comm : ∀ x ∈ P, ⁅g, x⁆ ∈ M

structure FUFacts (g : G) (U : Subgroup G) : Prop where
  elem : IsElemAbelian 2 (centEl U g)
  card : Nat.card ↥(centEl U g) = 8
  inv : ∀ u ∈ U, g * u * g⁻¹ = u⁻¹ → u ∈ centEl U g
  cls : ∀ w ∈ centEl U g, ∃ u ∈ U, u * g * u⁻¹ = w * g
  normal : ∀ u ∈ U, ∀ w ∈ centEl U g, u * w * u⁻¹ ∈ centEl U g

structure NtOne (t g : G) (U S U0 P0 : Subgroup G) (g0 : G) : Prop where
  g0_sq : g0 ^ 2 = 1
  g0_notin : g0 ∉ U
  U0_eq : U0 = U ⊔ zpowers g0
  gg0 : g0 * (t * g0 * t⁻¹) = g
  direct : IsInternalDirect P0 U0 (conjSub t U0)
  iso : Nonempty (↥U0 ≃* ↥(S ⊔ zpowers g))

end CFSG.OddStandard.HigherRank.YamadaG23
