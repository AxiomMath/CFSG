module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Facts
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeFinal
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Link
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SplitC
open CFSG.EvenSmallLie.OmegaEight.CPrime CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

theorem card_U_plus [Finite G] {L U : Subgroup G} (hZ : center L = ⊥)
    (hL : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) (hU2 : IsPGroup 2 U) :
    Nat.card U = 4096 := by
  have hcard : Nat.card L = 2 ^ 12 * 42525 := by
    rw [← Nat.card_congr (mulEquivQuotientCenter hZ).toEquiv, card_of_lieModel hL]
    norm_num
  exact card_eq_of_max hUL hUmax hU2 hcard (by decide)

theorem card_U_minus [Finite G] {L U : Subgroup G}
    (hL : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1) (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) (hU2 : IsPGroup 2 U) :
    Nat.card U = 4096 := by
  have hcard : Nat.card L = 2 ^ 12 * 48195 := by
    rw [OmegaEightMinus.card_of_lieModel_minus hL]
    norm_num
  exact card_eq_of_max hUL hUmax hU2 hcard (by decide)

theorem false_of_shapeC' [Finite G] {ε : Eps}
    (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x) {t c a : G} {L U Q P : Subgroup G}
    {ψ : V6 → G} {p : Fin 6 → G} {v₀ : ℕ} (hK : StepK t L) (hS : ShapeC' t L c)
    (hR : RadicalData ε L U Q P a ψ p)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) (hAc : AutCent L Q)
    (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U) (hv₀ : v₀ < 64) (hq₀ : qfB ε v₀ = true)
    (hcact : ∀ v, c * ψ v * c⁻¹ = ψ (toMat 6 6 (reflRows ε v₀) *ᵥ v)) : False :=
  false_of_sup_zpowers hG hnab hK.orderOf_eq hS.cprime.sq hK.not_mem hK.le_centralizer
    hS.c_mem_normalizer hS.centralizer_eq hR hUmax hcU hv₀ hq₀ hcact
    (hAc.centralizer_le hR.Q_le_L hK.le_centralizer hK.le_normalizer hK.inf_eq)

theorem false_of_shapeD' [Finite G] {ε : Eps}
    (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x) {t c r a : G}
    {L U Q P : Subgroup G} {ψ : V6 → G} {p : Fin 6 → G} {v₀ : ℕ} (hK : StepK t L)
    (hS : ShapeD' t L c r) (hNQ : ∀ n ∈ L ⊔ zpowers r, n ∈ normalizer (Q : Set G) → n ∈ L)
    (hR : RadicalData ε L U Q P a ψ p)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) (hAc : AutCent L Q)
    (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U) (hv₀ : v₀ < 64) (hq₀ : qfB ε v₀ = true)
    (hcact : ∀ v, c * ψ v * c⁻¹ = ψ (toMat 6 6 (reflRows ε v₀) *ᵥ v)) : False :=
  false_of_sup hG hnab hK.orderOf_eq hS.cprime.sq le_sup_left hS.le_centralizer hS.t_not_mem
    hS.c_mem_normalizer hS.centralizer_eq hS.odd hS.le_normalizer hNQ hR hUmax hcU hv₀ hq₀ hcact
    (hAc.centralizer_le hR.Q_le_L hK.le_centralizer hK.le_normalizer hK.inf_eq)

section Plus

theorem setup_of_shapeB {t r : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}
    (hK : StepK t L) (hS : ShapeB t L r) (hR : RadicalData .plus L U Q P a ψ p)
    (hF : LinkFacts .plus L U Q P a ψ p u)
    (hNQ : ∀ x ∈ centralizer ({t} : Set G),
      x ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) → x ∈ L ⊔ zpowers t) :
    Setup .plus t L U Q P a ψ p := by
  refine ⟨hK.shapeB_shapeAB hS hF.U_le_L hF.U_max hF.Q_le_L hF.P_eq hF.cent_Q ?_ hNQ, hR⟩
  intro x hx y hy
  obtain ⟨v, rfl⟩ := hF.mem_ψ x hx
  obtain ⟨w, rfl⟩ := hF.mem_ψ y hy
  rw [← hF.ψ_add, ← hF.ψ_add, add_comm]

theorem false_of_shapeB_of_link [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) {t r : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
    {p u : Fin 6 → G} (hK : StepK t L) (hS : ShapeB t L r) (hR : RadicalData .plus L U Q P a ψ p)
    (hU : UGens .plus U Q ψ u) (hF : LinkFacts .plus L U Q P a ψ p u)
    (hNQ : ∀ x ∈ centralizer ({t} : Set G),
      x ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) → x ∈ L ⊔ zpowers t)
    (hL9 : L9 t Q) : False :=
  (setup_of_shapeB hK hS hR hF hNQ).false_of_setup_plus hG hnab hL9 hU

end Plus

end CFSG.EvenSmallLie.OmegaEight.Stage0
