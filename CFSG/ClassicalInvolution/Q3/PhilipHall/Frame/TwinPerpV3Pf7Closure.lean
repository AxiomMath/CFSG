module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf7Distinct
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf6Trans
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Closure





theorem transitive_of_closure {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}
    (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card X < n) (hS : Q8Section X Φ) {J : Subgroup X}
    (hJ : J ∈ Φ) (hcl : ∀ M ∈ Φ, M ≤ ⨆ x : X, conjSub x J) :
    ∀ M ∈ Φ, ∃ y : X, conjSub y J = M := by
  intro M₀ hM₀
  by_contra hnot
  push Not at hnot
  have h4' := h4 X hlt Φ hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
  have hcomm : ∀ x : X, Commutes (conjSub x J) M₀ := fun x =>
    h4' _ (hS.hyp.conjInvariant x J hJ) M₀ hM₀ (by
      rintro ⟨g, hg⟩
      exact hnot (g * x) (by rw [conjSub_mul]; exact hg))
  have hle : (⨆ x : X, conjSub x J) ≤ Subgroup.centralizer (M₀ : Set X) := by
    refine iSup_le fun x a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm x a ha b hb).symm
  obtain ⟨R₀, hR₀, hR₀s, -⟩ := exists_mem_RSet_ge hM₀ (IsPGroup.of_bot (G := X)) bot_le
  obtain ⟨x, hx, y, hy, hxy⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hS.hyp hR₀).exists_not_commute
  have hy' := Subgroup.mem_centralizer_iff.mp (hle (hcl M₀ hM₀ (hR₀s.1 hy))) x (hR₀s.1 hx)
  exact hxy hy'

section Std

variable {n : ℕ}

@[expose] def V3LayerClosure (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ K₄ : Subgroup Y,
        FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ →
          SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
            (∀ J ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂), IsPGroup 2 J) →
            HasLifts (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
            ExactSylow (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
            Nonempty (OmegaLieU 3 1 (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R))
              (u₁ * u₂)))) →
              ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                M ≤ ⨆ x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
                    classicalInvolutionOddCore
                      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
                  conjSub x (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃)

theorem v3LayerTransitive_of_closure (h4 : Thm4RTwinBelow 3 n) (hcl : V3LayerClosure n) :
    V3LayerTransitive n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hno h2' hl hex hLie
  have hd := hStd.datum
  obtain ⟨hmem, -⟩ := v3_tq_members hStd hF
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  have hJ := secImg_mem_secFam hmem
  have htr := transitive_of_closure h4 hlt hS hJ
    (hcl Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hno h2' hl hex hLie)
  refine ⟨fun M hM N hN => ?_, v3_secImg_ne hStd hF⟩
  obtain ⟨x, hx⟩ := htr M hM
  obtain ⟨y, hy⟩ := htr N hN
  refine ⟨y * x⁻¹, ?_⟩
  rw [conjSub_mul, ← hx, conjSub_inv_conjSub, hy]

theorem v3LayerTrans_of_closure (h4 : Thm4RTwinBelow 3 n) (hcl : V3LayerClosure n) :
    V3LayerTrans n :=
  v3LayerTrans_of_transitive (v3LayerTransitive_of_closure h4 hcl)

end Std

end Closure

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
