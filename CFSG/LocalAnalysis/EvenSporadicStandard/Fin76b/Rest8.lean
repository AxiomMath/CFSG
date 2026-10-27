
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma67
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Finish

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] def Fin76bInnerRest₈ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → BetaData65 E β →
    ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) → z ∈ S →
      Nonempty (S ≃* DihedralGroup 4) → (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) →
      (∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
        N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
        (N : Set (centralizer (E : Set G))) *
          (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) =
            Set.univ) →
      (∃ hz : z ∈ centralizer ({β} : Set G),
        WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩)) →
      (∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t) →
      ∃ Rs R : Subgroup G, IsPGroup 2 Rs ∧ R ≤ Rs ∧ R.relIndex Rs = 2 ∧ z ∈ Rs ∧ z ∉ R ∧
        (∀ g : G, g * z * g⁻¹ ∈ Rs → ∃ r ∈ Rs, g * z * g⁻¹ = r * z * r⁻¹) ∧
        ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G))

theorem fin76bInnerRest₇_of_rest₈ (hZ : Fin76bNotZ2A6) (hBD : Fin76bBetaData)
    (hWF : Fin76bWFacts) (h8 : Fin76bInnerRest₈) : Fin76bInnerRest₇ := by
  intro G _ _ L z t T₀ E Q x β B hconf S hS2 hSC hSmax hzS hD8 hBS hodd
  have hW := hWF G L z t T₀ E Q x β B hconf
  have h66 := lemma66 hZ hconf hW
  have h67 := lemma67 hZ hBD hconf hW hS2 hSC hzS hBS
  obtain ⟨Rs, R, hRs, hRR, hidx, hzRs, hzR, hfus, hcent⟩ :=
    h8 G L z t T₀ E Q x β B hconf hW (hBD G L z t T₀ E Q x β B hconf hW) S hS2 hSC hSmax hzS hD8
      hBS hodd h66 h67
  have := hconf.std.simple
  exact false_of_fusion_pair hconf.std.nonabelian hconf.cfg.z_order hRs hRR hidx hzRs hzR hfus
    hcent

end CFSG.EvenSporadicStandard.Fin76b
