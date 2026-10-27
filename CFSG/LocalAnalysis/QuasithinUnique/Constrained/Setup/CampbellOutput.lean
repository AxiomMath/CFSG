module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellStruct2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellUtil

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2

section Output

variable {G : Type*} [Group G]

section Out

variable {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

theorem natural_center_Sylow_translate_produces_output [Finite G] [Finite k]
    (h : IsNatBase S ρ (Ecore G) ψ) (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hα : (S : Subgroup G) = CFSG.pCore 2 G ⊔ aimg (S : Subgroup G) α (Vmod G)) :
    ⁅CFSG.pCore 2 G, Kodd G⁆ = Vmod G ∧ Vmod G ≤ Ecore G ∧
      ∃ β : (⁅CFSG.pCore 2 G, Kodd G⁆ : Subgroup G) →* Multiplicative (Fin 2 → k),
        Function.Surjective β ∧
        β.ker = ((⁅CFSG.pCore 2 G, Kodd G⁆ : Subgroup G) ⊓ Subgroup.center G).subgroupOf
          (⁅CFSG.pCore 2 G, Kodd G⁆ : Subgroup G) ∧
        (∀ (g : G) (u u' : (⁅CFSG.pCore 2 G, Kodd G⁆ : Subgroup G)),
          (u' : G) = g * u * g⁻¹ → Multiplicative.toAdd (β u') =
            (ρ g : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (β u))) := by
  classical
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  have hVS : Vmod G ≤ (S : Subgroup G) :=
    Vmod_le_Ecore.trans (Ecore_le_core.trans (core_le_sylow S))
  have hVn : ((Vmod G).subgroupOf (S : Subgroup G)).Normal := inferInstance
  have hVe : CFSG.IsElementaryAbelian 2 (Vmod G) :=
    isElementaryAbelian_iff.mpr ⟨fun a ha b hb =>
      Ecore_commute (Vmod_le_Ecore ha) (Vmod_le_Ecore hb), fun a ha => Vmod_sq ha⟩
  have hSV : ⁅(S : Subgroup G), Vmod G⁆ ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [h.sylow_commutator_Vmod]; exact inf_le_right
  have hgen : ⨆ g : G, cj (S : Subgroup G) g = ⊤ := by
    rw [iSup_cj_eq_normalClosure]; exact h.normalClosure_sylow_eq_top
  obtain ⟨hQK, -⟩ := sylow_module_translate_centralizes_core hQ2 S hgen hVS hVn hVe hSV α hα
  have hQKE : ⁅CFSG.pCore 2 G, Kodd G⁆ ≤ Ecore G := hQK
  have hEq : ⁅CFSG.pCore 2 G, Kodd G⁆ = Vmod G := by
    have : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
    exact (prime_residual_commutator_through_normal_layer (p := 2) (E := Ecore G)
      (Q := CFSG.pCore 2 G) (K := Kodd G) Ecore_le_core hQ2 Kodd_closure hQK).1
  refine ⟨hEq, Vmod_le_Ecore, ψ.comp (Subgroup.inclusion hQKE), ?_, ?_, ?_⟩
  · intro w
    obtain ⟨v, hv, hψ⟩ := h.ψ_Vmod_surj w
    exact ⟨⟨v, hEq.symm ▸ hv⟩, hψ⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : (ψ.comp (Subgroup.inclusion hQKE)) u = 1 ↔
        ((Subgroup.inclusion hQKE u : Ecore G) : G) ∈ Subgroup.center G := h.ψ_eq_one_iff
    rw [h1]
    exact ⟨fun hc => ⟨u.2, hc⟩, fun hc => hc.2⟩
  · intro g u u' hu
    exact h.ψ_equiv g (Subgroup.inclusion hQKE u) (Subgroup.inclusion hQKE u') hu

end Out

end Output

end CFSG.QuasithinUnique.Setup.Campbell
