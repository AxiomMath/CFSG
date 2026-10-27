module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95UHyp

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem ivk95_u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 →
    Ivk95Empty (fun X _ => LieModel X .PSU 5 p f) := by
  intro p f hp hf hmod
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hf)
    omega
  refine ivk95_empty_of_cfg fun J _ _ hJ z hcfg => ?_
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have hud : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud (r := 2) (ε := 1) (by norm_num)
    (by norm_num)).1
  let θ : J ≃* hypPSU hud 2 1 := (e.trans (unitaryPSUEquiv hud (by norm_num)).symm).trans
    (hypProjTransport hud (R := R) hR).symm
  exact ivk95_hyp_false hud hp2 (r := 2) (ε := 1) (Or.inr (by norm_num)) θ hcfg

end CFSG.GH74.GLS.IVK.Proofs2
