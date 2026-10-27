module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldChain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldBruhat
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldRest

public section

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X} {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

namespace FoldData

theorem rgd2 (hf : FoldData R φ) {r₁' r₂' : X} (h1 : φ r₁' = r₁') (h1H : r₁⁻¹ * r₁' ∈ H)
    (h2 : φ r₂' = r₂') (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) :
    RGD2 3 (H ⊓ foldFix φ) r₁' r₂' (U ⊓ foldFix φ) (foldRoot φ root) :=
  hf.rgd2_aux h1 h1H h2 h2H hf.carrier_eq_F hf.unique_F hf.reverse_eq_F hf.subgroup_F
    (hf.rank₁_F h1 h1H) (hf.rank₂_F h2 h2H)

theorem exists_rgd2 (hf : FoldData R φ) :
    ∃ r₁' r₂' : X, φ r₁' = r₁' ∧ φ r₂' = r₂' ∧ r₁⁻¹ * r₁' ∈ H ∧
      (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H ∧
      RGD2 3 (H ⊓ foldFix φ) r₁' r₂' (U ⊓ foldFix φ) (foldRoot φ root) := by
  obtain ⟨r₁', h1, h1H⟩ := hf.exists_fixed_lift₁
  obtain ⟨r₂', h2, h2H⟩ := hf.exists_fixed_lift₂
  exact ⟨r₁', r₂', h1, h2, h1H, h2H, hf.rgd2 h1 h1H h2 h2H⟩

end FoldData

end CFSG.GH74.GLS.SP
