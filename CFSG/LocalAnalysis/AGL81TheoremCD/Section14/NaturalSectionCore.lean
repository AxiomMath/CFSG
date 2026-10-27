module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionOn
public import CFSG.Quasithin.Background.G6Natural

import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltSlice

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {X : Type} [Group X]

theorem exists_coreMod_of_naturalSectionOn {W L M : Subgroup X} {n : ℕ} (hn : Odd n)
    (hnat : NaturalSectionOn W L M n) :
    ∃ (θ : ↥M →* Equiv.Perm (Fin n)) (ψ : ↥⁅W, L⁆ →* ↥(CFSG.Quasithin.G6.coreMod n)),
      Function.Surjective ψ ∧
      ψ.ker = (⁅W, L⁆ ⊓ Subgroup.centralizer (L : Set X)).subgroupOf ⁅W, L⁆ ∧
      (∀ σ ∈ alternatingGroup (Fin n), ∃ l ∈ L, ∃ hl : l ∈ M, θ ⟨l, hl⟩ = σ) ∧
      (∀ m : ↥M, θ m = 1 → (m : X) ∈ Subgroup.centralizer (W : Set X)) ∧
      ∀ (m : ↥M) (w : ↥⁅W, L⁆) (hw : (m : X) * w * (m : X)⁻¹ ∈ ⁅W, L⁆),
        ψ ⟨(m : X) * w * (m : X)⁻¹, hw⟩ = CFSG.Quasithin.G6.coreAct n (θ m) (ψ w) := by
  obtain ⟨π, θ, hπsurj, hπker, hAlt, hequiv, hkerθ⟩ := hnat
  obtain ⟨e, he⟩ := CFSG.Quasithin.B69K.coreMod_equiv_altHeart hn
  let ψ : ↥⁅W, L⁆ →* ↥(CFSG.Quasithin.G6.coreMod n) := e.symm.toMonoidHom.comp π
  have hψ : ∀ w, ψ w = e.symm (π w) := fun _ => rfl
  refine ⟨θ, ψ, ?_, ?_, hAlt, hkerθ, ?_⟩
  · intro y
    obtain ⟨w, hw⟩ := hπsurj (e y)
    exact ⟨w, by rw [hψ, hw, e.symm_apply_apply]⟩
  · have hker : ψ.ker = π.ker :=
      MonoidHom.ker_comp_of_injective _ _ e.symm.injective
    rw [hker, hπker]
  · intro m w hw
    apply e.injective
    apply Multiplicative.toAdd.injective
    have hc : e (ψ ⟨(m : X) * w * (m : X)⁻¹, hw⟩) =
        π ⟨(m : X) * w * (m : X)⁻¹, hw⟩ := by rw [hψ, e.apply_symm_apply]
    have hw' : e (ψ w) = π w := by rw [hψ, e.apply_symm_apply]
    rw [hc, he (θ m) (ψ w), hw']
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π w))
    rw [hequiv m w ⟨(m : X) * w * (m : X)⁻¹, hw⟩ rfl x hx.symm, ← hx, altAct_mk]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
