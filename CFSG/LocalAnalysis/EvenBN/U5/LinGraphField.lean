module

public import CFSG.LocalAnalysis.EvenBN.U5.LinGraphFieldP
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofModelL3D
public import CFSG.LocalAnalysis.EvenBN.U5.LinModelSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinGF

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.ABGLocalTools (IsSylowOf)

theorem graphField_swaps_radicals {f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X] [Finite X]
    {A : Subgroup X} (hX : LieModel X .PSL 3 2 (2 * f)) (hA : LieModel A .PSU 3 2 f)
    {τ : MulAut X} (hτ : orderOf τ = 2) (hfix : ∀ a ∈ A, τ a = a)
    (hout : τ ∉ (MulAut.conj : X →* MulAut X).range) {V V₁ V₂ : Subgroup X}
    (hV : IsSylowOf 2 V ⊤) (hrad : Radicals V V₁ V₂ ((2 ^ f) ^ 2))
    (hτV : V.map τ.toMonoidHom = V) :
    V₁.map τ.toMonoidHom = V₂ ∧ V₂.map τ.toMonoidHom = V₁ := by
  obtain ⟨K, hF, h, σ, e, hσ, hey, -⟩ := S8c.canonical_form hf hX hA hτ hfix hout
  haveI := h.finite
  haveI := h.charP
  have hK : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hyE : fieldAut 3 K σ * dualAut 3 K ∉ semilinearAutGroup 3 K := by
    intro hyE
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) (n := 3) le_rfl
    have : dualAut 3 K = (fieldAut 3 K σ)⁻¹ * (fieldAut 3 K σ * dualAut 3 K) := by group
    rw [this]
    exact mul_mem (inv_mem (fieldAut_mem_semilinearAutGroup σ)) hyE
  have hVe : IsSylowOf 2 (V.map e.toMonoidHom) ⊤ := LinCase.l3syl_isSylowOf_map e hV
  have hrade : Radicals (V.map e.toMonoidHom) (V₁.map e.toMonoidHom) (V₂.map e.toMonoidHom)
      (Nat.card K) := by
    rw [hK]
    exact hrad.map e.injective
  have hmap : ∀ W : Subgroup X,
      (W.map e.toMonoidHom).map (fieldAut 3 K σ * dualAut 3 K).toMonoidHom =
        (W.map τ.toMonoidHom).map e.toMonoidHom := by
    intro W
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨τ w, ⟨w, hw, rfl⟩, hey w⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨e w, ⟨w, hw, rfl⟩, (hey w).symm⟩
  have hyV : (V.map e.toMonoidHom).map (fieldAut 3 K σ * dualAut 3 K).toMonoidHom =
      V.map e.toMonoidHom := by
    rw [hmap, hτV]
  obtain ⟨h1, h2⟩ := swap_radicals _ hyE hVe hrade hyV
  rw [hmap] at h1 h2
  exact ⟨Subgroup.map_injective e.injective h1, Subgroup.map_injective e.injective h2⟩

end LinGF

end CFSG.LocalAnalysis.EvenBN.U5
