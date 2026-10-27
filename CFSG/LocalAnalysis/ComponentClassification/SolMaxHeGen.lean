module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenE
public import CFSG.Sporadic.HeldB.AutModel

public section

namespace CFSG.ComponentClassification.SolMax.HeGen

open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier Subgroup

theorem congr_conj_heConjR
    {g : Equiv.Perm (Fin 8330)} (hg : g ∈ heP) (x y : heAutGroup)
    (hxy : (x : Equiv.Perm (Fin 8330)) = g * y * g⁻¹) :
    MulAut.congr (MulAut.conj (⟨g, hg⟩ : heP))⁻¹ (heConjR x) = heConjR y := by
  refine MulEquiv.ext fun q => Subtype.ext ?_
  have e1 : MulAut.congr (MulAut.conj (⟨g, hg⟩ : heP))⁻¹ (heConjR x) q =
      (MulAut.conj (⟨g, hg⟩ : heP))⁻¹ (heConjR x (MulAut.conj (⟨g, hg⟩ : heP) q)) := rfl
  rw [e1, MulAut.conj_inv_apply, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, heConjR_apply, hxy]
  group

theorem heldGenerationInput :
    Sol78.HeldGenerationInput := by
  intro G _ _ hG s hs
  obtain ⟨θ⟩ := hG
  have hbij := ctbh_full_automorphism_permutation_model.1
  set Θ₀ : G ≃* heP := θ.trans heEquivP with hΘ₀
  obtain ⟨x, hx⟩ := hbij.2 (MulAut.congr Θ₀ s)
  have hx2 : orderOf (x : Equiv.Perm (Fin 8330)) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective heConjR hbij.1 x, hx, orderOf_congr, hs]
  obtain ⟨g, hg, y, hy, hxy, hy3⟩ : ∃ g ∈ heP, ∃ y ∈ heAutGroup,
      (x : Equiv.Perm (Fin 8330)) = g * y * g⁻¹ ∧ (y = heGenPerm 0 ∨ y = heT1P ∨ y = heAutU) := by
    by_cases hxP : (x : Equiv.Perm (Fin 8330)) ∈ heP
    · rcases involution_conj_cases hxP hx2 with ⟨c, hc, hxc⟩ | ⟨c, hc, hxc⟩
      · exact ⟨c, hc, heGenPerm 0, heP_le_heAutGroup (heGenPerm_mem (by norm_num)), hxc,
          Or.inl rfl⟩
      · exact ⟨c, hc, heT1P, heP_le_heAutGroup heT1P_mem, hxc, Or.inr (Or.inl rfl)⟩
    · obtain ⟨c, hc, hxc⟩ := exists_conj_heAutU x.2 hxP hx2
      exact ⟨c, hc, heAutU, heAutU_mem_heAutGroup, hxc, Or.inr (Or.inr rfl)⟩
  have hΘ : MulAut.congr (Θ₀.trans (MulAut.conj (⟨g, hg⟩ : heP))⁻¹) s = heConjR ⟨y, hy⟩ := by
    have e : MulAut.congr (Θ₀.trans (MulAut.conj (⟨g, hg⟩ : heP))⁻¹) s =
        MulAut.congr (MulAut.conj (⟨g, hg⟩ : heP))⁻¹ (MulAut.congr Θ₀ s) :=
      MulEquiv.ext fun _ => rfl
    rw [e, ← hx]
    exact congr_conj_heConjR hg x ⟨y, hy⟩ hxy
  refine genAt_of_congr (Θ₀.trans (MulAut.conj (⟨g, hg⟩ : heP))⁻¹) s ?_
  rw [hΘ]
  rcases hy3 with rfl | rfl | rfl
  · exact genAt_t0 hy
  · exact genAt_t1 hy
  · exact genAt_u hy

end CFSG.ComponentClassification.SolMax.HeGen
