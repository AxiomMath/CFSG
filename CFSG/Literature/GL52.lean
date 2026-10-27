module

public import CFSG.Literature.GL52Classes
public import CFSG.Literature.GL52Transport

public section

namespace CFSG.Literature.GL52

open CFSG

section Transport

variable (c : G)

theorem centralizer_structure_conj {x : G} {K : Subgroup G}
    (h : K ≤ Subgroup.centralizer {x} ∧ Subgroup.zpowers x ⊓ K = ⊥ ∧
      Subgroup.zpowers x ⊔ K = Subgroup.centralizer {x}) :
    K.map (MulAut.conj c).toMonoidHom ≤ Subgroup.centralizer {c * x * c⁻¹} ∧
      Subgroup.zpowers (c * x * c⁻¹) ⊓ K.map (MulAut.conj c).toMonoidHom = ⊥ ∧
      Subgroup.zpowers (c * x * c⁻¹) ⊔ K.map (MulAut.conj c).toMonoidHom =
        Subgroup.centralizer {c * x * c⁻¹} := by
  obtain ⟨h1, h2, h3⟩ := h
  have hC : Subgroup.centralizer {c * x * c⁻¹} =
      (Subgroup.centralizer {x}).map (MulAut.conj c).toMonoidHom := by
    rw [map_centralizer_singleton]
    rfl
  have hZ : Subgroup.zpowers (c * x * c⁻¹) =
      (Subgroup.zpowers x).map (MulAut.conj c).toMonoidHom := by
    rw [map_zpowers_equiv]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hC]; exact Subgroup.map_mono h1
  · rw [hZ, ← map_inf_equiv, h2, map_bot_equiv]
  · rw [hZ, hC, ← Subgroup.map_sup, h3]

end Transport

theorem order_three_centralizer
    {τ : G} (hτ : orderOf τ = 3) :
    (commDim τ = 4 ∧ ∃ K : Subgroup G, K ≤ Subgroup.centralizer {τ} ∧
        Subgroup.zpowers τ ⊓ K = ⊥ ∧ Subgroup.zpowers τ ⊔ K = Subgroup.centralizer {τ} ∧
        Nonempty (K ≃* alternatingGroup (Fin 5))) ∨
      (commDim τ = 2 ∧ ∃ K : Subgroup G, K ≤ Subgroup.centralizer {τ} ∧
        Subgroup.zpowers τ ⊓ K = ⊥ ∧ Subgroup.zpowers τ ⊔ K = Subgroup.centralizer {τ} ∧
        Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) ∧
        Nonempty (K ≃* GL (Fin 3) (ZMod 2))) := by
  rcases order_three_fixCount hτ with h | h
  · refine Or.inl ⟨commDim_eq_of_fixCount (by norm_num) (by norm_num) h, ?_⟩
    obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_tau1 hτ h)
    obtain ⟨h1, h2, h3, ⟨e⟩⟩ := tau1_structure
    obtain ⟨k1, k2, k3⟩ := centralizer_structure_conj c ⟨h1, h2, h3⟩
    exact ⟨_, k1, k2, k3, ⟨(equivMap _ subK1).symm.trans e⟩⟩
  · refine Or.inr ⟨commDim_eq_of_fixCount (by norm_num) (by norm_num) h, ?_⟩
    obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_tau2 hτ h)
    obtain ⟨h1, h2, h3, ⟨e⟩, ⟨e'⟩⟩ := tau2_structure
    obtain ⟨k1, k2, k3⟩ := centralizer_structure_conj c ⟨h1, h2, h3⟩
    exact ⟨_, k1, k2, k3, ⟨(equivMap _ subK2).symm.trans e⟩,
      ⟨(equivMap _ subK2).symm.trans e'⟩⟩

end CFSG.Literature.GL52
