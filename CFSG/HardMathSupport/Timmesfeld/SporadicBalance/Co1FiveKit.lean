module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F

open CFSG.Open

variable {S : Type*} [Group S]

theorem centralizer_pair_conj (c x y : S) :
    Subgroup.centralizer ({c * x * c⁻¹, c * y * c⁻¹} : Set S) =
      (Subgroup.centralizer ({x, y} : Set S)).map (MulAut.conj c : S ≃* S).toMonoidHom := by
  ext z
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨c⁻¹ * z * c, ⟨?_, ?_⟩, ?_⟩
    · calc x * (c⁻¹ * z * c) = c⁻¹ * ((c * x * c⁻¹) * z) * c := by group
        _ = c⁻¹ * (z * (c * x * c⁻¹)) * c := by rw [h1]
        _ = c⁻¹ * z * c * x := by group
    · calc y * (c⁻¹ * z * c) = c⁻¹ * ((c * y * c⁻¹) * z) * c := by group
        _ = c⁻¹ * (z * (c * y * c⁻¹)) * c := by rw [h2]
        _ = c⁻¹ * z * c * y := by group
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    refine ⟨?_, ?_⟩
    · calc c * x * c⁻¹ * (c * w * c⁻¹) = c * (x * w) * c⁻¹ := by group
        _ = c * (w * x) * c⁻¹ := by rw [h1]
        _ = c * w * c⁻¹ * (c * x * c⁻¹) := by group
    · calc c * y * c⁻¹ * (c * w * c⁻¹) = c * (y * w) * c⁻¹ := by group
        _ = c * (w * y) * c⁻¹ := by rw [h2]
        _ = c * w * c⁻¹ * (c * y * c⁻¹) := by group

theorem gLAPPrimeCoreOf_pair_conj {p : ℕ} (c x y : S)
    (H : GLAPPrimeCoreOf p (Subgroup.centralizer ({x, y} : Set S)) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({c * x * c⁻¹, c * y * c⁻¹} : Set S)) = ⊥ := by
  rw [centralizer_pair_conj, ← Coordinator.map_glaPPrimeCoreOf_of_injective p
    (MulAut.conj c : S ≃* S).toMonoidHom (MulAut.conj c : S ≃* S).injective, H,
    Subgroup.map_bot]


theorem card_closure_pair_conj (c x y : S) :
    Nat.card (Subgroup.closure ({c * x * c⁻¹, c * y * c⁻¹} : Set S)) =
      Nat.card (Subgroup.closure ({x, y} : Set S)) := by
  have e : Subgroup.closure ({c * x * c⁻¹, c * y * c⁻¹} : Set S) =
      (Subgroup.closure ({x, y} : Set S)).map (MulAut.conj c : S ≃* S).toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
  rw [e, Subgroup.card_map_of_injective (MulAut.conj c : S ≃* S).injective]


theorem orderOf_conj_eq (c s : S) : orderOf (c * s * c⁻¹) = orderOf s := by
  simpa [MulAut.conj_apply] using (MulAut.conj c : S ≃* S).orderOf_eq s

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F
