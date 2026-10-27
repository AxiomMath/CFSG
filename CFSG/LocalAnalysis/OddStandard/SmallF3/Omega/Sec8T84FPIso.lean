module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPModel

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

open scoped Pointwise

theorem sec8t84_iso_model {Y : Type} [Group Y]
    {E H : Subgroup Y} [E.Normal] (hE : IsElemAb2 E 4)
    (hH : Nonempty (↥H ≃* alternatingGroup (Fin 6))) (hEH : E ⊓ H = ⊥) (hEH' : E ⊔ H = ⊤)
    (htr : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → ∃ h ∈ H, h * a * h⁻¹ = b) :
    ∃ Θ : Y ≃* Sec8T84FPM0 Certificates.certificate442267,
      E.map Θ.toMonoidHom = Sec8T84FPV0 Certificates.certificate442267 := by
  let F := Certificates.certificate442267
  have hdisj : Disjoint E H := disjoint_iff.mpr hEH
  have hmul : (E : Set Y) * (H : Set Y) = Set.univ := by
    rw [← Subgroup.normal_mul E H, hEH']
    rfl
  have hc : E.IsComplement' H := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  obtain ⟨e, ψ, hact⟩ := sec8t84_coords (Y := Y) (E := E) (H := H) hE hH htr
  let φ' : ↥H →* MulAut ↥E :=
    (E.normalizerMonoidHom).comp (Subgroup.inclusion (E.normalizer_eq_top ▸ le_top))
  have hφ : ∀ g : ↥H, φ' g = MulAut.conjNormal (g : Y) := by
    intro g
    ext x
    simp only [φ', MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion, MulAut.conjNormal_apply]
  have hcomm : ∀ g : ↥H, (φ' g).trans e = e.trans (sec8t84FPAct F (ψ g)) := by
    intro g
    apply MulEquiv.ext
    intro x
    apply Multiplicative.toAdd.injective
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, sec8t84FPAct_apply F, hφ g]
    exact hact g x
  let Φ : ↥E ⋊[φ'] ↥H ≃* Y := SemidirectProduct.mulEquivSubgroup hc
  let Ψ : ↥E ⋊[φ'] ↥H ≃* Sec8T84FPM0 F := SemidirectProduct.congr e ψ hcomm
  let Θ : Y ≃* Sec8T84FPM0 F := Φ.symm.trans Ψ
  have hΦ : ∀ n : ↥E, Φ (SemidirectProduct.inl n) = (n : Y) := by
    intro n
    change SemidirectProduct.mulEquivSubgroup hc (SemidirectProduct.inl n) = (n : Y)
    rw [SemidirectProduct.mulEquivSubgroup_apply]
    simp
  have hΨ : ∀ n : ↥E, Ψ (SemidirectProduct.inl n) = SemidirectProduct.inl (e n) := by
    intro n
    change SemidirectProduct.congr e ψ hcomm (SemidirectProduct.inl n) =
      SemidirectProduct.inl (e n)
    apply SemidirectProduct.ext <;>
      simp [SemidirectProduct.congr_apply_left, SemidirectProduct.congr_apply_right]
  refine ⟨Θ, le_antisymm ?_ ?_⟩
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨e ⟨x, hx⟩, ?_⟩
    have hxE : Φ.symm x = SemidirectProduct.inl ⟨x, hx⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact (hΦ ⟨x, hx⟩).symm
    calc SemidirectProduct.inl (e ⟨x, hx⟩) = Ψ (SemidirectProduct.inl ⟨x, hx⟩) :=
          (hΨ ⟨x, hx⟩).symm
      _ = Ψ (Φ.symm x) := by rw [hxE]
      _ = Θ x := rfl
  · rintro z ⟨v, rfl⟩
    refine Subgroup.mem_map.mpr ⟨Φ (SemidirectProduct.inl (e.symm v)), ?_, ?_⟩
    · rw [hΦ (e.symm v)]
      exact (e.symm v).2
    · show Θ (Φ (SemidirectProduct.inl (e.symm v))) = SemidirectProduct.inl v
      calc Θ (Φ (SemidirectProduct.inl (e.symm v)))
          = Ψ (Φ.symm (Φ (SemidirectProduct.inl (e.symm v)))) := rfl
        _ = Ψ (SemidirectProduct.inl (e.symm v)) := by rw [MulEquiv.symm_apply_apply]
        _ = SemidirectProduct.inl (e (e.symm v)) := hΨ (e.symm v)
        _ = SemidirectProduct.inl v := by rw [MulEquiv.apply_symm_apply]

end CFSG.OddStandard.SmallF3.Omega
