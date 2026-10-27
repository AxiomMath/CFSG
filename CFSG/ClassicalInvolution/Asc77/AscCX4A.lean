module

public import CFSG.ClassicalInvolution.Asc77.AscCX1

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4

open CFSG.Open (classicalInvolutionOddCore)

variable {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂]

theorem oddCoreOf_map_eq_bot (e : Y₁ ≃* Y₂) {A : Subgroup Y₁} (h : oddCoreOf A = ⊥) :
    oddCoreOf (A.map e.toMonoidHom) = ⊥ := by
  have hA : classicalInvolutionOddCore ↥A = ⊥ := by
    unfold oddCoreOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective).mp h
  let e₁ : ↥A ≃* ↥(A.map e.toMonoidHom) := A.equivMapOfInjective e.toMonoidHom e.injective
  have h1 : (classicalInvolutionOddCore ↥A).map e₁.toMonoidHom =
      classicalInvolutionOddCore ↥(A.map e.toMonoidHom) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e₁
  rw [hA, Subgroup.map_bot] at h1
  unfold oddCoreOf
  rw [← h1, Subgroup.map_bot]

theorem center_eq_bot_of_mulEquiv (e : Y₁ ≃* Y₂) (h : Subgroup.center Y₁ = ⊥) :
    Subgroup.center Y₂ = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hy' : e.symm y ∈ Subgroup.center Y₁ := by
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy (e g)
  rw [h, Subgroup.mem_bot] at hy'
  rw [Subgroup.mem_bot]
  have := congrArg e hy'
  rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem congr_apply (e : Y₁ ≃* Y₂) (β : MulAut Y₂) (y : Y₁) :
    MulAut.congr e.symm β y = e.symm (β (e y)) := by
  simp [MulAut.congr_apply]

theorem layerTwinFacts_map_of (e : Y₁ ≃* Y₂) {A A' : Subgroup Y₁} {z' : Y₁}
    (hcen : Subgroup.center Y₂ = ⊥) (hO : oddCoreOf (A.map e.toMonoidHom) = ⊥)
    (hO' : oddCoreOf (A'.map e.toMonoidHom) = ⊥)
    (hP : ∀ P : Subgroup (MulAut Y₁), IsPGroup 2 P →
      (∀ β ∈ P, (∀ y ∈ A, β y = y) ∧ ∀ y ∈ A', β y = y) →
        (∀ β ∈ P, β * β = 1) ∧ Nat.card P ≤ 4)
    (hβ : ∀ β : MulAut Y₁, (∀ y ∈ A, β y = y) → (∀ y ∈ A', β y = y) → β * β = 1 → β ≠ 1 →
      β ≠ MulAut.conj z' →
        ∃ x : Y₁, β x = x ∧ x * z' * x⁻¹ ≠ z' ∧ (x * z' * x⁻¹) * z' = z' * (x * z' * x⁻¹)) :
    LayerTwinFacts (A.map e.toMonoidHom) (A'.map e.toMonoidHom) (e z') := by
  set Φ : MulAut Y₂ ≃* MulAut Y₁ := MulAut.congr e.symm with hΦ
  have hfix : ∀ {B : Subgroup Y₁} {β : MulAut Y₂}, (∀ y ∈ B.map e.toMonoidHom, β y = y) →
      ∀ y ∈ B, Φ β y = y := by
    intro B β hβB y hy
    rw [hΦ, congr_apply, hβB (e y) ⟨y, hy, rfl⟩, MulEquiv.symm_apply_apply]
  have hconj : Φ (MulAut.conj (e z')) = MulAut.conj z' := by
    ext y
    rw [hΦ, congr_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    simp
  refine ⟨hcen, hO, hO', fun P hP2 hPfix => ?_, fun β hβA hβA' hβ2 hβ1 hβz => ?_⟩
  · have hP2' : IsPGroup 2 (P.map Φ.toMonoidHom) := hP2.map Φ.toMonoidHom
    obtain ⟨hsq, hcard⟩ := hP (P.map Φ.toMonoidHom) hP2' (by
      rintro _ ⟨β, hβP, rfl⟩
      exact ⟨hfix (hPfix β hβP).1, hfix (hPfix β hβP).2⟩)
    refine ⟨fun β hβP => ?_, ?_⟩
    · apply Φ.injective
      rw [map_mul, map_one]
      exact hsq _ ⟨β, hβP, rfl⟩
    · rwa [Subgroup.card_map_of_injective Φ.injective] at hcard
  · obtain ⟨x, hx, hxz, hxc⟩ := hβ (Φ β) (hfix hβA) (hfix hβA')
      (by rw [← map_mul, hβ2, map_one])
      (fun h1 => hβ1 (Φ.injective (h1.trans (map_one Φ).symm)))
      (fun h1 => hβz (Φ.injective (h1.trans hconj.symm)))
    refine ⟨e x, ?_, ?_, ?_⟩
    · have h1 : e.symm (β (e x)) = x := by rw [← congr_apply e β x]; exact hx
      calc β (e x) = e (e.symm (β (e x))) := (MulEquiv.apply_symm_apply e _).symm
        _ = e x := by rw [h1]
    · intro h1
      apply hxz
      apply e.injective
      rw [map_mul, map_mul, map_inv]
      exact h1
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hxc]

theorem layerTwinFacts_map (e : Y₁ ≃* Y₂) {A A' : Subgroup Y₁} {z' : Y₁}
    (h : LayerTwinFacts A A' z') :
    LayerTwinFacts (A.map e.toMonoidHom) (A'.map e.toMonoidHom) (e z') :=
  layerTwinFacts_map_of e (center_eq_bot_of_mulEquiv e h.1) (oddCoreOf_map_eq_bot e h.2.1)
    (oddCoreOf_map_eq_bot e h.2.2.1) h.2.2.2.1 h.2.2.2.2

end CFSG.ClassicalInvolution.Asc77.CX.CX4
