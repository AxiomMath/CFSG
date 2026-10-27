module

public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace E3S3O

variable {W Q : Type} [Group W] [Group Q]

theorem nonempty_mulEquiv_map (f : W →* Q) {H : Subgroup W} (hH : H ⊓ f.ker = ⊥) :
    Nonempty (↥H ≃* ↥(H.map f)) := by
  refine ⟨MulEquiv.ofBijective (f.subgroupMap H) ⟨fun x y hxy => ?_,
    MonoidHom.subgroupMap_surjective f H⟩⟩
  have h1 : f ((x : W)⁻¹ * y) = 1 := by
    have := congrArg Subtype.val hxy
    simp only [MonoidHom.subgroupMap_apply_coe] at this
    rw [map_mul, map_inv, this, inv_mul_cancel]
  have h2 : (x : W)⁻¹ * y ∈ H ⊓ f.ker := ⟨H.mul_mem (H.inv_mem x.2) y.2, h1⟩
  rw [hH, Subgroup.mem_bot] at h2
  exact Subtype.ext (inv_mul_eq_one.mp h2)

theorem isUniqueInvolution_map (f : W →* Q) {H : Subgroup W} (hH : H ⊓ f.ker = ⊥) {z : W}
    (hz : IsUniqueInvolution H z) : IsUniqueInvolution (H.map f) (f z) := by
  refine ⟨Subgroup.mem_map_of_mem f hz.mem, fun h1 => hz.ne_one ?_, by rw [← map_mul, hz.sq,
    map_one], fun y hy hy2 => ?_⟩
  · have h2 : z ∈ H ⊓ f.ker := ⟨hz.mem, h1⟩
    rw [hH, Subgroup.mem_bot] at h2
    exact h2
  · obtain ⟨x, hx, rfl⟩ := hy
    have h2 : x * x ∈ H ⊓ f.ker := ⟨H.mul_mem hx hx, by
      show x * x ∈ f.ker
      rw [MonoidHom.mem_ker, map_mul, hy2]⟩
    rw [hH, Subgroup.mem_bot] at h2
    rcases hz.unique x hx h2 with h3 | h3
    · exact Or.inl (by rw [h3, map_one])
    · exact Or.inr (by rw [h3])

theorem q8_commutator_sq : ∀ x y : QuaternionGroup 2, ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
  decide

theorem eq_of_map_eq {r : ℕ} {Φ : Set (Subgroup W)} (hΦ : TypeRFam r Φ) {f : W →* Q}
    (hc : f.ker ≤ Subgroup.center W) {M₁ M₂ : Subgroup W} (h₁ : M₁ ∈ Φ) (h₂ : M₂ ∈ Φ)
    (e₂ : ↥M₂ ≃* QuaternionGroup 2) (heq : M₁.map f = M₂.map f) : M₁ = M₂ := by
  obtain ⟨z₁, hz₁⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp h₁
  obtain ⟨z₂, hz₂⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp h₂
  set a : W := (e₂.symm (QuaternionGroup.a 1 : QuaternionGroup 2) : W) with ha
  set b : W := (e₂.symm (QuaternionGroup.xa 0 : QuaternionGroup 2) : W) with hb
  have haM : a ∈ M₂ := (e₂.symm _).2
  have hbM : b ∈ M₂ := (e₂.symm _).2
  have ec : ⁅a, b⁆ = ((e₂.symm ⁅(QuaternionGroup.a 1 : QuaternionGroup 2),
      (QuaternionGroup.xa 0 : QuaternionGroup 2)⁆ : ↥M₂) : W) := by
    simp only [ha, hb, commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hc2 : ⁅a, b⁆ * ⁅a, b⁆ = 1 := by
    rw [ec, ← Subgroup.coe_mul, ← map_mul, q8_commutator_sq, map_one, OneMemClass.coe_one]
  have hc1 : ⁅a, b⁆ ≠ 1 := by
    rw [ec]
    intro h1
    have h2 : e₂.symm ⁅(QuaternionGroup.a 1 : QuaternionGroup 2),
        (QuaternionGroup.xa 0 : QuaternionGroup 2)⁆ = 1 := Subtype.ext h1
    rw [← map_one e₂.symm] at h2
    exact absurd (e₂.symm.injective h2) (by decide)
  have hcM : ⁅a, b⁆ ∈ M₂ := by
    rw [commutatorElement_def]
    exact M₂.mul_mem (M₂.mul_mem (M₂.mul_mem haM hbM) (M₂.inv_mem haM)) (M₂.inv_mem hbM)
  have hab : ⁅a, b⁆ = z₂ := by
    rcases hz₂.unique _ hcM hc2 with h | h
    · exact absurd h hc1
    · exact h
  obtain ⟨a₁, ha₁, hfa⟩ : f a ∈ M₁.map f := heq ▸ Subgroup.mem_map_of_mem f haM
  obtain ⟨b₁, hb₁, hfb⟩ : f b ∈ M₁.map f := heq ▸ Subgroup.mem_map_of_mem f hbM
  have hpa := Subgroup.mem_center_iff.mp (hc (show a₁⁻¹ * a ∈ f.ker by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfa, inv_mul_cancel]))
  have hpb := Subgroup.mem_center_iff.mp (hc (show b₁⁻¹ * b ∈ f.ker by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfb, inv_mul_cancel]))
  have hcomm : ⁅a, b⁆ = ⁅a₁, b₁⁆ := by
    have ea : a = a₁ * (a₁⁻¹ * a) := by group
    have eb : b = b₁ * (b₁⁻¹ * b) := by group
    set p := a₁⁻¹ * a
    set p' := b₁⁻¹ * b
    rw [ea, eb]
    simp only [commutatorElement_def]
    calc a₁ * p * (b₁ * p') * (a₁ * p)⁻¹ * (b₁ * p')⁻¹ =
        a₁ * (p * (b₁ * p')) * p⁻¹ * a₁⁻¹ * p'⁻¹ * b₁⁻¹ := by group
      _ = a₁ * ((b₁ * p') * p) * p⁻¹ * a₁⁻¹ * p'⁻¹ * b₁⁻¹ := by rw [hpa (b₁ * p')]
      _ = a₁ * b₁ * (p' * a₁⁻¹) * p'⁻¹ * b₁⁻¹ := by group
      _ = a₁ * b₁ * (a₁⁻¹ * p') * p'⁻¹ * b₁⁻¹ := by rw [hpb a₁⁻¹]
      _ = a₁ * b₁ * a₁⁻¹ * b₁⁻¹ := by group
  have hz₂M₁ : z₂ ∈ M₁ := by
    rw [← hab, hcomm, commutatorElement_def]
    exact M₁.mul_mem (M₁.mul_mem (M₁.mul_mem ha₁ hb₁) (M₁.inv_mem ha₁)) (M₁.inv_mem hb₁)
  have hz : z₂ = z₁ := by
    rcases hz₁.unique _ hz₂M₁ hz₂.sq with h | h
    · exact absurd h hz₂.ne_one
    · exact h
  exact (hΦ.noTwins M₁ h₁ M₂ ⟨h₂, z₁, hz₁, hz ▸ hz₂⟩).symm

noncomputable def descend (f : W →* Q) (hf : Function.Surjective f) (σ : MulAut W)
    (hσ : f.ker.map σ.toMonoidHom = f.ker) : MulAut Q :=
  ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.congr f.ker f.ker σ hσ)).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)

theorem descend_apply (f : W →* Q) (hf : Function.Surjective f) (σ : MulAut W)
    (hσ : f.ker.map σ.toMonoidHom = f.ker) (w : W) : descend f hf σ hσ (f w) = f (σ w) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f w) =
      (QuotientGroup.mk w : W ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (QuotientGroup.quotientKerEquivOfSurjective f hf)
    (QuotientGroup.congr f.ker f.ker σ hσ
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f w))) = _
  rw [h1]
  rfl

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
