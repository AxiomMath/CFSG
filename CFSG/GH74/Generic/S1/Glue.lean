module

public import CFSG.GH74.Generic.S1.Props

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix

@[expose] def LinClassify : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F % 4 = 3 → ∀ α : MulAut ↥(StatedSL 4 F),
    α * α = 1 → (∀ k : ↥(StatedSL 4 F), α ≠ MulAut.conj k) →
      GoodFixedCentral (Nat.card F = 3) α ∨ IsReflection (StatedSL 4 F) α ∨
        IsGraphLike (StatedSL 4 F) α

@[expose] def UniClassify : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (q : ℕ), Nat.card F = q ^ 2 → q % 4 = 1 →
    ∀ α : MulAut ↥(StatedSU 4 q F), α * α = 1 → (∀ k : ↥(StatedSU 4 q F), α ≠ MulAut.conj k) →
      GoodFixedCentral False α ∨ IsReflection (StatedSU 4 q F) α ∨
        IsGraphFieldLike (StatedSU 4 q F) q α

theorem congr_mul_self_eq_one {K S : Type} [Group K] [Group S] (e : K ≃* S) {α : MulAut K}
    (hα : α * α = 1) : MulAut.congr e α * MulAut.congr e α = 1 := by
  rw [← map_mul, hα, map_one]

theorem congr_not_inner {K S : Type} [Group K] [Group S] (e : K ≃* S) {α : MulAut K}
    (hout : ∀ k : K, α ≠ MulAut.conj k) : ∀ s : S, MulAut.congr e α ≠ MulAut.conj s := by
  intro s h
  apply hout (e.symm s)
  apply MulEquiv.ext
  intro k
  have h1 : e (α (e.symm (e k))) = s * e k * s⁻¹ := congrArg (fun β : MulAut S => β (e k)) h
  rw [MulEquiv.symm_apply_apply] at h1
  apply e.injective
  rw [h1]
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem congr_symm_congr {K S : Type} [Group K] [Group S] (e : K ≃* S) (α : MulAut K) :
    MulAut.congr e.symm (MulAut.congr e α) = α := by
  apply MulEquiv.ext
  intro k
  simp [MulAut.congr_apply]

theorem s1OuterClassification_of_native (hL : LinClassify) (hU : UniClassify) :
    S1OuterClassification := by
  intro K _ hK α hα hout
  rcases hK with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · rcases hL F hF (MulAut.congr e α) (congr_mul_self_eq_one e hα) (congr_not_inner e hout) with
      hA | hR | hG
    · left
      have h1 := (hA.of_mulEquiv e.symm).mono (T' := ThreeModel K) (fun h => ⟨F, inferInstance,
        inferInstance, h, Or.inl ⟨e⟩⟩)
      rwa [congr_symm_congr] at h1
    · right; left
      exact Or.inl ⟨F, inferInstance, inferInstance, e, hF, hR⟩
    · right; right
      exact Or.inl ⟨F, inferInstance, inferInstance, e, hF, hG⟩
  · rcases hU F q hF hq (MulAut.congr e α) (congr_mul_self_eq_one e hα) (congr_not_inner e hout) with
      hA | hR | hG
    · left
      have h1 := (hA.of_mulEquiv e.symm).mono (T' := ThreeModel K) (fun h => h.elim)
      rwa [congr_symm_congr] at h1
    · right; left
      exact Or.inr ⟨q, F, inferInstance, inferInstance, e, hF, hq, hR⟩
    · right; right
      exact Or.inr ⟨q, F, inferInstance, inferInstance, e, hF, hq, hG⟩

theorem s1_shapeCase_of_native (hL : LinClassify) (hU : UniClassify) (hExo : S1ExoticExcluded)
    (hNbhd : S1Nbhd) (hE : S1LevelE) : S_shapeCaseMaxNT @ShapeS1 :=
  s1_shapeCase_of_props (s1OuterClassification_of_native hL hU) hExo hNbhd hE

end CFSG.GH74.Generic.S1
