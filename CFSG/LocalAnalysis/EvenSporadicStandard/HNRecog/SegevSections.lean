module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Segev
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Local

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Section3 CFSG.Monster.GMS

variable {G : Type} [Group G]

@[expose] def gammaConj (a : G) : G →* (Gamma a ≃g Gamma a) where
  toFun g :=
    { toEquiv := MulAction.toPerm g
      map_rel_iff' := by
        intro x y
        refine ⟨fun h => ?_, fun h => twoAGraph_adj_smul g h⟩
        simpa using twoAGraph_adj_smul g⁻¹ h }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [mul_smul]

@[simp]
theorem gammaConj_apply (a : G) (g : G) (x : ConjVert a) : gammaConj a g x = g • x :=
  rfl

@[expose] def SegevSection3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (a z : G), IsF5Type a z →
    Section3.F5Local G a z

@[expose] def SegevSection4 : Prop :=
  ∀ (G G' : Type) [Group G] [Finite G] [IsSimpleGroup G] [Group G'] [Finite G']
    [IsSimpleGroup G'] (a z : G) (a' z' : G'), IsF5Type a z → Section3.F5Local G a z →
      IsF5Type a' z' → Section3.F5Local G' a' z' → Nonempty (Gamma a ≃g Gamma a')

@[expose] def SegevSection5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (a z : G), IsF5Type a z →
    Section3.F5Local G a z →
      Function.Injective (gammaConj a) ∧
        (gammaConj a).range = commutator (Gamma a ≃g Gamma a)

@[expose] def isoConj {V W : Type} {Γ₁ : SimpleGraph V} {Γ₂ : SimpleGraph W} (θ : Γ₁ ≃g Γ₂) :
    (Γ₁ ≃g Γ₁) ≃* (Γ₂ ≃g Γ₂) where
  toFun f := (θ.symm.trans f).trans θ
  invFun f := (θ.trans f).trans θ.symm
  left_inv f := by
    ext x
    simp
  right_inv f := by
    ext x
    simp
  map_mul' f g := by
    ext x
    simp [RelIso.mul_apply]

theorem map_commutator_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (commutator A).map e.toMonoidHom = commutator B := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem segevUniqueness_of_sections (h3 : SegevSection3) (h4 : SegevSection4)
    (h5 : SegevSection5) : SegevUniqueness := by
  intro G G' _ _ _ _ _ _ a z a' z' ha ha'
  have hL := h3 G a z ha
  have hL' := h3 G' a' z' ha'
  obtain ⟨θ⟩ := h4 G G' a z a' z' ha hL ha' hL'
  obtain ⟨hinj, hrange⟩ := h5 G a z ha hL
  obtain ⟨hinj', hrange'⟩ := h5 G' a' z' ha' hL'
  have hmap : (commutator (Gamma a ≃g Gamma a)).map (isoConj θ).toMonoidHom =
      commutator (Gamma a' ≃g Gamma a') :=
    map_commutator_mulEquiv (isoConj θ)
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans
    (((Subgroup.equivMapOfInjective _ (isoConj θ).toMonoidHom (isoConj θ).injective).trans
      (MulEquiv.subgroupCongr (hmap.trans hrange'.symm))).trans
        (MonoidHom.ofInjective hinj').symm)⟩

end CFSG.EvenSporadicStandard.HNRecog
