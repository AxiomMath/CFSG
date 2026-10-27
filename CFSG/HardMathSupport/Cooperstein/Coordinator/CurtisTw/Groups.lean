module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Basic

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] def Xg (a : Fin t.foldedTag.rank) : Subgroup (ModGL t.tag K) :=
  rootSpan t.tag K (simpleOrbitRoots t a) ⊓ twistedFixedGroup t K σ

@[expose] def Yg (a : Fin t.foldedTag.rank) : Subgroup (ModGL t.tag K) :=
  rootSpan t.tag K (negOrbitRoots t a) ⊓ twistedFixedGroup t K σ

@[expose] def Qg (a : Fin t.foldedTag.rank) : Subgroup (ModGL t.tag K) :=
  rootSpan t.tag K (negComplementRoots t a) ⊓ twistedFixedGroup t K σ

variable {t K σ}

theorem Xg_le (a : Fin t.foldedTag.rank) : Xg t K σ a ≤ graphFixedPosUnipotent t K σ :=
  inf_le_inf_right _ (rootSpan_le_posUnipotent (simpleOrbitRoots_pos a))

theorem Yg_le (a : Fin t.foldedTag.rank) : Yg t K σ a ≤ graphFixedNegUnipotent t K σ := by
  refine inf_le_inf_right _ (rootSpan_mono ?_)
  rintro _ ⟨i, -, rfl⟩
  exact ⟨isRoot_neg_single _ i, by rw [height_neg, height_single]; omega⟩

theorem Qg_le (a : Fin t.foldedTag.rank) : Qg t K σ a ≤ graphFixedNegUnipotent t K σ :=
  inf_le_inf_right _ (rootSpan_mono fun _ h => h.1)

theorem mem_Xg_iff (a : Fin t.foldedTag.rank) {g : ModGL t.tag K} :
    g ∈ Xg t K σ a ↔ ∃ c : orbitField t K σ a, (orbitX t K σ a c : ModGL t.tag K) = g :=
  mem_rootSpan_simpleOrbitRoots_iff σ a

theorem mem_Yg_iff (a : Fin t.foldedTag.rank) {g : ModGL t.tag K} :
    g ∈ Yg t K σ a ↔ ∃ c : orbitField t K σ a, (orbitY t K σ a c : ModGL t.tag K) = g := by
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := (orbitYEquiv t σ a).surjective ⟨g, hg⟩
    refine ⟨Multiplicative.toAdd x, ?_⟩
    have := congrArg Subtype.val hx
    rw [← coe_orbitYEquiv t (σ := σ) a (Multiplicative.toAdd x)]
    exact this
  · rintro ⟨c, rfl⟩
    rw [← coe_orbitYEquiv t (σ := σ) a c]
    exact (orbitYEquiv t σ a (Multiplicative.ofAdd c)).2

theorem orbitX_mem_Xg (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) ∈ Xg t K σ a :=
  (mem_Xg_iff a).2 ⟨c, rfl⟩

theorem orbitY_mem_Yg (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitY t K σ a c : ModGL t.tag K) ∈ Yg t K σ a :=
  (mem_Yg_iff a).2 ⟨c, rfl⟩

section Conj

variable (D : LongestData t)

theorem conj_mem_negUnipotent_iff (g : ModGL t.tag K) :
    canonicalRep (coxeterSystem t.tag) K D.w * g *
        (canonicalRep (coxeterSystem t.tag) K D.w)⁻¹ ∈ graphFixedNegUnipotent t K σ ↔
      g ∈ graphFixedPosUnipotent t K σ := by
  have h := conj_mem_rootSpan_inf_iff σ D.mem (S := {α | IsRoot t.tag α ∧ 0 < height α})
    (fun α hα => hα.1) g
  rw [D.image_smul_posRoots] at h
  exact h

theorem conj_mem_Yg_iff (a : Fin t.foldedTag.rank) (g : ModGL t.tag K) :
    canonicalRep (coxeterSystem t.tag) K D.w * g *
        (canonicalRep (coxeterSystem t.tag) K D.w)⁻¹ ∈ Yg t K σ a ↔ g ∈ Xg t K σ a := by
  have h := conj_mem_rootSpan_inf_iff σ D.mem (S := simpleOrbitRoots t a)
    (fun α hα => (simpleOrbitRoots_pos a α hα).1) g
  rw [D.image_smul_simpleOrbitRoots] at h
  exact h

theorem conj_mem_Qg_iff (a : Fin t.foldedTag.rank) (g : ModGL t.tag K) :
    canonicalRep (coxeterSystem t.tag) K D.w * g *
        (canonicalRep (coxeterSystem t.tag) K D.w)⁻¹ ∈ Qg t K σ a ↔
      g ∈ graphFixedSimpleComplement t K σ a := by
  have h := conj_mem_rootSpan_inf_iff σ D.mem (S := simpleComplementRoots t a)
    (fun α hα => hα.1.1) g
  rw [D.image_smul_simpleComplementRoots] at h
  exact h

end Conj

section ConjSimple

variable (a : Fin t.foldedTag.rank) (g : ModGL t.tag K)

theorem conj_simple_mem_Yg_iff :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * g *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹ ∈ Yg t K σ a ↔
      g ∈ Xg t K σ a := by
  have h := conj_mem_rootSpan_inf_iff σ (t.orbitReflection_mem a) (S := simpleOrbitRoots t a)
    (fun α hα => (simpleOrbitRoots_pos a α hα).1) g
  rw [orbitReflection_image_simpleOrbitRoots t a] at h
  exact h

theorem conj_simple_mem_Xg_iff :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * g *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹ ∈ Xg t K σ a ↔
      g ∈ Yg t K σ a := by
  have h := conj_mem_rootSpan_inf_iff σ (t.orbitReflection_mem a) (S := negOrbitRoots t a)
    (fun α hα => by
      obtain ⟨i, -, rfl⟩ := hα
      exact isRoot_neg_single _ i) g
  rw [orbitReflection_image_negOrbitRoots t a] at h
  exact h

theorem conj_simple_mem_Qg_iff :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * g *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹ ∈ Qg t K σ a ↔
      g ∈ Qg t K σ a := by
  have h := conj_mem_rootSpan_inf_iff σ (t.orbitReflection_mem a) (S := negComplementRoots t a)
    (fun α hα => hα.1.1) g
  rw [orbitReflection_image_negComplementRoots t a] at h
  exact h

end ConjSimple

theorem canonicalRep_mem_normalizer_graphFixedRootTorus {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) :
    canonicalRep (coxeterSystem t.tag) K w ∈
      Subgroup.normalizer (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) := by
  have hN := graphFixedRootTorus_subgroupOf_normal t K σ
  have hn := canonicalRep_mem_graphFixedRootMonomial t K σ hw
  have hHN : graphFixedRootTorus t K σ ≤ graphFixedRootMonomial t K σ :=
    inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial t K σ)
  have hconj : ∀ m ∈ graphFixedRootMonomial t K σ, ∀ h ∈ graphFixedRootTorus t K σ,
      m * h * m⁻¹ ∈ graphFixedRootTorus t K σ := fun m hm h hh =>
    Subgroup.mem_subgroupOf.1 (hN.conj_mem ⟨h, hHN hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨m, hm⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj _ hn h, fun hh => ?_⟩
  have := hconj _ (inv_mem hn) _ hh
  rwa [show (canonicalRep (coxeterSystem t.tag) K w)⁻¹ *
    (canonicalRep (coxeterSystem t.tag) K w * h *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹) *
    (canonicalRep (coxeterSystem t.tag) K w)⁻¹⁻¹ = h by group] at this

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
