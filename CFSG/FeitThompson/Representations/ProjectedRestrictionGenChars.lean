module

public import CFSG.FeitThompson.Representations.DadeSubsetSemidirectProduct
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Pullback

variable {X Y : Type*} [Group X] [Group Y]

theorem Representation.character_comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Y V) (φ : X →* Y) :
    Representation.character (ρ.comp φ) = ρ.character ∘ φ := rfl

theorem comp_mem_span_Irr [Finite X] (φ : X →* Y) {f : Y → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr Y)) : f ∘ φ ∈ Submodule.span ℤ (Irr X) := by
  have h : Submodule.span ℤ (Irr Y) ≤
      (Submodule.span ℤ (Irr X)).comap (LinearMap.funLeft ℤ ℂ (φ : X → Y)) := by
    rw [Submodule.span_le]
    intro χ hχ
    obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
    obtain ⟨m, hm⟩ := exists_character_eq_sum_nsmul (V.ρ.comp φ)
    have hval : (LinearMap.funLeft ℤ ℂ (φ : X → Y)) (FDRep.character V)
        = ∑ χ : irrFinset X, (m χ : ℂ) • (χ : X → ℂ) := by
      rw [← hm, Representation.character_comp V.ρ φ]; rfl
    simp only [SetLike.mem_coe, Submodule.mem_comap, hval]
    refine Submodule.sum_mem _ fun χ _ => ?_
    rw [Nat.cast_smul_eq_nsmul ℂ]
    exact nsmul_mem (Submodule.subset_span (mem_irrFinset.1 χ.2)) _
  exact h hf

theorem comp_mem_virtualChars [Finite X] (φ : X →* Y) {f : Y → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr Y)) : f ∘ φ ∈ virtualChars X :=
  span_Irr_le_virtualChars (comp_mem_span_Irr φ hf)

end Pullback

variable {G : Type*} [Group G] {L : Subgroup G} {A B : Set G} {H : G → Subgroup G}

noncomputable def IsDadeData.dadeProjToL [Finite G] (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) : dadeSubsetGroup H L B →* L :=
  (Subgroup.inclusion (dadeStab_le_left (L := L) (B := B))).comp (hD.dadeProj hBA hB)

theorem IsDadeData.dadeProjToL_apply [Finite G] (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) (x : dadeSubsetGroup H L B) :
    hD.dadeProjToL hBA hB x = Subgroup.inclusion dadeStab_le_left (hD.dadeProj hBA hB x) := (rfl)

theorem IsDadeData.dadeProjToL_apply_mul [Finite G] (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) {h u : G} (hh : h ∈ dadeInter H B) (hu : u ∈ dadeStab L B) :
    hD.dadeProjToL hBA hB ⟨h * u, (hD.mem_dadeSubsetGroup_iff hBA).2 ⟨h, hh, u, hu, rfl⟩⟩
      = ⟨u, dadeStab_le_left hu⟩ := by
  rw [hD.dadeProjToL_apply, hD.dadeProj_apply_mul hBA hB hh hu]; rfl

theorem IsDadeData.dadePullback_eq_comp [Finite G] {M : Type*} (hD : IsDadeData L A H)
    (hBA : B ⊆ A) (hB : B.Nonempty) (f : ↥L → M) :
    dadePullback (hD.dadeProj hBA hB) f = f ∘ hD.dadeProjToL hBA hB := by
  funext x
  rw [dadePullback_apply, Function.comp_apply, hD.dadeProjToL_apply]

theorem IsDadeData.dadePullback_mem_span_Irr [Finite G] (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) {f : ↥L → ℂ} (hf : f ∈ Submodule.span ℤ (Irr ↥L)) :
    dadePullback (hD.dadeProj hBA hB) f ∈ Submodule.span ℤ (Irr ↥(dadeSubsetGroup H L B)) := by
  rw [hD.dadePullback_eq_comp hBA hB f]
  exact comp_mem_span_Irr _ hf

theorem IsDadeData.dadePullback_mem_virtualChars [Finite G] (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) {f : ↥L → ℂ} (hf : f ∈ Submodule.span ℤ (Irr ↥L)) :
    dadePullback (hD.dadeProj hBA hB) f ∈ virtualChars ↥(dadeSubsetGroup H L B) :=
  span_Irr_le_virtualChars (hD.dadePullback_mem_span_Irr hBA hB hf)

end CFSG.FeitThompson
