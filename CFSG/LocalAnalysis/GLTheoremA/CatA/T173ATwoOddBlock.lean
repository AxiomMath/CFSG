module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp glueHom isCompl_fixSp_comSp
  glue glue_apply_left glue_apply_right exists_decomp)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private lemma glue_mem_left {U Uc : Submodule (ZMod 2) V} (hc : IsCompl U Uc)
    (g' : U ≃ₗ[ZMod 2] U) {w : V} (hw : w ∈ U) : glue hc g' w ∈ U := by
  have h := glue_apply_left hc g' ⟨w, hw⟩
  rw [h]
  exact (g' ⟨w, hw⟩).2

private lemma glue_mem_left_iff {U Uc : Submodule (ZMod 2) V} (hc : IsCompl U Uc)
    (g' : U ≃ₗ[ZMod 2] U) (w : V) : glue hc g' w ∈ U ↔ w ∈ U := by
  refine ⟨fun hw => ?_, glue_mem_left hc g'⟩
  have h1 : glue hc g'⁻¹ (glue hc g' w) ∈ U := glue_mem_left hc g'⁻¹ hw
  have h2 : glue hc g'⁻¹ (glue hc g' w) = w := by
    have hm : glueHom hc g'⁻¹ * glueHom hc g' = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    calc glue hc g'⁻¹ (glue hc g' w)
        = (glueHom hc g'⁻¹ * glueHom hc g') w := rfl
      _ = (1 : V ≃ₗ[ZMod 2] V) w := by rw [hm]
      _ = w := rfl
  rwa [h2] at h1

theorem lin_two_oddBlock_eq_range {g : V ≃ₗ[ZMod 2] V} (hg3 : g ^ 3 = 1) :
    linTwoOddBlock g = (glueHom (isCompl_fixSp_comSp hg3).symm).range := by
  let hc : IsCompl (comSp g) (fixSp g) := (isCompl_fixSp_comSp hg3).symm
  apply le_antisymm
  · intro h hh
    obtain ⟨hfix, hcom⟩ := hh
    let φ : (comSp g) →ₗ[ZMod 2] (comSp g) :=
      { toFun := fun u => ⟨h (u : V), (hcom (u : V)).1 u.2⟩
        map_add' := fun a b => Subtype.ext (by
          change h ((a + b : comSp g) : V) = h (a : V) + h (b : V)
          rw [Submodule.coe_add, map_add])
        map_smul' := fun c a => Subtype.ext (by
          change h ((c • a : comSp g) : V) = c • h (a : V)
          rw [Submodule.coe_smul, map_smul]) }
    have hφ : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      have h3 : h (a : V) = h (b : V) :=
        congrArg (fun z : comSp g => (z : V)) hab
      exact h.injective h3
    let g' : (comSp g) ≃ₗ[ZMod 2] (comSp g) := LinearEquiv.ofInjectiveEndo φ hφ
    refine MonoidHom.mem_range.2 ⟨g', ?_⟩
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, u', rfl⟩ := exists_decomp hc v
    have hu : h (u : V) = ((g' u : comSp g) : V) := by
      change h (u : V) = ((φ u : comSp g) : V)
      rfl
    have hu' : h (u' : V) = (u' : V) := hfix (u' : V) u'.2
    calc glue hc g' ((u : V) + (u' : V))
        = glue hc g' (u : V) + glue hc g' (u' : V) := map_add (glue hc g') _ _
      _ = ((g' u : comSp g) : V) + (u' : V) := by
            rw [glue_apply_left, glue_apply_right]
      _ = h (u : V) + h (u' : V) := by rw [← hu, hu']
      _ = h ((u : V) + (u' : V)) := (map_add h _ _).symm
  · rintro h ⟨g', rfl⟩
    change glue hc g' ∈ linTwoOddBlock g
    refine ⟨fun v hv => ?_, fun w => (glue_mem_left_iff hc g' w).symm⟩
    simpa using glue_apply_right hc g' ⟨v, hv⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
