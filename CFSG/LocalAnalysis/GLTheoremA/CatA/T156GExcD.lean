module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapGlue
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownOmegaPlus
public import CFSG.LieType.Universal.SpinOmega.Center

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Assembly CFSG.StandardType
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.RankThree.PartOne.KCSpComm (card_descentField)

section Fix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem exists_fixGeom_omegaPlus (hm : 4 ≤ m) {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ n)
    (hS : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
    (hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)), a * b ≠ b * a)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m))))
    (hord : orderOf f = p) :
    LargeEvenRecipeOmegaPlus m (2 ^ (n / p)) fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))) f I₀
          θ₀ := by
  have hm1 : 1 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  obtain ⟨σ, hσf⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_field hm1 hf
  have hinj : Function.Injective (AutOm.fieldAutP (K := K) m) :=
    (injective_iff_map_eq_one _).2 fun τ h => AutOm.eq_one_of_fieldAutP_eq_one hm3 h
  have hσ : orderOf σ = p := by
    rw [← orderOf_injective (AutOm.fieldAutP m) hinj σ, ← hσf, MulEquiv.orderOf_eq]
    exact hord
  set k := descentField σ with hkdef
  have hσk : ∀ x, x ∈ k ↔ σ x = x := fun x => mem_descentField
  obtain ⟨-, hcard⟩ := card_descentField Nat.prime_two hn hK hσ
  have hS₀ : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus hm3
  have hna₀ : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)), a * b ≠ b * a := by
    haveI := hS₀
    haveI : Group.IsPerfect ↥(LargeEvenOmega (LargeEvenQPlus k m)) :=
      CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus hm3
    haveI : Group.IsPerfect (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m))) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    exact Y10GField.exists_mul_ne_of_isPerfect _
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) = ⊥ := by
    obtain ⟨x, y, hxy⟩ := hna
    exact TableBOrth.center_eq_bot_of_simple hxy
  have hrange : (FieldFixOmegaPlus.subfieldInj k hm1).range = ggFixSub f := by
    ext r
    rw [FieldFixOmegaPlus.mem_range_subfieldInj_iff k hp hp2 hσ hσk hm3 hσf r, mem_ggFixSub]
  let e : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)) ≃* ↥(ggFixSub f) :=
    (MonoidHom.ofInjective (FieldFixOmegaPlus.subfieldInj_injective k hm1)).trans
      (MulEquiv.subgroupCongr hrange)
  haveI := hS₀
  exact ⟨k, inferInstance, inferInstance, hcard, hS₀, hna₀,
    ggFixGeom_of_inn hna₀ hZ (fun _ h => h) (fun _ h => h) e⟩

end Fix

variable {p : ℕ}

theorem cAll_geomBody_D_all (hp : p.Prime) (hp2 : p ≠ 2) {l n : ℕ} (hl : 4 ≤ l) (hn : 1 ≤ n) :
    MI.CAll ⟨.D, l, n⟩ (GeomBody p ⟨.D, l, n⟩) := by
  have hlab : LargeEvenInLambda2 ⟨.D, l, n⟩ := ⟨hn, show 3 ≤ l by omega⟩
  refine (MI.canonAll_iff_legacyAll hlab (by simp [MI.DerivedLab]) _).2 ?_
  refine largeEvenLabelAll_omegaPlus (lab := ⟨.D, l, n⟩) rfl hl fun K _ _ _ hK => ?_
  refine geomBody_of_field (by simp) fun hS hna f hf hord => ?_
  have h := exists_fixGeom_omegaPlus hl hn hp hp2 hK hS hna hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hlab₀ : LargeEvenInLambda2 ⟨.D, l, n / p⟩ :=
    ⟨one_le_of_card_field hK₀, show 3 ≤ l by omega⟩
  refine fixAlt_of_raw hlab₀ ?_
  have h3 : l ≠ 3 := by omega
  dsimp only [CFSG.Assembly.LargeEvenRawDatum]
  simp only [h3, ↓reduceIte]
  exact exists_fixGeom_omegaPlus hl hn hp hp2 hK hS hna hf hord

end CFSG.LocalAnalysis.GLTheoremA.T156

end
