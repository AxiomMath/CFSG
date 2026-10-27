module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Extend
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.DualData

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

section ExtendProps


section Entrywise

variable {R S : Type} [Field R] [Field S]

theorem units_map_entrywiseHom_baseChangeGL (ι : R →+* S) (σ : R →+* R) (σt : S →+* S)
    (h : ∀ x, σt (ι x) = ι (σ x)) (w : ModGL Tag.D4 R) :
    Units.map (entrywiseHom σt) (baseChangeGL ι w) =
      baseChangeGL ι (Units.map (entrywiseHom σ) w) := by
  have e : σt.comp ι = ι.comp σ := RingHom.ext h
  simp only [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, e]

theorem units_map_entrywiseHom_baseChangeGL_fix (ι : R →+* S) (F : S →+* S)
    (h : ∀ x, F (ι x) = ι x) (w : ModGL Tag.D4 R) :
    Units.map (entrywiseHom F) (baseChangeGL ι w) = baseChangeGL ι w := by
  have e : F.comp ι = ι := RingHom.ext h
  simp only [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, e]

theorem units_map_entrywiseHom_comm (F G : S →+* S) (h : ∀ y, F (G y) = G (F y))
    (w : ModGL Tag.D4 S) :
    Units.map (entrywiseHom F) (Units.map (entrywiseHom G) w) =
      Units.map (entrywiseHom G) (Units.map (entrywiseHom F) w) := by
  have e : F.comp G = G.comp F := RingHom.ext h
  simp only [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, e]

end Entrywise

section Props

variable {K K₃ : Type} [Field K] [Field K₃] (ι : K →+* K₃)

theorem coe_baseChangeAdj (u : adjointGroup Tag.D4 K) :
    ((baseChangeAdj ι u : adjointGroup Tag.D4 K₃) : ModGL Tag.D4 K₃) =
      baseChangeGL ι (u : ModGL Tag.D4 K) := rfl

theorem coe_ext_conjNormal (c : adjointGroup Tag.D4 K) (b : Fin Tag.D4.rank → Kˣ)
    (σt : K₃ ≃+* K₃) (w : adjointGroup Tag.D4 K₃) :
    ((MulAut.conj (baseChangeAdj ι c) *
        exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0) w :
          ModGL Tag.D4 K₃) =
      baseChangeGL ι ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b) *
        Units.map (entrywiseHom σt.toRingHom) (w : ModGL Tag.D4 K₃) *
          (baseChangeGL ι ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b))⁻¹ := by
  rw [coe_conjNormal]
  simp only [map_mul, baseChangeGL_rootDiagUnit, coe_baseChangeAdj]

theorem coe_ext_graphNormal (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (Fr : K₃ ≃+* K₃) (w : adjointGroup Tag.D4 K₃) :
    ((MulAut.conj (baseChangeAdj ι g) *
        (exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (a i)) Fr 0 *
          d4Graph K₃ 1)) w : ModGL Tag.D4 K₃) =
      baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K) *
        Units.map (entrywiseHom Fr.toRingHom) (w : ModGL Tag.D4 K₃) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K))⁻¹ := by
  rw [coe_graphNormal]
  simp only [map_mul, baseChangeGL_rootDiagUnit, coe_baseChangeAdj, graphType_baseChangeGL_d4P]

theorem ext_apply_baseChange (c : adjointGroup Tag.D4 K) (b : Fin Tag.D4.rank → Kˣ)
    (σ : K ≃+* K) (σt : K₃ ≃+* K₃) (hσt : ∀ x, σt (ι x) = ι (σ x)) (u : adjointGroup Tag.D4 K) :
    (MulAut.conj (baseChangeAdj ι c) *
        exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0)
        (baseChangeAdj ι u) =
      baseChangeAdj ι ((MulAut.conj c * exactNormalAut Tag.D4 K b σ 0) u) := by
  apply Subtype.ext
  rw [coe_ext_conjNormal, coe_baseChangeAdj, coe_baseChangeAdj, coe_conjNormal]
  simp only [map_mul, map_inv, baseChangeGL_rootDiagUnit,
    units_map_entrywiseHom_baseChangeGL ι σ.toRingHom σt.toRingHom hσt]

theorem ext_commute_entrywise (c : adjointGroup Tag.D4 K) (b : Fin Tag.D4.rank → Kˣ)
    (σt Fr : K₃ ≃+* K₃) (hFrι : ∀ x, Fr (ι x) = ι x) (hFrσt : ∀ y, Fr (σt y) = σt (Fr y)) :
    (MulAut.conj (baseChangeAdj ι c) *
        exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0) *
        entrywiseAdjointAut Tag.D4 Fr =
      entrywiseAdjointAut Tag.D4 Fr *
        (MulAut.conj (baseChangeAdj ι c) *
          exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0) := by
  obtain ⟨Y, hY⟩ : ∃ Y : ModGL Tag.D4 K₃,
      Y = baseChangeGL ι ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b) := ⟨_, rfl⟩
  have hFrY : Units.map (entrywiseHom Fr.toRingHom) Y = Y := by
    rw [hY]
    exact units_map_entrywiseHom_baseChangeGL_fix ι Fr.toRingHom hFrι _
  obtain ⟨Ξt, hΞt⟩ : ∃ Ξt : MulAut (adjointGroup Tag.D4 K₃), Ξt = MulAut.conj (baseChangeAdj ι c) *
      exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0 := ⟨_, rfl⟩
  rw [← hΞt]
  have hΞf : ∀ w : adjointGroup Tag.D4 K₃, ((Ξt w : adjointGroup Tag.D4 K₃) : ModGL Tag.D4 K₃) =
      Y * Units.map (entrywiseHom σt.toRingHom) (w : ModGL Tag.D4 K₃) * Y⁻¹ := by
    intro w
    rw [hΞt, hY]
    exact coe_ext_conjNormal ι c b σt w
  refine MulEquiv.ext fun w => Subtype.ext ?_
  change ((Ξt (entrywiseAdjointAut Tag.D4 Fr w) : adjointGroup Tag.D4 K₃) : ModGL Tag.D4 K₃) =
    ((entrywiseAdjointAut Tag.D4 Fr (Ξt w) : adjointGroup Tag.D4 K₃) : ModGL Tag.D4 K₃)
  simp only [hΞf, coe_entrywiseAdjointAut, map_mul, map_inv, hFrY]
  rw [units_map_entrywiseHom_comm Fr.toRingHom σt.toRingHom hFrσt]

theorem ext_commute_graph (c g : adjointGroup Tag.D4 K) (a b : Fin Tag.D4.rank → Kˣ)
    (σ : K ≃+* K) (σt Fr : K₃ ≃+* K₃) (hσt : ∀ x, σt (ι x) = ι (σ x))
    (hFrι : ∀ x, Fr (ι x) = ι x) (hFrσt : ∀ y, Fr (σt y) = σt (Fr y))
    (hstar : ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b) *
        Units.map (entrywiseHom σ.toRingHom)
          ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K) *
        ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b)) :
    (MulAut.conj (baseChangeAdj ι c) *
        exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0) *
        (MulAut.conj (baseChangeAdj ι g) *
          (exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (a i)) Fr 0 *
            d4Graph K₃ 1)) =
      (MulAut.conj (baseChangeAdj ι g) *
          (exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (a i)) Fr 0 *
            d4Graph K₃ 1)) *
        (MulAut.conj (baseChangeAdj ι c) *
          exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0) := by
  obtain ⟨Y, hY⟩ : ∃ Y : ModGL Tag.D4 K₃,
      Y = baseChangeGL ι ((c : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 b) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ModGL Tag.D4 K₃,
      X = baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K) := ⟨_, rfl⟩
  have hFrY : Units.map (entrywiseHom Fr.toRingHom) Y = Y := by
    rw [hY]
    exact units_map_entrywiseHom_baseChangeGL_fix ι Fr.toRingHom hFrι _
  have hstar3 : Y * Units.map (entrywiseHom σt.toRingHom) X = X * Y := by
    rw [hY, hX, units_map_entrywiseHom_baseChangeGL ι σ.toRingHom σt.toRingHom hσt, ← map_mul,
      ← map_mul, hstar]
  obtain ⟨Ξt, hΞt⟩ : ∃ Ξt : MulAut (adjointGroup Tag.D4 K₃), Ξt = MulAut.conj (baseChangeAdj ι c) *
      exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : MulAut (adjointGroup Tag.D4 K₃), β = MulAut.conj (baseChangeAdj ι g) *
      (exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (a i)) Fr 0 *
        d4Graph K₃ 1) := ⟨_, rfl⟩
  rw [← hΞt, ← hβ]
  have hΞf : ∀ w : adjointGroup Tag.D4 K₃, ((Ξt w : adjointGroup Tag.D4 K₃) : ModGL Tag.D4 K₃) =
      Y * Units.map (entrywiseHom σt.toRingHom) (w : ModGL Tag.D4 K₃) * Y⁻¹ := by
    intro w
    rw [hΞt, hY]
    exact coe_ext_conjNormal ι c b σt w
  have hβf : ∀ w : adjointGroup Tag.D4 K₃, ((β w : adjointGroup Tag.D4 K₃) : ModGL Tag.D4 K₃) =
      X * Units.map (entrywiseHom Fr.toRingHom) (w : ModGL Tag.D4 K₃) * X⁻¹ := by
    intro w
    rw [hβ, hX]
    exact coe_ext_graphNormal ι g a Fr w
  refine MulEquiv.ext fun w => Subtype.ext ?_
  change ((Ξt (β w) : adjointGroup Tag.D4 K₃) : ModGL Tag.D4 K₃) =
    ((β (Ξt w) : adjointGroup Tag.D4 K₃) : ModGL Tag.D4 K₃)
  simp only [hΞf, hβf, map_mul, map_inv, hFrY]
  rw [units_map_entrywiseHom_comm Fr.toRingHom σt.toRingHom hFrσt]
  calc Y * (Units.map (entrywiseHom σt.toRingHom) X *
        Units.map (entrywiseHom σt.toRingHom) (Units.map (entrywiseHom Fr.toRingHom)
          (w : ModGL Tag.D4 K₃)) *
        (Units.map (entrywiseHom σt.toRingHom) X)⁻¹) * Y⁻¹
      = (Y * Units.map (entrywiseHom σt.toRingHom) X) *
          Units.map (entrywiseHom σt.toRingHom) (Units.map (entrywiseHom Fr.toRingHom)
            (w : ModGL Tag.D4 K₃)) *
          (Y * Units.map (entrywiseHom σt.toRingHom) X)⁻¹ := by group
    _ = (X * Y) * Units.map (entrywiseHom σt.toRingHom) (Units.map (entrywiseHom Fr.toRingHom)
            (w : ModGL Tag.D4 K₃)) * (X * Y)⁻¹ := by rw [hstar3]
    _ = _ := by group

end Props

end ExtendProps

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
