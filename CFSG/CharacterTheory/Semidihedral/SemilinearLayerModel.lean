module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateSemilinear

public section

namespace CFSG.Semidihedral.SemilinearLayerModel

noncomputable section

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u v

theorem generalizedFitting_characteristic (Γ : Type u) [Group Γ] :
    (CFSG.generalizedFitting Γ).Characteristic := by
  rw [CFSG.generalizedFitting_eq_componentClassification]
  exact CFSG.ComponentClassification.GeneralizedFitting.characteristic Γ

theorem generalizedFitting_normal (Γ : Type u) [Group Γ] :
    (CFSG.generalizedFitting Γ).Normal := by
  let := generalizedFitting_characteristic Γ
  infer_instance

theorem generalizedFitting_centralizer_eq_bot (Γ : Type u) [Group Γ] [Finite Γ]
    [IsSimpleGroup (CFSG.generalizedFitting Γ)]
    (hnonab : ∃ a b : CFSG.generalizedFitting Γ, a * b ≠ b * a) :
    Subgroup.centralizer (CFSG.generalizedFitting Γ : Set Γ) = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have hmem := CFSG.centralizer_generalizedFitting_le Γ hg
  have hcenter : (⟨g, hmem⟩ : CFSG.generalizedFitting Γ) ∈
      Subgroup.center (CFSG.generalizedFitting Γ) := by
    apply Subgroup.mem_center_iff.mpr
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg l.val l.property)
  rw [CFSG.ComponentClassification.Helpers.center_eq_bot _ hnonab] at hcenter
  exact congrArg Subtype.val hcenter

@[expose] def generalizedFittingConjugation (Γ : Type u) [Group Γ] :
    Γ →* MulAut (CFSG.generalizedFitting Γ) := by
  let := generalizedFitting_normal Γ
  exact MulAut.conjNormal

theorem generalizedFittingConjugation_ker (Γ : Type u) [Group Γ] :
    (generalizedFittingConjugation Γ).ker =
      Subgroup.centralizer (CFSG.generalizedFitting Γ : Set Γ) := by
  let := generalizedFitting_normal Γ
  ext g
  constructor
  · intro hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro l hl
    have heq := congrArg (fun α : MulAut (CFSG.generalizedFitting Γ) =>
      (α (⟨l, hl⟩ : CFSG.generalizedFitting Γ)).val) hg
    change g * l * g⁻¹ = l at heq
    have hcomm := congrArg (fun x : Γ => x * g) heq
    have hgl : g * l = l * g := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcomm
    exact hgl.symm
  · intro hg
    change generalizedFittingConjugation Γ g = 1
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    change g * l.val * g⁻¹ = l.val
    rw [← Subgroup.mem_centralizer_iff.mp hg l.val l.property]
    group

theorem generalizedFittingConjugation_injective (Γ : Type u) [Group Γ] [Finite Γ]
    [IsSimpleGroup (CFSG.generalizedFitting Γ)]
    (hnonab : ∃ a b : CFSG.generalizedFitting Γ, a * b ≠ b * a) :
    Function.Injective (generalizedFittingConjugation Γ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [generalizedFittingConjugation_ker, generalizedFitting_centralizer_eq_bot Γ hnonab]

@[expose] def coordinateSocleInclusion (K : Type v) [Field K] :
    coordinateG K →* coordinateE K :=
  Subgroup.inclusion ((coordinateG_le_D K).trans (coordinateD_le_E K))

@[expose] def coordinateEquivAut (K : Type v) [Field K] [Finite K] :
    coordinateE K ≃* MulAut (coordinateG K) :=
  ((semilinearEquivCoordinateE K).symm.trans (semilinearEquivAut K)).trans
    (MulAut.congr (pslEquivCoordinateG K))

theorem semilinearEquivAut_symm_conj (K : Type v) [Field K] [Finite K]
    (x : PSL2 K) :
    (semilinearEquivAut K).symm (MulAut.conj x) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
  apply (semilinearEquivAut K).injective
  rw [(semilinearEquivAut K).apply_symm_apply]
  change MulAut.conj x = semilinearAction K
    (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x))
  rw [semilinearAction_inl, pglAction_toPGL]

theorem coordinate_inner_value (K : Type v) [Field K] [Finite K]
    (x : PSL2 K) :
    ((semilinearEquivCoordinateE K ((semilinearEquivAut K).symm (MulAut.conj x))).val) =
      (pslEquivCoordinateG K x).val := by
  rw [semilinearEquivAut_symm_conj, semilinearEquivCoordinateE_coe,
    coordinateSemilinearAction_inl, coordinatePGLAction_toPGL]
  rfl

theorem congr_conj {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (x : A) :
    (MulAut.congr e) (MulAut.conj x) = MulAut.conj (e x) := by
  apply MulEquiv.ext
  intro y
  change e (x * e.symm y * x⁻¹) = e x * y * (e x)⁻¹
  simp only [map_mul, map_inv, e.apply_symm_apply]

theorem coordinateEquivAut_symm_conj (K : Type v) [Field K] [Finite K]
    (x : coordinateG K) :
    (coordinateEquivAut K).symm (MulAut.conj x) = coordinateSocleInclusion K x := by
  have htransport : (MulAut.congr (pslEquivCoordinateG K)).symm (MulAut.conj x) =
      MulAut.conj ((pslEquivCoordinateG K).symm x) := by
    apply (MulAut.congr (pslEquivCoordinateG K)).injective
    rw [(MulAut.congr (pslEquivCoordinateG K)).apply_symm_apply,
      congr_conj, (pslEquivCoordinateG K).apply_symm_apply]
  apply Subtype.ext
  change (semilinearEquivCoordinateE K ((semilinearEquivAut K).symm
    ((MulAut.congr (pslEquivCoordinateG K)).symm (MulAut.conj x)))).val = x.val
  rw [htransport, coordinate_inner_value, (pslEquivCoordinateG K).apply_symm_apply]

theorem coordinateEquivAut_socle (K : Type v) [Field K] [Finite K]
    (x : coordinateG K) :
    coordinateEquivAut K (coordinateSocleInclusion K x) = MulAut.conj x := by
  rw [← coordinateEquivAut_symm_conj, (coordinateEquivAut K).apply_symm_apply]

theorem generalizedFitting_semilinear_model_of_equiv {Γ : Type u} [Group Γ] [Finite Γ]
    [IsSimpleGroup (CFSG.generalizedFitting Γ)]
    (hnonab : ∃ a b : CFSG.generalizedFitting Γ, a * b ≠ b * a)
    {K : Type v} [Field K] [Finite K]
    (θ : CFSG.generalizedFitting Γ ≃* coordinateG K) :
    ∃ ρ : Γ →* coordinateE K, Function.Injective ρ ∧
      (∀ l : CFSG.generalizedFitting Γ, (ρ l.val).val = (θ l).val) ∧
      (CFSG.generalizedFitting Γ).map ρ = (coordinateG K).subgroupOf (coordinateE K) ∧
      (coordinateG K).subgroupOf (coordinateE K) ≤ ρ.range ∧
      ((coordinateG K).subgroupOf (coordinateE K)).relIndex ρ.range =
        (CFSG.generalizedFitting Γ).index := by
  let L := CFSG.generalizedFitting Γ
  let : L.Normal := generalizedFitting_normal Γ
  let a : Γ →* MulAut L := generalizedFittingConjugation Γ
  let c := coordinateEquivAut K
  let ρ : Γ →* coordinateE K :=
    c.symm.toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp a)
  have hρ : Function.Injective ρ := c.symm.injective.comp
    ((MulAut.congr θ).injective.comp (generalizedFittingConjugation_injective Γ hnonab))
  have hextends : ∀ l : L, (ρ l.val).val = (θ l).val := by
    intro l
    have hinner : a l.val = MulAut.conj l := MulAut.conjNormal_val
    change (c.symm ((MulAut.congr θ) (a l.val))).val = (θ l).val
    rw [hinner, congr_conj]
    exact congrArg Subtype.val (coordinateEquivAut_symm_conj K (θ l))
  have hmap : L.map ρ = (coordinateG K).subgroupOf (coordinateE K) := by
    apply le_antisymm
    · rintro g ⟨l, hl, rfl⟩
      change (ρ l).val ∈ coordinateG K
      rw [hextends (⟨l, hl⟩ : L)]
      exact (θ (⟨l, hl⟩ : L)).property
    · intro g hg
      let x : coordinateG K := ⟨g.val, hg⟩
      let l := θ.symm x
      refine ⟨l.val, l.property, ?_⟩
      apply Subtype.ext
      rw [hextends l]
      exact congrArg Subtype.val (θ.apply_symm_apply x)
  have hindex : ((coordinateG K).subgroupOf (coordinateE K)).relIndex ρ.range =
      L.index := by
    rw [← hmap, ← Subgroup.map_top ρ,
      Subgroup.relIndex_map_map_of_injective L ⊤ hρ, Subgroup.relIndex_top_right]
  exact ⟨ρ, hρ, hextends, hmap, hmap ▸ Subgroup.map_le_range ρ L, hindex⟩

theorem generalizedFitting_semilinear_model {Γ : Type} [Group Γ] [Finite Γ]
    [IsSimpleGroup (CFSG.generalizedFitting Γ)]
    (hnonab : ∃ a b : CFSG.generalizedFitting Γ, a * b ≠ b * a)
    {p f : ℕ}
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting Γ) .PSL 2 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      ∃ (θ : CFSG.generalizedFitting Γ ≃* coordinateG K) (ρ : Γ →* coordinateE K),
        Function.Injective ρ ∧
        (∀ l : CFSG.generalizedFitting Γ, (ρ l.val).val = (θ l).val) ∧
        (CFSG.generalizedFitting Γ).map ρ = (coordinateG K).subgroupOf (coordinateE K) ∧
        (coordinateG K).subgroupOf (coordinateE K) ≤ ρ.range ∧
        ((coordinateG K).subgroupOf (coordinateE K)).relIndex ρ.range =
          (CFSG.generalizedFitting Γ).index := by
  obtain ⟨K, hfield, hfinite, hcard, ⟨e⟩⟩ := hmodel.2
  let : Field K := hfield
  let : Finite K := hfinite
  let θ : CFSG.generalizedFitting Γ ≃* coordinateG K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      2 K).symm).trans (pslEquivCoordinateG K)
  obtain ⟨ρ, hρ, hextends, hmap, hcontains, hindex⟩ :=
    generalizedFitting_semilinear_model_of_equiv hnonab θ
  exact ⟨K, hfield, hfinite, hcard, θ, ρ, hρ, hextends, hmap, hcontains, hindex⟩

end

end CFSG.Semidihedral.SemilinearLayerModel
