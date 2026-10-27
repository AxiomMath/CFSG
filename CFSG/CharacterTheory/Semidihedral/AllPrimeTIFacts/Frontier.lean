module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts.Model
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsTransport
public import CFSG.CharacterTheory.Semidihedral.AllPrimeSetting

public section

namespace CFSG.Semidihedral.AllPrime.QDTI

noncomputable section

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.Semidihedral.MatrixTorus
open CFSG.Wreathed.OriginalAllPrime.TIFacts

variable {G : Type} [Group G]

theorem layerPreimage_normal (t : G) :
    ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).Normal := by
  have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
  exact Subgroup.Normal.comap inferInstance _

theorem frontier_model_exists [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht2 : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (s₀ : C t) (hs₀ : orderOf s₀ = 2) (hs₀t : s₀ ≠ tInC t) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F)) (a : Fˣ)
      (hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a) (Psi : OriginalH F a A hfix ≃* H t),
      Nat.card F = p ^ f ∧ Odd (Nat.card A) ∧ Nat.card A ∣ f ∧ ¬IsSquare a ∧
      Psi (originalZ F a A hfix) = nu t (tInC t) ∧ Psi (originalU F a A hfix) = nu t s₀ ∧
      (Psi.toMonoidHom.comp (originalSlInH F a A hfix)).range =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  have hfixedodd : Odd (Nat.card (MatrixCover.FixedField F A)) := by
    rw [data.fixed_field_card]
    exact hpodd.pow
  obtain ⟨b, -, hb⟩ :=
    ActualFourGroupCentralizer.odd_field_generator_nonsquare (MatrixCover.FixedField F A) hfixedodd
  obtain ⟨hbF, phi, hz, hlayer, -⟩ := data.every_coefficient b hb
  set e := ActualFourGroupCentralizer.fixedModelEquiv F A b with he
  set Psi0 := e.symm.trans phi with hPsi0
  have hz0 : Psi0 (originalZ F (MatrixCover.fixedUnit F A b) A
      (ActualFourGroupCentralizer.fixed_coefficient_action F A b)) = nu t (tInC t) := by
    change phi (e.symm _) = _
    rw [← ActualFourGroupCentralizer.fixedModelEquiv_z, MulEquiv.symm_apply_apply]
    exact hz
  have hsl : ∀ X : MatrixCoverData.SL F, e.symm (originalSlInH F (MatrixCover.fixedUnit F A b) A
      (ActualFourGroupCentralizer.fixed_coefficient_action F A b) X) =
        SemidirectProduct.inl (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A b) X) := by
    intro X
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    apply SemidirectProduct.ext
    · apply SemidirectProduct.ext
      · exact ((ActualFourGroupCentralizer.fixedModelEquiv_coordinates F A b _).1).symm
      · exact ((ActualFourGroupCentralizer.fixedModelEquiv_coordinates F A b _).2.1).symm
    · exact ((ActualFourGroupCentralizer.fixedModelEquiv_coordinates F A b _).2.2).symm
  have hlayer0 : (Psi0.toMonoidHom.comp (originalSlInH F (MatrixCover.fixedUnit F A b) A
      (ActualFourGroupCentralizer.fixed_coefficient_action F A b))).range =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
    rw [← hlayer]
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨X, by
        change phi _ = phi (e.symm _)
        rw [hsl]
        rfl⟩
    · rintro ⟨X, rfl⟩
      exact ⟨X, by
        change phi (e.symm _) = phi _
        rw [hsl]
        rfl⟩
  obtain ⟨c, Psi, hPsiZ, hPsiU, hpoint⟩ := ActualFourGroupAlignment.exists_original_aligned_equiv
    F (MatrixCover.fixedUnit F A b) A (ActualFourGroupCentralizer.fixed_coefficient_action F A b)
    n hn S fS hG t ht2 Psi0 hz0 s₀ hs₀ hs₀t
  refine ⟨F, hfield, hfinite, A, MatrixCover.fixedUnit F A b,
    ActualFourGroupCentralizer.fixed_coefficient_action F A b, Psi, data.field_card,
    data.field_group_odd, data.field_group_dvd, hbF, hPsiZ, hPsiU, ?_⟩
  have hLn := layerPreimage_normal t
  rw [← hlayer0]
  ext y
  constructor
  · rintro ⟨X, rfl⟩
    have h := hpoint (originalSlInH F (MatrixCover.fixedUnit F A b) A
      (ActualFourGroupCentralizer.fixed_coefficient_action F A b) X)
    change Psi _ ∈ _
    rw [h, hlayer0]
    exact hLn.conj_mem _ (hlayer0 ▸ ⟨X, rfl⟩) _
  · intro hy
    rw [hlayer0] at hy
    have hy' : (nu t c)⁻¹ * y * ((nu t c)⁻¹)⁻¹ ∈
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := hLn.conj_mem _ hy _
    rw [← hlayer0] at hy'
    obtain ⟨X, hX⟩ := hy'
    refine ⟨X, ?_⟩
    change Psi _ = _
    rw [hpoint]
    change nu t c * Psi0 _ * (nu t c)⁻¹ = y
    rw [show Psi0 (originalSlInH F (MatrixCover.fixedUnit F A b) A
      (ActualFourGroupCentralizer.fixed_coefficient_action F A b) X) = _ from hX]
    group

@[expose] def modelMap {t : G} {F : Type} [Field F] {A : Subgroup (F ≃+* F)} {a : Fˣ}
    {hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a} (Psi : OriginalH F a A hfix ≃* H t) :
    C t →* OriginalH F a A hfix :=
  Psi.symm.toMonoidHom.comp (nu t)

@[expose] def frontierModelMap {n : ℕ} (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G) (p f : ℕ) {F : Type} [Field F]
    {A : Subgroup (F ≃+* F)} {a : Fˣ} {hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a}
    (Psi : OriginalH F a A hfix ≃* H t) :
    (frontierSetting S fS t p f).N →* OriginalH F a A hfix :=
  modelMap Psi

theorem frontier_isModelMap [Finite G] {n : ℕ} (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G) (p f : ℕ)
    (hσ : (frontierSetting S fS t p f).IsValid) {F : Type} [Field F] {A : Subgroup (F ≃+* F)}
    {a : Fˣ} {hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a} (Psi : OriginalH F a A hfix ≃* H t)
    (hsC : (fS (s n) : G) ∈ C t)
    (hPsiU : Psi (originalU F a A hfix) = nu t ⟨(fS (s n) : G), hsC⟩)
    (hlayer : (Psi.toMonoidHom.comp (originalSlInH F a A hfix)).range =
      (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    IsModelMap (frontierSetting S fS t p f) (frontierModelMap S fS t p f Psi)
      (layerM F a A hfix) (originalU F a A hfix) := by
  have hs2 : orderOf (fS (s n) : G) = 2 := hσ.x₂_order
  refine
    { surjective := Psi.symm.surjective.comp (QuotientGroup.mk'_surjective (N t))
      ker_eq := ?_
      x₂_mem := hsC
      x₂_mul_self := by
        change (fS (s n) : G) * (fS (s n) : G) = 1
        have h := pow_orderOf_eq_one (fS (s n) : G)
        rw [hs2] at h
        rw [← pow_two]
        exact h
      map_x₂ := by
        change Psi.symm (nu t ⟨(fS (s n) : G), hsC⟩) = _
        rw [← hPsiU, MulEquiv.symm_apply_apply]
      L₀_le := hσ.L₀_le_N
      ON_le := hσ.ON_le_L₀
      map_L₀ := ?_ }
  · ext ⟨x, hx⟩
    change Psi.symm (nu t ⟨x, hx⟩) = 1 ↔ x ∈ (frontierSetting S fS t p f).ON
    rw [map_eq_one_iff _ Psi.symm.injective, ← MonoidHom.mem_ker, QuotientGroup.ker_mk',
      frontierSetting_ON]
    exact (Subgroup.mem_map_iff_mem (C t).subtype_injective (x := ⟨x, hx⟩)).symm
  · change (((localLayerPreimage t).map (C t).subtype).subgroupOf (C t)).map
      (Psi.symm.toMonoidHom.comp (nu t)) = _
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (C t).subtype_injective,
      ← Subgroup.map_map, localLayerPreimage,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (N t)), ← hlayer,
      MonoidHom.range_comp, Subgroup.map_map]
    ext m
    constructor
    · rintro ⟨y, ⟨X, rfl⟩, rfl⟩
      exact ⟨X, by simp⟩
    · rintro ⟨X, rfl⟩
      exact ⟨_, ⟨X, rfl⟩, by simp⟩

theorem frontier_package {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F)) (a : Fˣ)
      (hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a) (Psi : OriginalH F a A hfix ≃* H t),
      Nat.card F = p ^ f ∧ Odd (Nat.card A) ∧ Nat.card A ∣ f ∧ ¬IsSquare a ∧
      Psi (originalZ F a A hfix) = nu t (tInC t) ∧
      IsModelMap (frontierSetting S fS t p f) (frontierModelMap S fS t p f Psi)
        (layerM F a A hfix) (originalU F a A hfix) := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  have hs₀ : orderOf (⟨(fS (s n) : G), hsC⟩ : C t) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hs2
  have hs₀t : (⟨(fS (s n) : G), hsC⟩ : C t) ≠ tInC t := fun h =>
    hst (congrArg Subtype.val h)
  obtain ⟨F, hfield, hfinite, A, a, hfix, Psi, hcard, hA, hAf, ha, hPsiZ, hPsiU, hlayer⟩ :=
    frontier_model_exists n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel _ hs₀
      hs₀t
  exact ⟨F, hfield, hfinite, A, a, hfix, Psi, hcard, hA, hAf, ha, hPsiZ,
    frontier_isModelMap S fS t p f hσ Psi hsC hPsiU hlayer⟩

end

end CFSG.Semidihedral.AllPrime.QDTI
