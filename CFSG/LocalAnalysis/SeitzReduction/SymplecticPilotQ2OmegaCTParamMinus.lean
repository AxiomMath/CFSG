module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesLevi

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus
  commutator_coordinateQuadMinus)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL mat_leviEmbedSL)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore coordEmbedGL coe_coordEmbedGL
  coordEmbedMat_mulVec_of_not_mem coordEmbedMat_mulVec_comp coordEmbedMat_apply_image)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Res

variable (k : Type) [Field k] [Finite k] [CharP k 2] {r : ℕ} {b c : k} (hr : 3 ≤ r)
  (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)

theorem exists_mem_fixedSubgroup_kOmMFixRes_ne_one :
    ∃ A : fixedSubgroup (kOmMBetaC k r b c), kOmMFixRes k hr hirr A ≠ 1 := by
  classical
  set i0 : Fin r := ⟨0, by omega⟩ with hi0
  set i1 : Fin r := ⟨1, by omega⟩ with hi1
  set i2 : Fin r := ⟨2, by omega⟩ with hi2
  set B : Finset (Fin r) := {i0, i1, i2} with hB
  have hBc : 3 ≤ B.card := by
    rw [hB, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hi1, hi2, Fin.ext_iff]
    · simp [hi0, hi1, hi2, Fin.ext_iff]
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  set C : SL(r, k) := SpecialLinearGroup.transvection h01 1 with hCdef
  have hC : C ∈ blockSpecialLinear (K := k) B :=
    LinearPilot.transvection_mem_blockSpecialLinear h01 (by simp [hB]) (by simp [hB]) 1
  set y : StatedSp r k := leviEmbedSL k r C with hydef
  have hyS : y ∈ siegelBlock k B := ⟨C, hC, rfl⟩
  have hyO : (y : GL (Fin r ⊕ Fin r) k) ∈ StatedOmega (StatedQuadPlus r k) :=
    siegelBlockGL_le_statedOmega_of_three_le hBc ⟨y, hyS, rfl⟩
  set X : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k :=
    coordEmbedGL (kOmMEmb r) kOmMEmb_injective (y : GL (Fin r ⊕ Fin r) k) with hXdef
  have hXO : X ∈ StatedOmega (StatedQuadMinus (r + 1) k b c) :=
    (kOmM_isCoordSplit_hyp (r := r) b c).map_statedOmega_le kOmMEmb_injective ⟨_, hyO, rfl⟩
  set A : StatedOmega (StatedQuadMinus (r + 1) k b c) := ⟨X, hXO⟩ with hAdef
  have hfix : A ∈ fixedSubgroup (kOmMBetaC k r b c) := by
    rw [mem_fixedSubgroup_kOmMBetaC_iff k hr hirr]
    change F4Pilot.coordEmbedMat (kOmMEmb r) ((y : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) *ᵥ kOmMVec k r = kOmMVec k r
    funext a
    by_cases ha : a ∈ Set.range (kOmMEmb r)
    · obtain ⟨z, rfl⟩ := ha
      have h1 := congrFun (coordEmbedMat_mulVec_comp kOmMEmb_injective ((y : GL (Fin r ⊕ Fin r)
        k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (kOmMVec k r)) z
      simp only [Function.comp_apply] at h1
      rw [h1, kOmMVec_kOmMEmb]
      have h0 : (kOmMVec k r ∘ kOmMEmb r) = 0 := funext fun w => kOmMVec_kOmMEmb k w
      rw [h0, Matrix.mulVec_zero, Pi.zero_apply]
    · exact coordEmbedMat_mulVec_of_not_mem _ _ ha
  refine ⟨⟨A, hfix⟩, fun h1 => ?_⟩
  have h2 := congrArg (fun z : StatedSp r k => mat r k z (Sum.inl i0) (Sum.inl i1)) h1
  simp only [map_one] at h2
  rw [mat_apply, coe_kOmMFixRes] at h2
  simp only [submatrix_apply] at h2
  change F4Pilot.coordEmbedMat (kOmMEmb r) ((y : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (kOmMEmb r (Sum.inl i0))
        (kOmMEmb r (Sum.inl i1)) = _ at h2
  rw [coordEmbedMat_apply_image kOmMEmb_injective, ← mat_apply, hydef, mat_leviEmbedSL,
    fromBlocks_apply₁₁, hCdef, SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.one_apply_ne h01, single_apply_same, zero_add,
    Matrix.one_apply_ne (by simp [Fin.ext_iff])] at h2
  exact one_ne_zero h2

theorem kOmMFixRes_injective_two (hK : Nat.card k = 2) :
    Function.Injective (kOmMFixRes k hr hirr) := by
  obtain ⟨e⟩ := nonempty_fixedSubgroup_kOmMBetaC_mulEquiv k hr hirr (f := 1) le_rfl
    (by rw [hK, pow_one])
  have : IsSimpleGroup (StatedSp r k) := isSimpleGroup_statedSp_two hK hr
  have : IsSimpleGroup (fixedSubgroup (kOmMBetaC k r b c)) := e.isSimpleGroup
  rcases (kOmMFixRes k hr hirr).normal_ker.eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    obtain ⟨A, hA⟩ := exists_mem_fixedSubgroup_kOmMFixRes_ne_one k hr hirr
    have hker : A ∈ (kOmMFixRes k hr hirr).ker := by
      rw [h]
      exact Subgroup.mem_top _
    exact hA hker

theorem kOmMFixRes_bijective_two (hK : Nat.card k = 2) :
    Function.Bijective (kOmMFixRes k hr hirr) := by
  obtain ⟨e⟩ := nonempty_fixedSubgroup_kOmMBetaC_mulEquiv k hr hirr (f := 1) le_rfl
    (by rw [hK, pow_one])
  exact (kOmMFixRes_injective_two k hr hirr hK).bijective_of_nat_card_le
    (Nat.card_congr e.toEquiv).ge

variable {k}

@[expose] noncomputable def q2OmMIota (hK : Nat.card k = 2) :
    StatedSp r k →* StatedOmega (StatedQuadMinus (r + 1) k b c) :=
  (fixedSubgroup (kOmMBetaC k r b c)).subtype.comp
    (MulEquiv.ofBijective (kOmMFixRes k hr hirr)
      (kOmMFixRes_bijective_two k hr hirr hK)).symm.toMonoidHom

theorem q2OmMIota_injective (hK : Nat.card k = 2) : Function.Injective (q2OmMIota hr hirr hK) :=
  (fixedSubgroup _).subtype_injective.comp (MulEquiv.injective _)

theorem range_q2OmMIota (hK : Nat.card k = 2) :
    (q2OmMIota hr hirr hK).range = fixedSubgroup (kOmMBetaC k r b c) := by
  rw [q2OmMIota, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map, range_subtype]

theorem kOmMFixRes_q2OmMIota (hK : Nat.card k = 2) (g : StatedSp r k) :
    ∃ y : fixedSubgroup (kOmMBetaC k r b c), (y : StatedOmega (StatedQuadMinus (r + 1) k b c)) =
      q2OmMIota hr hirr hK g ∧ kOmMFixRes k hr hirr y = g :=
  ⟨_, rfl, MulEquiv.apply_symm_apply (MulEquiv.ofBijective (kOmMFixRes k hr hirr)
    (kOmMFixRes_bijective_two k hr hirr hK)) g⟩

end Res

section Param


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_q2OmMParam (hset : SeitzSetting G L) {r : ℕ} (hK : Nat.card K = 2) (hr3 : 3 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (r + 1)) (h : NsKindSp e t k .omegaMinus) :
    ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (Φ : StatedOmega (StatedQuadMinus (r + 1) K b c) ≃*
        centralizerPerfectCore (modelToG e (nsTorusSp K k))),
      (∀ g, t * ((Φ g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) * t⁻¹ =
        ((Φ (kOmMBetaC K r b c g) : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G)) ∧
      ∀ x : StatedSp r K,
        ((Φ (q2OmMIota hr3 hirr hK x) : centralizerPerfectCore (modelToG e (nsTorusSp K k))) :
          G) = ((e.symm (complSpEquiv k x) : L) : G) := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  set E := centralizerPerfectCore (modelToG e (nsTorusSp K k)) with hEdef
  have hN : t ∈ normalizer (E : Set G) :=
    UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _
  obtain ⟨hty, hout, hfix⟩ := nsCore_omega_facts_two (m := r) hset hK hr3 e htC ht k rfl rfl
    (Or.inr rfl) h hN
  have hty' : LieModel E .POmegaMinus (r + 1) 2 1 := hty
  obtain ⟨b, c, hirr, ⟨ε₀⟩⟩ := kOmM_nonempty_mulEquiv_of_lieModel (by omega) hty' K hKc
  set π := F4Pilot.omegaProjEquiv (minusIndexEquiv (r + 1) (by omega)) (quadMinus (r + 1) K b c)
    (coe_quadMinus (r + 1) K b c) (kOmM_matrixDerivedScalars_eq_bot K r b c) with hπ
  have hreg := regular_coordinateQuadMinus (r + 1) K b c (by omega) hirr
  have hE := commutator_coordinateQuadMinus (r + 1) K b c (by omega) hirr
  have hθθ : E.normalizerMonoidHom ⟨t, hN⟩ * E.normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (E : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hout hfix (le_refl 1) hKc
    (by omega : 4 ≤ r + 1) hreg.1 hreg.2 hE (kOmM_hconj K (by omega) le_rfl hKc hirr)
    (kOmM_reindexQuadraticForm_vec K r) (ε₀.trans π)
  set Φ₀ : StatedOmega (StatedQuadMinus (r + 1) K b c) ≃* E := π.trans ψ with hΦ₀
  have hΦ₀t : ∀ g, t * ((Φ₀ g : E) : G) * t⁻¹ = ((Φ₀ (kOmMBetaC K r b c g) : E) : G) := by
    intro g
    have h12 : (E.normalizerMonoidHom ⟨t, hN⟩) (ψ (π g)) = ψ (π (kOmMBetaC K r b c g)) :=
      (hψ (π g)).trans (congrArg ψ (F4Pilot.omegaProjEquiv_omegaSymmetryAut _ _ _ _ _ g).symm)
    change t * ((ψ (π g) : E) : G) * t⁻¹ = ((ψ (π (kOmMBetaC K r b c g)) : E) : G)
    rw [← h12, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hfixmap := map_fixedSubgroup_eq_of_comm_two (m := r) hset hK hr3 e htC ht k (Or.inr rfl) h
    Φ₀ (kOmMBetaC K r b c) hΦ₀t
  set ι := q2OmMIota (k := K) hr3 hirr hK with hιdef
  set κ : StatedSp r K →* G := E.subtype.comp (Φ₀.toMonoidHom.comp ι) with hκdef
  have hκinj : Function.Injective κ :=
    E.subtype_injective.comp (Φ₀.injective.comp (q2OmMIota_injective hr3 hirr hK))
  have hκr : κ.range = modelToG e (complSp K k) := by
    rw [hκdef, MonoidHom.range_comp, MonoidHom.range_comp, hιdef, range_q2OmMIota, hfixmap]
  set lam : StatedSp r K →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((complSp K k).subtype.comp (complSpEquiv (K := K) k).toMonoidHom)) with hlamdef
  have hlaminj : Function.Injective lam := L.subtype_injective.comp (e.symm.injective.comp
    ((complSp K k).subtype_injective.comp (complSpEquiv (K := K) k).injective))
  have hlamr : lam.range = modelToG e (complSp K k) := by
    rw [hlamdef, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (complSpEquiv (K := K) k).surjective, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  set δ : MulAut (StatedSp r K) := ((MonoidHom.ofInjective hlaminj).trans
    (MulEquiv.subgroupCongr (hlamr.trans hκr.symm))).trans (MonoidHom.ofInjective hκinj).symm
    with hδdef
  have hκδ : ∀ g, κ (δ g) = lam g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκinj).apply_symm_apply
      (MulEquiv.subgroupCongr (hlamr.trans hκr.symm) (MonoidHom.ofInjective hlaminj g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, σ₀, hsσ⟩ := exists_eq_conj_mul_fieldSp hr3 δ
  rw [q2RingEquiv_eq_one hK σ₀, map_one, mul_one] at hsσ
  have hιs : kOmMBetaC K r b c (ι s) = ι s := by
    have hmem : ι s ∈ fixedSubgroup (kOmMBetaC K r b c) := by
      rw [hιdef, ← range_q2OmMIota hr3 hirr hK]
      exact ⟨s, rfl⟩
    exact hmem
  refine ⟨b, c, hirr, (MulAut.conj (ι s)).trans Φ₀, fun g => ?_, fun x => ?_⟩
  · change t * ((Φ₀ (ι s * g * (ι s)⁻¹) : E) : G) * t⁻¹ =
      ((Φ₀ (ι s * kOmMBetaC K r b c g * (ι s)⁻¹) : E) : G)
    have h2 : kOmMBetaC K r b c (ι s * g * (ι s)⁻¹) = ι s * kOmMBetaC K r b c g * (ι s)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hιs]
    rw [hΦ₀t, h2]
  · have h1 := hκδ x
    rw [hsσ, MulAut.conj_apply] at h1
    change ((Φ₀ (ι s * ι x * (ι s)⁻¹) : E) : G) = _
    rw [← map_inv, ← map_mul, ← map_mul]
    exact h1

end Param

end CFSG.SeitzReduction.SymplecticPilot
