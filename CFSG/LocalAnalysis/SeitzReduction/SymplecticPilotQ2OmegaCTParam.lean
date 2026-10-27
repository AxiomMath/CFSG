module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBHigh
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphTwist
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus
  commutator_coordinateQuadPlus)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL mat_leviEmbedSL)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Siegel

variable {F : Type} [Field F] {m : ℕ}

theorem siegelBlockGL_le_statedOmega_of_three_le {B : Finset (Fin m)} (hB : 3 ≤ B.card) :
    OmegaPilot.siegelBlockGL F B ≤ StatedOmega (StatedQuadPlus m F) := by
  have hperf : ⁅OmegaPilot.siegelBlockGL F B, OmegaPilot.siegelBlockGL F B⁆ =
      OmegaPilot.siegelBlockGL F B := by
    rw [OmegaPilot.siegelBlockGL, ← Subgroup.map_commutator,
      commutator_siegelBlock_eq (LinearPilot.commutator_blockSpecialLinear_eq_of_three_le hB)]
  rw [← hperf, OmegaPilot.statedOmega_eq_commutator_isometryClosure]
  have h := (OmegaPilot.siegelBlockGL_le_omegaLeviSL B).trans
    ((OmegaPilot.omegaLeviSL_le_omegaLeviGL (F := F) (k := m)).trans
      (OmegaPilot.omegaLeviGL_le_isometryClosure (F := F) (k := m)))
  exact Subgroup.commutator_mono h h

end Siegel

section Res

variable (k : Type) [Field k] {r : ℕ} (hr : 2 ≤ r)

theorem exists_mem_fixedSubgroup_kOmegaFixRes_ne_one [CharP k 2] (hr3 : 3 ≤ r) :
    ∃ A : fixedSubgroup (kOmegaBetaC k r), kOmegaFixRes k hr A ≠ 1 := by
  classical
  set i0 : Fin (r + 1) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (r + 1) := ⟨1, by omega⟩ with hi1
  set i2 : Fin (r + 1) := ⟨2, by omega⟩ with hi2
  set B : Finset (Fin (r + 1)) := {i0, i1, i2} with hB
  have hBc : 3 ≤ B.card := by
    rw [hB, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hi1, hi2, Fin.ext_iff]
    · simp [hi0, hi1, hi2, Fin.ext_iff]
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  set C : SL(r + 1, k) := SpecialLinearGroup.transvection h01 1 with hCdef
  have hC : C ∈ blockSpecialLinear (K := k) B :=
    LinearPilot.transvection_mem_blockSpecialLinear h01 (by simp [hB]) (by simp [hB]) 1
  set x : StatedSp (r + 1) k := leviEmbedSL k (r + 1) C with hxdef
  have hxS : x ∈ siegelBlock k B := ⟨C, hC, rfl⟩
  have hxO : (x : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) ∈ StatedOmega (StatedQuadPlus (r + 1) k) :=
    siegelBlockGL_le_statedOmega_of_three_le hBc ⟨x, hxS, rfl⟩
  have hsupp := siegelBlock_le_spBlock B hxS
  have hlast : Fin.last r ∉ B := by
    simp only [hB, Finset.mem_insert, Finset.mem_singleton, hi0, hi1, hi2, Fin.ext_iff,
      Fin.val_last]
    omega
  set A : StatedOmega (StatedQuadPlus (r + 1) k) := ⟨_, hxO⟩ with hAdef
  have hfix : A ∈ fixedSubgroup (kOmegaBetaC k r) := by
    rw [mem_fixedSubgroup_kOmegaBetaC_iff k hr]
    have hcol : ∀ (a : Fin (r + 1) ⊕ Fin (r + 1)) (b : Fin (r + 1) ⊕ Fin (r + 1)),
        planeOf b = Fin.last r → mat (r + 1) k x a b = (1 : Matrix _ _ k) a b := by
      intro a b hb
      refine hsupp a b fun hab => hlast ?_
      have hbB := hab.2
      rw [mem_planeCoords, hb] at hbB
      exact hbB
    funext a
    change (mat (r + 1) k x *ᵥ kOmegaVec k r) a = kOmegaVec k r a
    simp only [kOmegaVec, Matrix.mulVec_add, Pi.add_apply, Matrix.mulVec_single_one]
    rw [Matrix.col_apply, Matrix.col_apply, hcol a _ (planeOf_inl _), hcol a _ (planeOf_inr _)]
    simp only [Matrix.one_apply, Pi.single_apply]
  refine ⟨⟨A, hfix⟩, fun h1 => ?_⟩
  have h2 := congrArg (fun y : StatedSp r k => mat r k y (Sum.inl ⟨0, by omega⟩)
    (Sum.inl ⟨1, by omega⟩)) h1
  simp only [map_one] at h2
  rw [mat_apply, coe_kOmegaFixRes] at h2
  simp only [submatrix_apply, kOmegaEmb, Sum.map_inl] at h2
  have h3 : ((x : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
      (Fin (r + 1) ⊕ Fin (r + 1)) k) (Sum.inl i0) (Sum.inl i1) = 1 := by
    rw [← mat_apply, hxdef, mat_leviEmbedSL, fromBlocks_apply₁₁, hCdef,
      SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne h01,
      single_apply_same, zero_add]
  have h4 : (Fin.castSucc (⟨0, by omega⟩ : Fin r)) = i0 := Fin.ext rfl
  have h5 : (Fin.castSucc (⟨1, by omega⟩ : Fin r)) = i1 := Fin.ext rfl
  rw [h4, h5] at h2
  change ((x : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
      (Fin (r + 1) ⊕ Fin (r + 1)) k) (Sum.inl i0) (Sum.inl i1) = _ at h2
  rw [h3, Matrix.one_apply_ne (by simp [Fin.ext_iff])] at h2
  exact one_ne_zero h2

variable [Finite k] [CharP k 2]

theorem kOmegaFixRes_injective_two (hK : Nat.card k = 2) (hr3 : 3 ≤ r) :
    Function.Injective (kOmegaFixRes k hr) := by
  obtain ⟨e⟩ := nonempty_fixedSubgroup_kOmegaBetaC_mulEquiv k hr3 (f := 1) le_rfl
    (by rw [hK, pow_one])
  have : IsSimpleGroup (StatedSp r k) := isSimpleGroup_statedSp_two hK hr3
  have : IsSimpleGroup (fixedSubgroup (kOmegaBetaC k r)) := e.isSimpleGroup
  rcases (kOmegaFixRes k hr).normal_ker.eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    obtain ⟨A, hA⟩ := exists_mem_fixedSubgroup_kOmegaFixRes_ne_one k hr hr3
    have hker : A ∈ (kOmegaFixRes k hr).ker := by
      rw [h]
      exact Subgroup.mem_top _
    exact hA hker

theorem kOmegaFixRes_bijective_two (hK : Nat.card k = 2) (hr3 : 3 ≤ r) :
    Function.Bijective (kOmegaFixRes k hr) := by
  obtain ⟨e⟩ := nonempty_fixedSubgroup_kOmegaBetaC_mulEquiv k hr3 (f := 1) le_rfl
    (by rw [hK, pow_one])
  exact (kOmegaFixRes_injective_two k hr hK hr3).bijective_of_nat_card_le
    (Nat.card_congr e.toEquiv).ge

variable {k}

@[expose] noncomputable def q2OmIota (hK : Nat.card k = 2) (hr3 : 3 ≤ r) :
    StatedSp r k →* StatedOmega (StatedQuadPlus (r + 1) k) :=
  (fixedSubgroup (kOmegaBetaC k r)).subtype.comp
    (MulEquiv.ofBijective (kOmegaFixRes k hr)
      (kOmegaFixRes_bijective_two k hr hK hr3)).symm.toMonoidHom

theorem q2OmIota_injective (hK : Nat.card k = 2) (hr3 : 3 ≤ r) :
    Function.Injective (q2OmIota hr hK hr3) :=
  (fixedSubgroup _).subtype_injective.comp (MulEquiv.injective _)

theorem range_q2OmIota (hK : Nat.card k = 2) (hr3 : 3 ≤ r) :
    (q2OmIota hr hK hr3).range = fixedSubgroup (kOmegaBetaC k r) := by
  rw [q2OmIota, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map, range_subtype]

theorem kOmegaFixRes_q2OmIota (hK : Nat.card k = 2) (hr3 : 3 ≤ r) (g : StatedSp r k) :
    ∃ y : fixedSubgroup (kOmegaBetaC k r), (y : StatedOmega (StatedQuadPlus (r + 1) k)) =
      q2OmIota hr hK hr3 g ∧ kOmegaFixRes k hr y = g :=
  ⟨_, rfl, MulEquiv.apply_symm_apply (MulEquiv.ofBijective (kOmegaFixRes k hr)
    (kOmegaFixRes_bijective_two k hr hK hr3)) g⟩

end Res

section Param


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_q2OmParam (hset : SeitzSetting G L) {r : ℕ} (hK : Nat.card K = 2) (hr : 2 ≤ r)
    (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (r + 1)) (h : NsKindSp e t k .omegaPlus) :
    ∃ Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃*
        centralizerPerfectCore (modelToG e (nsTorusSp K k)),
      (∀ g, t * ((Φ g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) * t⁻¹ =
        ((Φ (kOmegaBetaC K r g) : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G)) ∧
      ∀ x : StatedSp r K,
        ((Φ (q2OmIota hr hK hr3 x) : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
          ((e.symm (complSpEquiv k x) : L) : G) := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  set E := centralizerPerfectCore (modelToG e (nsTorusSp K k)) with hEdef
  have hN : t ∈ normalizer (E : Set G) :=
    UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _
  obtain ⟨hty, hout, hfix⟩ := nsCore_omega_facts_two (m := r) hset hK hr3 e htC ht k rfl rfl
    (Or.inl rfl) h hN
  have hty' : LieModel E .POmegaPlus (r + 1) 2 1 := hty
  obtain ⟨ε₀⟩ := OmegaPilot.nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hty' K hKc
  set π := F4Pilot.omegaProjEquiv (plusIndexEquiv (r + 1)) (quadPlus (r + 1) K)
    (coe_quadPlus (r + 1) K) (kOmega_matrixDerivedScalars_eq_bot K r) with hπ
  have hreg := regular_coordinateQuadPlus (K := K) (n := r + 1) (by omega)
  have hE := commutator_coordinateQuadPlus (K := K) (n := r + 1) (by omega)
  have hθθ : E.normalizerMonoidHom ⟨t, hN⟩ * E.normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (E : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hout hfix (le_refl 1) hKc
    (by omega : 4 ≤ r + 1) hreg.1 hreg.2 hE (kOmega_hconj K (by omega) le_rfl hKc)
    (kOmega_reindexQuadraticForm_vec K r) (ε₀.trans π)
  set Φ₀ : StatedOmega (StatedQuadPlus (r + 1) K) ≃* E := π.trans ψ with hΦ₀
  have hΦ₀t : ∀ g, t * ((Φ₀ g : E) : G) * t⁻¹ = ((Φ₀ (kOmegaBetaC K r g) : E) : G) := by
    intro g
    have h12 : (E.normalizerMonoidHom ⟨t, hN⟩) (ψ (π g)) = ψ (π (kOmegaBetaC K r g)) :=
      (hψ (π g)).trans (congrArg ψ (F4Pilot.omegaProjEquiv_omegaSymmetryAut _ _ _ _ _ g).symm)
    change t * ((ψ (π g) : E) : G) * t⁻¹ = ((ψ (π (kOmegaBetaC K r g)) : E) : G)
    rw [← h12, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hfixmap := map_fixedSubgroup_eq_of_comm_two (m := r) hset hK hr3 e htC ht k (Or.inl rfl) h
    Φ₀ (kOmegaBetaC K r) hΦ₀t
  set ι := q2OmIota (k := K) hr hK hr3 with hιdef
  set κ : StatedSp r K →* G := E.subtype.comp (Φ₀.toMonoidHom.comp ι) with hκdef
  have hκinj : Function.Injective κ :=
    E.subtype_injective.comp (Φ₀.injective.comp (q2OmIota_injective hr hK hr3))
  have hκr : κ.range = modelToG e (complSp K k) := by
    rw [hκdef, MonoidHom.range_comp, MonoidHom.range_comp, hιdef, range_q2OmIota, hfixmap]
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
  have hιs : kOmegaBetaC K r (ι s) = ι s := by
    have hmem : ι s ∈ fixedSubgroup (kOmegaBetaC K r) := by
      rw [hιdef, ← range_q2OmIota hr hK hr3]
      exact ⟨s, rfl⟩
    exact hmem
  refine ⟨(MulAut.conj (ι s)).trans Φ₀, fun g => ?_, fun x => ?_⟩
  · change t * ((Φ₀ (ι s * g * (ι s)⁻¹) : E) : G) * t⁻¹ =
      ((Φ₀ (ι s * kOmegaBetaC K r g * (ι s)⁻¹) : E) : G)
    have h2 : kOmegaBetaC K r (ι s * g * (ι s)⁻¹) = ι s * kOmegaBetaC K r g * (ι s)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hιs]
    rw [hΦ₀t, h2]
  · have h1 := hκδ x
    rw [hsσ, MulAut.conj_apply] at h1
    change ((Φ₀ (ι s * ι x * (ι s)⁻¹) : E) : G) = _
    rw [← map_inv, ← map_mul, ← map_mul]
    exact h1

end Param

end CFSG.SeitzReduction.SymplecticPilot
