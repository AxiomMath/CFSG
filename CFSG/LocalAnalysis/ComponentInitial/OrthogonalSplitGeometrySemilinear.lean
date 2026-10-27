module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRigidity

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)

variable {r : ℕ} {K : Type*} [Field K]

section Coord

@[expose] def sCoord (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) : Fin r ⊕ Fin r → K :=
  fun x => σ (v x)

@[simp] theorem sCoord_apply (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) (x : Fin r ⊕ Fin r) :
    sCoord σ v x = σ (v x) :=
  rfl

theorem sCoord_symm_sCoord (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) :
    sCoord σ.symm (sCoord σ v) = v :=
  funext fun _ => σ.symm_apply_apply _

theorem sCoord_sCoord_symm (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) :
    sCoord σ (sCoord σ.symm v) = v :=
  funext fun _ => σ.apply_symm_apply _

theorem sCoord_add (σ : K ≃+* K) (v w : Fin r ⊕ Fin r → K) :
    sCoord σ (v + w) = sCoord σ v + sCoord σ w :=
  funext fun _ => map_add σ _ _

theorem sCoord_smul (σ : K ≃+* K) (c : K) (v : Fin r ⊕ Fin r → K) :
    sCoord σ (c • v) = σ c • sCoord σ v :=
  funext fun _ => map_mul σ _ _

theorem sCoord_ne_zero (σ : K ≃+* K) {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) : sCoord σ v ≠ 0 :=
  fun h => hv (by rw [← sCoord_symm_sCoord σ v, h]; funext x; simp)

theorem quadPlus_sCoord (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) :
    quadPlus r K (sCoord σ v) = σ (quadPlus r K v) := by
  rw [quadPlus_apply, quadPlus_apply, map_sum]
  simp [map_mul]

theorem polar_sCoord (σ : K ≃+* K) (v w : Fin r ⊕ Fin r → K) :
    polar (quadPlus r K) (sCoord σ v) (sCoord σ w) = σ (polar (quadPlus r K) v w) := by
  rw [polar_quadPlus, polar_quadPlus, map_sum]
  simp [map_add, map_mul]

@[expose] def sCoordImage (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    Submodule K (Fin r ⊕ Fin r → K) where
  carrier := {v | sCoord σ.symm v ∈ W}
  add_mem' {v w} hv hw := by
    change sCoord σ.symm (v + w) ∈ W
    rw [sCoord_add]
    exact W.add_mem hv hw
  zero_mem' := by
    change sCoord σ.symm 0 ∈ W
    convert W.zero_mem using 1
    funext x
    simp
  smul_mem' c v hv := by
    change sCoord σ.symm (c • v) ∈ W
    rw [sCoord_smul]
    exact W.smul_mem _ hv

theorem mem_sCoordImage {σ : K ≃+* K} {W : Submodule K (Fin r ⊕ Fin r → K)}
    {v : Fin r ⊕ Fin r → K} : v ∈ sCoordImage σ W ↔ sCoord σ.symm v ∈ W :=
  Iff.rfl

theorem sCoord_mem_sCoordImage {σ : K ≃+* K} {W : Submodule K (Fin r ⊕ Fin r → K)}
    {w : Fin r ⊕ Fin r → K} : sCoord σ w ∈ sCoordImage σ W ↔ w ∈ W := by
  rw [mem_sCoordImage, sCoord_symm_sCoord]

theorem sCoordImage_symm_sCoordImage (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    sCoordImage σ.symm (sCoordImage σ W) = W := by
  ext v
  rw [mem_sCoordImage, mem_sCoordImage, RingEquiv.symm_symm, sCoord_symm_sCoord]

theorem sCoordImage_sCoordImage_symm (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    sCoordImage σ (sCoordImage σ.symm W) = W := by
  have := sCoordImage_symm_sCoordImage σ.symm W
  rwa [RingEquiv.symm_symm] at this

theorem sCoordImage_mono {σ : K ≃+* K} {W W' : Submodule K (Fin r ⊕ Fin r → K)} (h : W ≤ W') :
    sCoordImage σ W ≤ sCoordImage σ W' :=
  fun _ hv => h hv

theorem sCoordImage_le_iff {σ : K ≃+* K} {W W' : Submodule K (Fin r ⊕ Fin r → K)} :
    sCoordImage σ W ≤ sCoordImage σ W' ↔ W ≤ W' := by
  refine ⟨fun h => ?_, sCoordImage_mono⟩
  rw [← sCoordImage_symm_sCoordImage σ W, ← sCoordImage_symm_sCoordImage σ W']
  exact sCoordImage_mono h

theorem sCoordImage_span_singleton (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) :
    sCoordImage σ (K ∙ v) = K ∙ sCoord σ v := by
  ext u
  rw [mem_sCoordImage, mem_span_singleton, mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨σ c, ?_⟩
    rw [← sCoord_smul, hc, sCoord_sCoord_symm]
  · rintro ⟨c, rfl⟩
    refine ⟨σ.symm c, ?_⟩
    rw [sCoord_smul, sCoord_symm_sCoord]

theorem sCoordImage_refl (W : Submodule K (Fin r ⊕ Fin r → K)) :
    sCoordImage (RingEquiv.refl K) W = W := by
  ext v
  rfl

end Coord

section Semi

@[expose] def semiImage (A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (σ : K ≃+* K)
    (W : Submodule K (Fin r ⊕ Fin r → K)) : Submodule K (Fin r ⊕ Fin r → K) :=
  (sCoordImage σ W).map (A : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))

@[expose] def semiPreimage (A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (σ : K ≃+* K)
    (W : Submodule K (Fin r ⊕ Fin r → K)) : Submodule K (Fin r ⊕ Fin r → K) :=
  sCoordImage σ.symm (W.map (A.symm : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)))

variable (A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (σ : K ≃+* K)

theorem map_symm_map (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (W.map (A : (Fin r ⊕ Fin r → K) →ₗ[K] _)).map (A.symm : (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      W := by
  ext v
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

theorem map_map_symm (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (W.map (A.symm : (Fin r ⊕ Fin r → K) →ₗ[K] _)).map (A : (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      W := by
  have := map_symm_map A.symm W
  rwa [LinearEquiv.symm_symm] at this

theorem semiPreimage_semiImage (W : Submodule K (Fin r ⊕ Fin r → K)) :
    semiPreimage A σ (semiImage A σ W) = W := by
  rw [semiPreimage, semiImage, map_symm_map, sCoordImage_symm_sCoordImage]

theorem semiImage_semiPreimage (W : Submodule K (Fin r ⊕ Fin r → K)) :
    semiImage A σ (semiPreimage A σ W) = W := by
  rw [semiPreimage, semiImage, sCoordImage_sCoordImage_symm, map_map_symm]

theorem semiImage_mono {W W' : Submodule K (Fin r ⊕ Fin r → K)} (h : W ≤ W') :
    semiImage A σ W ≤ semiImage A σ W' :=
  Submodule.map_mono (sCoordImage_mono h)

theorem semiImage_le_iff {W W' : Submodule K (Fin r ⊕ Fin r → K)} :
    semiImage A σ W ≤ semiImage A σ W' ↔ W ≤ W' := by
  refine ⟨fun h => ?_, semiImage_mono A σ⟩
  rw [← semiPreimage_semiImage A σ W, ← semiPreimage_semiImage A σ W']
  exact sCoordImage_mono (Submodule.map_mono h)

theorem semiPreimage_mono {W W' : Submodule K (Fin r ⊕ Fin r → K)} (h : W ≤ W') :
    semiPreimage A σ W ≤ semiPreimage A σ W' :=
  sCoordImage_mono (Submodule.map_mono h)

theorem semiImage_span_singleton (v : Fin r ⊕ Fin r → K) :
    semiImage A σ (K ∙ v) = K ∙ A (sCoord σ v) := by
  rw [semiImage, sCoordImage_span_singleton, Submodule.map_span, Set.image_singleton]
  rfl

theorem semiPreimage_span_singleton (v : Fin r ⊕ Fin r → K) :
    semiPreimage A σ (K ∙ v) = K ∙ sCoord σ.symm (A.symm v) := by
  rw [semiPreimage, Submodule.map_span, Set.image_singleton, sCoordImage_span_singleton]
  rfl

variable {A} (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))
include hA

theorem quadPlus_semi (v : Fin r ⊕ Fin r → K) :
    quadPlus r K (A (sCoord σ v)) = σ (quadPlus r K v) := by
  rw [map_of_mem hA, quadPlus_sCoord]

theorem quadPlus_semiInv (v : Fin r ⊕ Fin r → K) :
    quadPlus r K (sCoord σ.symm (A.symm v)) = σ.symm (quadPlus r K v) := by
  rw [quadPlus_sCoord, ← map_of_mem hA (A.symm v), LinearEquiv.apply_symm_apply]

theorem polar_semi (v w : Fin r ⊕ Fin r → K) :
    polar (quadPlus r K) (A (sCoord σ v)) (A (sCoord σ w)) =
      σ (polar (quadPlus r K) v w) := by
  rw [polar_map_of_mem hA, polar_sCoord]

theorem totSing_semiImage {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) : ∀ v ∈ semiImage A σ W, quadPlus r K v = 0 := by
  rintro _ ⟨u, hu, rfl⟩
  have hu' : sCoord σ.symm u ∈ W := hu
  have h := quadPlus_semi σ hA (sCoord σ.symm u)
  rw [sCoord_sCoord_symm, hW _ hu', map_zero] at h
  exact h

theorem totSing_semiPreimage {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) : ∀ v ∈ semiPreimage A σ W, quadPlus r K v = 0 := by
  intro v hv
  rw [semiPreimage, mem_sCoordImage, RingEquiv.symm_symm, Submodule.mem_map_equiv,
    LinearEquiv.symm_symm] at hv
  have h := hW _ hv
  rw [map_of_mem hA, quadPlus_sCoord] at h
  exact (map_eq_zero_iff σ σ.injective).1 h

@[expose] noncomputable def semiPointEquiv : Points (quadPlus r K) ≃ Points (quadPlus r K) where
  toFun L := ⟨semiImage A σ L.val, by
    obtain ⟨v, hv0, hL⟩ := exists_eq_span_of_points L
    rw [hL, semiImage_span_singleton]
    exact finrank_span_singleton ((LinearEquiv.map_ne_zero_iff A).2 (sCoord_ne_zero σ hv0)),
    totSing_semiImage σ hA L.2.2⟩
  invFun L := ⟨semiPreimage A σ L.val, by
    obtain ⟨v, hv0, hL⟩ := exists_eq_span_of_points L
    rw [hL, semiPreimage_span_singleton]
    exact finrank_span_singleton (sCoord_ne_zero σ.symm ((LinearEquiv.map_ne_zero_iff _).2 hv0)),
    totSing_semiPreimage σ hA L.2.2⟩
  left_inv L := Subtype.ext (semiPreimage_semiImage A σ L.val)
  right_inv L := Subtype.ext (semiImage_semiPreimage A σ L.val)

theorem coe_semiPointEquiv (L : Points (quadPlus r K)) :
    (semiPointEquiv σ hA L).val = semiImage A σ L.val :=
  rfl

theorem coe_semiPointEquiv_symm (L : Points (quadPlus r K)) :
    ((semiPointEquiv σ hA).symm L).val = semiPreimage A σ L.val :=
  rfl

theorem polarOrtho_semiPointEquiv (L M : Points (quadPlus r K)) :
    PolarOrtho (quadPlus r K) L.val M.val ↔
      PolarOrtho (quadPlus r K) (semiPointEquiv σ hA L).val (semiPointEquiv σ hA M).val := by
  obtain ⟨v, -, hL⟩ := exists_eq_span_of_points L
  obtain ⟨w, -, hM⟩ := exists_eq_span_of_points M
  rw [coe_semiPointEquiv, coe_semiPointEquiv, hL, hM, semiImage_span_singleton,
    semiImage_span_singleton, polarOrtho_span_singleton, polarOrtho_span_singleton,
    polar_semi σ hA, map_eq_zero_iff σ σ.injective]

theorem image_ptsIn_semiPointEquiv (W : Submodule K (Fin r ⊕ Fin r → K)) :
    semiPointEquiv σ hA '' ptsIn (quadPlus r K) W = ptsIn (quadPlus r K) (semiImage A σ W) := by
  ext L
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact semiImage_mono A σ hM
  · intro hL
    refine ⟨(semiPointEquiv σ hA).symm L, ?_, Equiv.apply_symm_apply _ _⟩
    change semiPreimage A σ L.val ≤ W
    rw [← semiPreimage_semiImage A σ W]
    exact semiPreimage_mono A σ hL

theorem image_ptsIn_semiPointEquiv_symm (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (semiPointEquiv σ hA).symm '' ptsIn (quadPlus r K) W =
      ptsIn (quadPlus r K) (semiPreimage A σ W) := by
  ext L
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact semiPreimage_mono A σ hM
  · intro hL
    refine ⟨semiPointEquiv σ hA L, ?_, Equiv.symm_apply_apply _ _⟩
    change semiImage A σ L.val ≤ W
    rw [← semiImage_semiPreimage A σ W]
    exact semiImage_mono A σ hL

variable (φ : Points (quadPlus r K) ≃ Points (quadPlus r K))
  (hφ : ∀ L M : Points (quadPlus r K),
    PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (φ L).val (φ M).val)
include hφ

theorem polarOrtho_trans_symm (L M : Points (quadPlus r K)) :
    PolarOrtho (quadPlus r K) L.val M.val ↔
      PolarOrtho (quadPlus r K) ((φ.trans (semiPointEquiv σ hA).symm) L).val
        ((φ.trans (semiPointEquiv σ hA).symm) M).val := by
  have h := polarOrtho_semiPointEquiv σ hA ((semiPointEquiv σ hA).symm (φ L))
    ((semiPointEquiv σ hA).symm (φ M))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [hφ, Equiv.trans_apply, Equiv.trans_apply]
  exact h.symm

theorem polarImage_trans_symm {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) :
    polarImage r K (φ.trans (semiPointEquiv σ hA).symm) W =
      semiPreimage A σ (polarImage r K φ W) := by
  refine (eq_polarImage _ (totSing_semiPreimage σ hA (totSing_polarImage φ hφ hW)) ?_).symm
  rw [Equiv.coe_trans, Set.image_comp, ← ptsIn_polarImage φ hφ hW,
    image_ptsIn_semiPointEquiv_symm]

end Semi

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
