module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEMinusPlace

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin

section Vectors

variable (K : Type) [Field K] {r : ℕ}

@[expose] def plDW (m : Fin (r + 1)) : Fin (r + 2) ⊕ Fin (r + 2) → K :=
  Pi.single (.inl m.castSucc) 1 + pdMP (Fin.last r) + Pi.single (.inl (Fin.last (r + 1))) 1

variable {K}

theorem plD_polar_W (z : Fin (r + 2) ⊕ Fin (r + 2) → K) (m : Fin (r + 1)) :
    polar (quadPlus (r + 2) K) z (plDW K m) =
      z (.inr m.castSucc) + (z (.inr (Fin.last r).castSucc) + z (.inl (Fin.last r).castSucc)) +
        z (.inr (Fin.last (r + 1))) := by
  rw [plDW, polar_add_right, polar_add_right, polar_quadPlus_single_inl, pe_polar_pdMP,
    polar_quadPlus_single_inl]

theorem plD_castSucc_ne {m : Fin (r + 1)} (hm : m ≠ Fin.last r) :
    m.castSucc ≠ (Fin.last r).castSucc := fun h => hm (Fin.castSucc_injective _ h)

theorem plD_quad_W {m : Fin (r + 1)} (hm : m ≠ Fin.last r) : quadPlus (r + 2) K (plDW K m) = 1 := by
  have h1 : (m.castSucc : Fin (r + 2)) ≠ (Fin.last r).castSucc := plD_castSucc_ne hm
  rw [plDW, QuadraticMap.map_add (⇑(quadPlus (r + 2) K)),
    QuadraticMap.map_add (⇑(quadPlus (r + 2) K)), pdM_single_quad, pdM_single_quad, pdMP_quad,
    polar_add_left, polar_quadPlus_single_inl, polar_quadPlus_single_inl, pe_polar_pdMP]
  simp [pdMP, h1, Fin.castSucc_ne_last]

variable [CharP K 2]

theorem plD_polar_peMU_W {m : Fin (r + 1)} (hm : m ≠ Fin.last r) :
    polar (quadPlus (r + 2) K) (peMU K m) (plDW K m) = 0 := by
  have h1 : (Fin.last r).castSucc ≠ (m.castSucc : Fin (r + 2)) := (plD_castSucc_ne hm).symm
  rw [plD_polar_W]
  simp [peMU, pdMP, kOmegaVec, h1, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

omit [CharP K 2] in
theorem plD_polar_vec_W (m : Fin (r + 1)) :
    polar (quadPlus (r + 2) K) (kOmegaVec K (r + 1)) (plDW K m) = 1 := by
  rw [plD_polar_W]
  simp [kOmegaVec, Fin.castSucc_ne_last]

omit [CharP K 2] in
theorem plD_polar_peMU_of_peOff {S : Finset (Fin (r + 2))} {z : Fin (r + 2) ⊕ Fin (r + 2) → K}
    (hz : PEOff S z) {m : Fin (r + 1)} (hmS : m.castSucc ∈ S) (hNS : Fin.last (r + 1) ∈ S) :
    polar (quadPlus (r + 2) K) z (peMU K m) = 0 := by
  rw [pe_polar_peMU, (hz _ hmS).1, (hz _ hmS).2, (hz _ hNS).1, (hz _ hNS).2]
  simp

omit [CharP K 2] in
theorem plD_polar_W_of_peOff {S : Finset (Fin (r + 2))} {z : Fin (r + 2) ⊕ Fin (r + 2) → K}
    (hz : PEOff S z) {m : Fin (r + 1)} (hmS : m.castSucc ∈ S) (hrS : (Fin.last r).castSucc ∈ S)
    (hNS : Fin.last (r + 1) ∈ S) : polar (quadPlus (r + 2) K) z (plDW K m) = 0 := by
  rw [plD_polar_W, (hz _ hmS).2, (hz _ hrS).1, (hz _ hrS).2, (hz _ hNS).2]
  simp

end Vectors

section Siegel

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

@[expose] noncomputable def plDSiegSpin {m : Fin (r + 1)} (hm : m ≠ Fin.last r) :
    spinGroup (quadPlus (r + 2) K) :=
  rootHom (quadPlus (r + 2) K) (pe_quad_peMU m) (plD_polar_peMU_W hm)
    (one_add_smul_ι_mul_ι_mem_spinGroup_of_isUnit _ (pe_quad_peMU m) (plD_polar_peMU_W hm)
      (by rw [plD_quad_W hm]; exact isUnit_one)) (.ofAdd 1)

@[expose] noncomputable def plDSieg (hr : 1 ≤ r) {m : Fin (r + 1)} (hm : m ≠ Fin.last r) :
    StatedOmega (StatedQuadPlus (r + 2) K) :=
  peRho (n := r + 2) (by omega) (plDSiegSpin hm)

variable (hr : 1 ≤ r) {m : Fin (r + 1)} (hm : m ≠ Fin.last r)

theorem plDSieg_mulVec (z : Fin (r + 2) ⊕ Fin (r + 2) → K) :
    (((plDSieg hr hm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ z =
      z + polar (quadPlus (r + 2) K) z (peMU K m) • plDW K m -
        polar (quadPlus (r + 2) K) z (plDW K m) • peMU K m -
          polar (quadPlus (r + 2) K) z (peMU K m) • peMU K m := by
  rw [plDSieg, peRho_mulVec, plDSiegSpin, spinAction_rootHom, one_smul, plD_quad_W hm, one_mul]

theorem plDSieg_mulVec_of_polar {z : Fin (r + 2) ⊕ Fin (r + 2) → K}
    (h1 : polar (quadPlus (r + 2) K) z (peMU K m) = 0)
    (h2 : polar (quadPlus (r + 2) K) z (plDW K m) = 0) :
    (((plDSieg hr hm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ z = z := by
  rw [plDSieg_mulVec hr hm, h1, h2, zero_smul, zero_smul, add_zero, sub_zero, sub_zero]

theorem plDSieg_mulVec_of_peOff {S : Finset (Fin (r + 2))} {z : Fin (r + 2) ⊕ Fin (r + 2) → K}
    (hz : PEOff S z) (hmS : m.castSucc ∈ S) (hrS : (Fin.last r).castSucc ∈ S)
    (hNS : Fin.last (r + 1) ∈ S) :
    (((plDSieg hr hm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ z = z :=
  plDSieg_mulVec_of_polar hr hm (plD_polar_peMU_of_peOff hz hmS hNS)
    (plD_polar_W_of_peOff hz hmS hrS hNS)

theorem plDSieg_mulVec_vec :
    (((plDSieg hr hm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ kOmegaVec K (r + 1) = pdMP m := by
  rw [plDSieg_mulVec hr hm, pe_polar_vec_peMU, plD_polar_vec_W, zero_smul, zero_smul, add_zero,
    sub_zero, one_smul, peMU]
  funext c
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  rw [CharTwo.two_eq_zero, mul_zero, zero_add]

theorem plDSieg_mem_range [Finite K] (hK : Nat.card K = 2) (hr3 : 3 ≤ r) :
    plDSieg hr hm ∈ (pcOMExt (K := K) (Fin.last r)).range := by
  have hne : Fin.last r ≠ m := Ne.symm hm
  have h1 : (Fin.last r).castSucc ≠ (m.castSucc : Fin (r + 2)) := (plD_castSucc_ne hm).symm
  refine (mem_pcOMExt_range_iff (Fin.last r) hK hr3 _).2 ⟨?_, ?_⟩
  · refine plDSieg_mulVec_of_polar hr hm (pe_polar_pdMA_peMU hne) ?_
    rw [plD_polar_W]
    simp [pdMA, kOmegaVec, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]
  · refine plDSieg_mulVec_of_polar hr hm (pe_polar_pdMB_peMU hne) ?_
    rw [plD_polar_W]
    simp [pdMB, kOmegaVec, h1.symm, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

theorem plDSieg_commute (A : StatedOmega (StatedQuadPlus (r + 2) K))
    (hu : ((A : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
      (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ peMU K m = peMU K m)
    (hw : ((A : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
      (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ plDW K m = plDW K m) :
    A * plDSieg hr hm = plDSieg hr hm * A := by
  have hiso : ∀ z, quadPlus (r + 2) K (((A : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
      Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ z) =
      quadPlus (r + 2) K z := fun z => by
    rw [coe_quadPlus]
    exact pd_isometry_of_mem_statedOmega A.2 z
  have hpol : ∀ x y, polar (quadPlus (r + 2) K) (((A : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
      Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ x)
      (((A : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ y) =
      polar (quadPlus (r + 2) K) x y := fun x y => by
    rw [polar, polar, ← Matrix.mulVec_add, hiso, hiso, hiso]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  refine pd_matrix_ext_mulVec fun z => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, plDSieg_mulVec hr hm,
    plDSieg_mulVec hr hm, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hw]
  conv_rhs => rw [← hu, hpol, ← hw, hpol, hw, hu]

end Siegel

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

omit [Finite K] in
theorem plD_conj_mem_fixed (hr : 2 ≤ r) (E z : StatedOmega (StatedQuadPlus (r + 2) K))
    (hz : ((z : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
      (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ (((E : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          kOmegaVec K (r + 1)) =
      ((E : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ kOmegaVec K (r + 1)) :
    E⁻¹ * z * E ∈ fixedSubgroup (kOmegaBetaC K (r + 1)) := by
  rw [mem_fixedSubgroup_kOmegaBetaC_iff K (by omega)]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem plD_conj_mem_range_of_fix (hK : Nat.card K = 2) (hr3 : 3 ≤ r) (k : Fin (r + 1))
    (h g : StatedOmega (StatedQuadPlus (r + 2) K))
    (hA : ((g : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
      (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ (((h : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMA K k) =
      ((h : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMA K k)
    (hB : ((g : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
      (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ (((h : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMB K k) =
      ((h : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMB K k) :
    h⁻¹ * g * h ∈ (pcOMExt (K := K) k).range := by
  rw [mem_pcOMExt_range_iff k hK hr3]
  constructor
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hA, Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hB, Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end Conj

section Transporters

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2)
  (hr3 : 3 ≤ r)

omit [Finite K] in
@[expose] noncomputable def plDT01 : StatedSp (r + 1) K :=
  peMTr hr3 (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (m := ⟨2, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

omit [Finite K] in
@[expose] noncomputable def plDT21 : StatedSp (r + 1) K :=
  peMTr hr3 (i := ⟨2, by omega⟩) (j := ⟨1, by omega⟩) (m := ⟨0, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

theorem q2OmIota_plDT01 : q2OmIota (r := r + 1) (by omega) hK (by omega) (plDT01 hr3) =
    peMEich (K := K) (by omega) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (m := ⟨2, by omega⟩)
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmIota_peMTr hK hr3 _ _ _

theorem q2OmIota_plDT21 : q2OmIota (r := r + 1) (by omega) hK (by omega) (plDT21 hr3) =
    peMEich (K := K) (by omega) (i := ⟨2, by omega⟩) (j := ⟨1, by omega⟩) (m := ⟨0, by omega⟩)
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmIota_peMTr hK hr3 _ _ _

theorem q2OmIota_plDT01_mem_range {k : Fin (r + 1)} (h0 : k.val ≠ 0) (h1 : k.val ≠ 1) :
    q2OmIota (r := r + 1) (by omega) hK (by omega) (plDT01 hr3) ∈ (pcOMExt (K := K) k).range := by
  rw [q2OmIota_plDT01]
  exact peMEich_mem_range _ _ _ _ hK hr3 (Fin.ne_of_val_ne (by simpa using h0))
    (Fin.ne_of_val_ne (by simpa using h1))

theorem q2OmIota_plDT21_mem_range {k : Fin (r + 1)} (h2 : k.val ≠ 2) (h1 : k.val ≠ 1) :
    q2OmIota (r := r + 1) (by omega) hK (by omega) (plDT21 hr3) ∈ (pcOMExt (K := K) k).range := by
  rw [q2OmIota_plDT21]
  exact peMEich_mem_range _ _ _ _ hK hr3 (Fin.ne_of_val_ne (by simpa using h2))
    (Fin.ne_of_val_ne (by simpa using h1))

theorem q2OmIota_plDT0121_mem_range {k : Fin (r + 1)} (h0 : k.val ≠ 0) (h1 : k.val ≠ 1)
    (h2 : k.val ≠ 2) :
    q2OmIota (r := r + 1) (by omega) hK (by omega) (plDT01 hr3 * plDT21 hr3) ∈
      (pcOMExt (K := K) k).range := by
  rw [map_mul]
  exact mul_mem (q2OmIota_plDT01_mem_range hK hr3 h0 h1) (q2OmIota_plDT21_mem_range hK hr3 h2 h1)

theorem q2OmIota_plDT01_mulVec_a :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (plDT01 hr3) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMA K ⟨0, by omega⟩ =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩ := by
  rw [q2OmIota_plDT01, peMEich_mulVec_a]

theorem q2OmIota_plDT01_mulVec_b :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (plDT01 hr3) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMB K ⟨0, by omega⟩ =
      Pi.single (Sum.inr (⟨0, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩ := by
  rw [q2OmIota_plDT01, peMEich_mulVec_b]

theorem q2OmIota_plDT0121_mulVec_a :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (plDT01 hr3 * plDT21 hr3) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMA K ⟨2, by omega⟩ =
      Pi.single (Sum.inl (⟨2, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩ := by
  rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, q2OmIota_plDT21,
    peMEich_mulVec_a, q2OmIota_plDT01]
  exact peMEich_mulVec_of_polar _ _ _ _
    (pe_polar_inl_add_pdMP_peMU (Fin.ne_of_val_ne (by norm_num)))
    (pe_polar_inl_add_pdMP_peMU (Fin.ne_of_val_ne (by norm_num)))

theorem q2OmIota_plDT0121_mulVec_b :
    (((q2OmIota (r := r + 1) (by omega) hK (by omega) (plDT01 hr3 * plDT21 hr3) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          pdMB K ⟨2, by omega⟩ =
      Pi.single (Sum.inr (⟨2, by omega⟩ : Fin (r + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩ := by
  rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, q2OmIota_plDT21,
    peMEich_mulVec_b, q2OmIota_plDT01]
  exact peMEich_mulVec_of_polar _ _ _ _
    (pe_polar_inr_add_pdMP_peMU (Fin.ne_of_val_ne (by norm_num)))
    (pe_polar_inr_add_pdMP_peMU (Fin.ne_of_val_ne (by norm_num)))

end Transporters

end CFSG.SeitzReduction.SymplecticPilot
