module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEPlusPlace

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin

section Vectors

variable (K : Type) [Field K] {r : ℕ}

@[expose] def plBW (m : Fin (r + 1)) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl m : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
    pdPP (Fin.last r) +
      Pi.single (Sum.inr (Sum.inr 1) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1

variable {K} [CharP K 2]

theorem plB_polar_W (z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)
    (m : Fin (r + 1)) :
    polar (quadMinus (r + 1 + 1) K 1 1) z (plBW K m) =
      z (Sum.inr (Sum.inl m)) + (z (Sum.inr (Sum.inl (Fin.last r))) + z (Sum.inl (Fin.last r))) +
        z (Sum.inr (Sum.inr 0)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [plBW, polar_add_right, polar_add_right, polar_quadMinus_single_inl, pe_polar_pdPP,
    polar_quadMinus_single_inr_inr_one]
  linear_combination z (Sum.inr (Sum.inr 1)) * h2

omit [CharP K 2] in
theorem plB_quad_single_w :
    quadMinus (r + 1 + 1) K 1 1
      (Pi.single (Sum.inr (Sum.inr 1) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1) =
        1 := by
  rw [coe_quadMinus]
  simp [StatedQuadMinus]

theorem plB_quad_W {m : Fin (r + 1)} (hm : m ≠ Fin.last r) :
    quadMinus (r + 1 + 1) K 1 1 (plBW K m) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 : polar (quadMinus (r + 1 + 1) K 1 1)
      (Pi.single (Sum.inl m : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1)
      (pdPP (Fin.last r)) = 0 := by
    rw [pe_polar_pdPP]
    simp [hm]
  have e2 : polar (quadMinus (r + 1 + 1) K 1 1)
      (Pi.single (Sum.inl m : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
        pdPP (Fin.last r))
      (Pi.single (Sum.inr (Sum.inr 1) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1) =
        0 := by
    rw [polar_quadMinus_single_inr_inr_one]
    simp [pdPP]
  rw [plBW, QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)),
    QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)), pdP_single_quad_inl, pdPP_quad, e1,
    plB_quad_single_w, e2]
  linear_combination h2

theorem plB_polar_pePU_W {m : Fin (r + 1)} (hm : m ≠ Fin.last r) :
    polar (quadMinus (r + 1 + 1) K 1 1) (pePU K m) (plBW K m) = 0 := by
  rw [plB_polar_W]
  simp [pePU, pdPP, kOmMVec, Ne.symm hm, CharTwo.add_self_eq_zero]

theorem plB_polar_vec_W (m : Fin (r + 1)) :
    polar (quadMinus (r + 1 + 1) K 1 1) (kOmMVec K (r + 1)) (plBW K m) = 1 := by
  rw [plB_polar_W]
  simp [kOmMVec]

omit [CharP K 2] in
theorem plB_polar_W_pdPP {m j : Fin (r + 1)} (hmj : m ≠ j) (hj : j ≠ Fin.last r) :
    polar (quadMinus (r + 1 + 1) K 1 1) (plBW K m) (pdPP j) = 0 := by
  rw [pe_polar_pdPP]
  simp [plBW, pdPP, Ne.symm hmj, hj]

theorem plB_polar_inl_add_pdPP_W {m a b : Fin (r + 1)} (har : a ≠ Fin.last r)
    (hbm : b ≠ m) (hbr : b ≠ Fin.last r) :
    polar (quadMinus (r + 1 + 1) K 1 1)
      (Pi.single (Sum.inl a : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP b)
        (plBW K m) = 0 := by
  rw [plB_polar_W]
  simp [pdPP, Ne.symm hbm, Ne.symm hbr, Ne.symm har]

theorem plB_polar_inr_add_pdPP_W {m a b : Fin (r + 1)} (ham : a ≠ m) (har : a ≠ Fin.last r)
    (hbm : b ≠ m) (hbr : b ≠ Fin.last r) :
    polar (quadMinus (r + 1 + 1) K 1 1)
      (Pi.single (Sum.inr (Sum.inl a) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
        pdPP b) (plBW K m) = 0 := by
  rw [plB_polar_W]
  simp [pdPP, Ne.symm hbm, Ne.symm hbr, Ne.symm ham, Ne.symm har]

end Vectors

section Eichler

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

@[expose] noncomputable def plBSiegSpin {m j : Fin (r + 1)} (hm : m ≠ Fin.last r) (hmj : m ≠ j)
    (hj : j ≠ Fin.last r) : spinGroup (quadMinus (r + 1 + 1) K 1 1) :=
  peEichG (pe_quad_pePU m) (plB_polar_pePU_W hm) (pe_polar_pePU_pdPP hmj)
    (plB_polar_W_pdPP hmj hj) (by rw [pdPP_quad]; exact isUnit_one)

variable [Finite K] (hK : Nat.card K = 2) (hn : 4 ≤ r + 1 + 1)

@[expose] noncomputable def plBSieg {m j : Fin (r + 1)} (hm : m ≠ Fin.last r) (hmj : m ≠ j)
    (hj : j ≠ Fin.last r) : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1) :=
  peRhoM hn (q2Omega_irreducible_one_one hK) (plBSiegSpin hm hmj hj)

variable {m j : Fin (r + 1)} (hm : m ≠ Fin.last r) (hmj : m ≠ j) (hj : j ≠ Fin.last r)

theorem plBSieg_mulVec (z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) :
    (((plBSieg hK hn hm hmj hj : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ z =
      z + polar (quadMinus (r + 1 + 1) K 1 1) z (pePU K m) • plBW K m -
        polar (quadMinus (r + 1 + 1) K 1 1) z (plBW K m) • pePU K m := by
  rw [plBSieg, peRhoM_mulVec, plBSiegSpin, spinAction_peEichG _ (plB_quad_W hm)]

theorem plBSieg_mulVec_of_polar {z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K}
    (h1 : polar (quadMinus (r + 1 + 1) K 1 1) z (pePU K m) = 0)
    (h2 : polar (quadMinus (r + 1 + 1) K 1 1) z (plBW K m) = 0) :
    (((plBSieg hK hn hm hmj hj : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ z = z := by
  rw [plBSieg_mulVec hK hn hm hmj hj, h1, h2, zero_smul, zero_smul, add_zero, sub_zero]

theorem plBSieg_mulVec_vec :
    (((plBSieg hK hn hm hmj hj : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ kOmMVec K (r + 1) =
      pdPP m := by
  rw [plBSieg_mulVec hK hn hm hmj hj, pe_polar_vec_pePU, plB_polar_vec_W, zero_smul, add_zero,
    one_smul, pePU]
  funext c
  rw [Pi.sub_apply, Pi.add_apply, sub_add_cancel_right, CharTwo.neg_eq]

theorem plBSieg_mem_range (hr : 2 ≤ r) :
    plBSieg hK hn hm hmj hj ∈ (pcOPExt (K := K) (Fin.last r)).range := by
  have hne : Fin.last r ≠ m := Ne.symm hm
  refine (mem_pcOPExt_range_iff (Fin.last r) hK hr _).2 ⟨?_, ?_⟩
  · refine plBSieg_mulVec_of_polar hK hn hm hmj hj (pe_polar_pdPA_pePU hne) ?_
    rw [plB_polar_W]
    simp [pdPA, kOmMVec, CharTwo.add_self_eq_zero]
  · refine plBSieg_mulVec_of_polar hK hn hm hmj hj (pe_polar_pdPB_pePU hne) ?_
    rw [plB_polar_W]
    simp [pdPB, kOmMVec, hm, CharTwo.add_self_eq_zero]

theorem plBSieg_mulVec_inl_add_pdPP {a b : Fin (r + 1)} (ham : a ≠ m) (har : a ≠ Fin.last r)
    (hbm : b ≠ m) (hbr : b ≠ Fin.last r) :
    (((plBSieg hK hn hm hmj hj : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inl a : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP b) =
      Pi.single (Sum.inl a : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP b :=
  plBSieg_mulVec_of_polar hK hn hm hmj hj (pe_polar_inl_add_pdPP_pePU (Ne.symm ham))
    (plB_polar_inl_add_pdPP_W har hbm hbr)

theorem plBSieg_mulVec_inr_add_pdPP {a b : Fin (r + 1)} (ham : a ≠ m) (har : a ≠ Fin.last r)
    (hbm : b ≠ m) (hbr : b ≠ Fin.last r) :
    (((plBSieg hK hn hm hmj hj : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inr (Sum.inl a) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
          pdPP b) =
      Pi.single (Sum.inr (Sum.inl a) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
        pdPP b :=
  plBSieg_mulVec_of_polar hK hn hm hmj hj (pe_polar_inr_add_pdPP_pePU (Ne.symm ham))
    (plB_polar_inr_add_pdPP_W ham har hbm hbr)

theorem plBSieg_commute (A : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1))
    (hu : ((A : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pePU K m = pePU K m)
    (hw : ((A : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ plBW K m = plBW K m) :
    A * plBSieg hK hn hm hmj hj = plBSieg hK hn hm hmj hj * A := by
  have hiso : ∀ z, quadMinus (r + 1 + 1) K 1 1
      (((A : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ z) =
      quadMinus (r + 1 + 1) K 1 1 z := fun z => by
    rw [coe_quadMinus]
    exact pd_isometry_of_mem_statedOmega A.2 z
  have hpol : ∀ x y, polar (quadMinus (r + 1 + 1) K 1 1)
      (((A : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ x)
      (((A : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ y) =
      polar (quadMinus (r + 1 + 1) K 1 1) x y := fun x y => by
    rw [polar, polar, ← Matrix.mulVec_add, hiso, hiso, hiso]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  refine pd_matrix_ext_mulVec fun z => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, plBSieg_mulVec hK hn hm hmj hj,
    plBSieg_mulVec hK hn hm hmj hj, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, hu, hw]
  conv_rhs => rw [← hu, hpol, ← hw, hpol, hw, hu]

end Eichler

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2)
include hK

theorem plB_conj_mem_fixed (hr : 2 ≤ r) (E z : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1))
    (hz : ((z : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
          (((E : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
              (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ kOmMVec K (r + 1)) =
      ((E : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ kOmMVec K (r + 1)) :
    E⁻¹ * z * E ∈ fixedSubgroup (kOmMBetaC K (r + 1) 1 1) := by
  rw [mem_fixedSubgroup_kOmMBetaC_iff K (by omega) (q2Omega_irreducible_one_one hK)]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem plB_conj_mem_range_of_fix (hr : 2 ≤ r) (k : Fin (r + 1))
    (h g : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1))
    (hA : ((g : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
          (((h : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
              (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K k) =
      ((h : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K k)
    (hB : ((g : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
          (((h : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
              (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K k) =
      ((h : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K k) :
    h⁻¹ * g * h ∈ (pcOPExt (K := K) k).range := by
  rw [mem_pcOPExt_range_iff k hK hr]
  constructor
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hA, Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hB, Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end Conj

section Transporters

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2) (hr : 2 ≤ r)

@[expose] noncomputable def plBT01 : StatedSp (r + 1) K :=
  pePTr hK hr (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (m := ⟨2, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

@[expose] noncomputable def plBT21 : StatedSp (r + 1) K :=
  pePTr hK hr (i := ⟨2, by omega⟩) (j := ⟨1, by omega⟩) (m := ⟨0, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
    (Fin.ne_of_val_ne (by norm_num))

theorem q2OmMIota_plBT01 :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (plBT01 hK hr) =
      pePEich hK hr (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (m := ⟨2, by omega⟩)
        (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
        (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmMIota_pePTr hK hr _ _ _

theorem q2OmMIota_plBT21 :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (plBT21 hK hr) =
      pePEich hK hr (i := ⟨2, by omega⟩) (j := ⟨1, by omega⟩) (m := ⟨0, by omega⟩)
        (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
        (Fin.ne_of_val_ne (by norm_num)) :=
  q2OmMIota_pePTr hK hr _ _ _

theorem q2OmMIota_plBT01_mem_range {k : Fin (r + 1)} (h0 : k.val ≠ 0) (h1 : k.val ≠ 1) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (plBT01 hK hr) ∈
      (pcOPExt (K := K) k).range := by
  rw [q2OmMIota_plBT01]
  exact pePEich_mem_range _ _ _ _ _ (Fin.ne_of_val_ne (by simpa using h0))
    (Fin.ne_of_val_ne (by simpa using h1))

theorem q2OmMIota_plBT21_mem_range {k : Fin (r + 1)} (h2 : k.val ≠ 2) (h1 : k.val ≠ 1) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (plBT21 hK hr) ∈
      (pcOPExt (K := K) k).range := by
  rw [q2OmMIota_plBT21]
  exact pePEich_mem_range _ _ _ _ _ (Fin.ne_of_val_ne (by simpa using h2))
    (Fin.ne_of_val_ne (by simpa using h1))

theorem q2OmMIota_plBT0121_mem_range {k : Fin (r + 1)} (h0 : k.val ≠ 0) (h1 : k.val ≠ 1)
    (h2 : k.val ≠ 2) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
        (plBT01 hK hr * plBT21 hK hr) ∈ (pcOPExt (K := K) k).range := by
  rw [map_mul]
  exact mul_mem (q2OmMIota_plBT01_mem_range hK hr h0 h1) (q2OmMIota_plBT21_mem_range hK hr h2 h1)

theorem q2OmMIota_plBT01_mulVec_a :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (plBT01 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
              pdPA K ⟨0, by omega⟩ =
      Pi.single (Sum.inl ((⟨0, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩ := by
  rw [q2OmMIota_plBT01, pePEich_mulVec_a]

theorem q2OmMIota_plBT01_mulVec_b :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (plBT01 hK hr) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
              pdPB K ⟨0, by omega⟩ =
      Pi.single (Sum.inr (Sum.inl ((⟨0, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩ := by
  rw [q2OmMIota_plBT01, pePEich_mulVec_b]

theorem q2OmMIota_plBT0121_mulVec_a :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
      (plBT01 hK hr * plBT21 hK hr) : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
              pdPA K ⟨2, by omega⟩ =
      Pi.single (Sum.inl ((⟨2, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩ := by
  rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, q2OmMIota_plBT21,
    pePEich_mulVec_a, q2OmMIota_plBT01]
  exact pePEich_mulVec_of_polar _ _ _ _ _
    (pe_polar_inl_add_pdPP_pePU (Fin.ne_of_val_ne (by norm_num)))
    (pe_polar_inl_add_pdPP_pePU (Fin.ne_of_val_ne (by norm_num)))

theorem q2OmMIota_plBT0121_mulVec_b :
    (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
      (plBT01 hK hr * plBT21 hK hr) : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
              pdPB K ⟨2, by omega⟩ =
      Pi.single (Sum.inr (Sum.inl ((⟨2, by omega⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) :
        Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩ := by
  rw [map_mul, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, q2OmMIota_plBT21,
    pePEich_mulVec_b, q2OmMIota_plBT01]
  exact pePEich_mulVec_of_polar _ _ _ _ _
    (pe_polar_inr_add_pdPP_pePU (Fin.ne_of_val_ne (by norm_num)))
    (pe_polar_inr_add_pdPP_pePU (Fin.ne_of_val_ne (by norm_num)))

end Transporters

end CFSG.SeitzReduction.SymplecticPilot
