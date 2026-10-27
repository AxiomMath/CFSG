module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCPlusFrame

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus
  polar_quadMinus_single_inl polar_quadMinus_single_inr_inl polar_quadMinus_single_inr_inr_zero
  polar_quadMinus_single_inr_inr_one)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

section Vectors

variable (K : Type) [Field K] {r : ℕ} (k : Fin (r + 1))

@[expose] def pdPA : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl k : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + kOmMVec K (r + 1)

@[expose] def pdPB : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inr (Sum.inl k) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
    kOmMVec K (r + 1)

variable {K} [CharP K 2]

theorem pdP_polar_vec (z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus (r + 1 + 1) K 1 1) z (kOmMVec K (r + 1)) = z (Sum.inr (Sum.inr 1)) := by
  rw [kOmMVec, polar_quadMinus_single_inr_inr_zero, CharTwo.two_eq_zero, zero_mul, zero_add,
    one_mul]

theorem pdP_polar_a (z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus (r + 1 + 1) K 1 1) z (pdPA K k) =
      z (Sum.inr (Sum.inl k)) + z (Sum.inr (Sum.inr 1)) := by
  rw [pdPA, polar_add_right, polar_quadMinus_single_inl, pdP_polar_vec]

theorem pdP_polar_b (z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus (r + 1 + 1) K 1 1) z (pdPB K k) = z (Sum.inl k) + z (Sum.inr (Sum.inr 1)) := by
  rw [pdPB, polar_add_right, polar_quadMinus_single_inr_inl, pdP_polar_vec]

omit [CharP K 2] in
theorem pdP_single_quad_inl (j : Fin (r + 1 + 1 - 1)) :
    quadMinus (r + 1 + 1) K 1 1 (Pi.single (Sum.inl j) 1) = 0 := by
  rw [coe_quadMinus]
  simp [StatedQuadMinus, Pi.single_apply]

omit [CharP K 2] in
theorem pdP_single_quad_inr (j : Fin (r + 1 + 1 - 1)) :
    quadMinus (r + 1 + 1) K 1 1 (Pi.single (Sum.inr (Sum.inl j)) 1) = 0 := by
  rw [coe_quadMinus]
  simp [StatedQuadMinus, Pi.single_apply]

theorem pdP_quad_a : quadMinus (r + 1 + 1) K 1 1 (pdPA K k) = 1 := by
  rw [pdPA, QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)), pdP_single_quad_inl,
    kOmM_quadMinus_vec, pdP_polar_vec]
  simp

theorem pdP_quad_b : quadMinus (r + 1 + 1) K 1 1 (pdPB K k) = 1 := by
  rw [pdPB, QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)), pdP_single_quad_inr,
    kOmM_quadMinus_vec, pdP_polar_vec]
  simp

theorem pdP_polar_ab : polar (quadMinus (r + 1 + 1) K 1 1) (pdPA K k) (pdPB K k) = 1 := by
  rw [pdP_polar_b]
  simp [pdPA, kOmMVec]

theorem pdP_polar_vec_a :
    polar (quadMinus (r + 1 + 1) K 1 1) (kOmMVec K (r + 1)) (pdPA K k) = 0 := by
  rw [pdP_polar_a]
  simp [kOmMVec]

theorem pdP_polar_vec_b :
    polar (quadMinus (r + 1 + 1) K 1 1) (kOmMVec K (r + 1)) (pdPB K k) = 0 := by
  rw [pdP_polar_b]
  simp [kOmMVec]

end Vectors

section Plane

variable {K : Type} [Field K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

theorem pcOPProj_mulVec_vec : pcOPProj K k *ᵥ kOmMVec K (r + 1) = kOmegaVec K r := by
  rw [← pcOPMat_mulVec_vec k, Matrix.mulVec_mulVec, pcOPProj_mul_pcOPMat, Matrix.one_mulVec]

theorem pcOPProj_mulVec_a : pcOPProj K k *ᵥ pdPA K k = 0 := by
  rw [pdPA, Matrix.mulVec_add, pcOPProj_mulVec_single_k k _ (Or.inl rfl), pcOPProj_mulVec_vec,
    pd_add_self]

theorem pcOPProj_mulVec_b : pcOPProj K k *ᵥ pdPB K k = 0 := by
  rw [pdPB, Matrix.mulVec_add, pcOPProj_mulVec_single_k k _ (Or.inr rfl), pcOPProj_mulVec_vec,
    pd_add_self]

theorem pdP_ker {z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K}
    (hz : pcOPProj K k *ᵥ z = 0) :
    z = z (Sum.inl k) • pdPA K k + z (Sum.inr (Sum.inl k)) • pdPB K k := by
  have h1 : ∀ i : Fin r, z (Sum.inl (k.succAbove i)) = 0 := fun i => by
    rw [← pcOPProj_mulVec_inl k z i, hz, Pi.zero_apply]
  have h2 : ∀ i : Fin r, z (Sum.inr (Sum.inl (k.succAbove i))) = 0 := fun i => by
    rw [← pcOPProj_mulVec_inr k z i, hz, Pi.zero_apply]
  have hp : z (Sum.inr (Sum.inr 1)) + z (Sum.inr (Sum.inr 0)) + z (Sum.inl k) +
      z (Sum.inr (Sum.inl k)) = 0 := by
    rw [← pcOPProj_mulVec_p k z, hz, Pi.zero_apply]
  have hq : z (Sum.inr (Sum.inr 0)) + z (Sum.inl k) + z (Sum.inr (Sum.inl k)) = 0 := by
    rw [← pcOPProj_mulVec_q k z, hz, Pi.zero_apply]
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hu : z (Sum.inr (Sum.inr 0)) = z (Sum.inl k) + z (Sum.inr (Sum.inl k)) := by
    linear_combination hq - (z (Sum.inl k) + z (Sum.inr (Sum.inl k))) * h22
  have hw : z (Sum.inr (Sum.inr 1)) = 0 := by linear_combination hp - hq
  funext j
  rcases j with m | m | t
  · rcases Fin.eq_self_or_eq_succAbove k m with rfl | ⟨i, rfl⟩
    · simp [pdPA, pdPB, kOmMVec]
    · simp [pdPA, pdPB, kOmMVec, h1, Fin.succAbove_ne]
  · rcases Fin.eq_self_or_eq_succAbove k m with rfl | ⟨i, rfl⟩
    · simp [pdPA, pdPB, kOmMVec]
    · simp [pdPA, pdPB, kOmMVec, h2, Fin.succAbove_ne]
  · fin_cases t
    · simp [pdPA, pdPB, kOmMVec, hu]
    · simp [pdPA, pdPB, kOmMVec, hw]

theorem pcOP_quad' (x : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)
    (y : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    quadMinus (r + 1 + 1) K 1 1 (x + pcOPMat K k *ᵥ y) - quadMinus (r + 1 + 1) K 1 1 x =
      quadPlus (r + 1) K (pcOPProj K k *ᵥ x + y) - quadPlus (r + 1) K (pcOPProj K k *ᵥ x) := by
  rw [coe_quadPlus, coe_quadMinus]
  exact pcOP_quad k x y

theorem isPDFramePlane_pcOP :
    IsPDFramePlane (pcOPMat K k) (pcOPProj K k) (quadMinus (r + 1 + 1) K 1 1) (quadPlus (r + 1) K)
      (pdPA K k) (pdPB K k) :=
  ⟨pcOPProj_mul_pcOPMat k, pcOP_quad' k, pcOPProj_mulVec_a k, pcOPProj_mulVec_b k,
    fun _ hz => ⟨_, _, pdP_ker k hz⟩, pdP_quad_a k, pdP_quad_b k, pdP_polar_ab k⟩

theorem coe_pcOPExt (g : StatedOmega (StatedQuadPlus (r + 1) K)) :
    (((pcOPExt k g : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) =
      pcExtMat (pcOPMat K k) (pcOPProj K k) ((g : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K) := rfl

end Plane

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

theorem pdP_rot_mem (hK : Nat.card K = 2) (hr : 2 ≤ r) :
    pdRotGL (pdP_polar_ab k) ∈ StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1) := by
  have h := pdRotGL_mem_statedOmega (pdP_quad_a k) (pdP_quad_b k) (pdP_polar_ab k)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (r + 1 + 1) K
      (q2Omega_irreducible_one_one hK))
    (pd_exists_totallySingular_quadMinus (by omega) K 1 1)
  rwa [coe_quadMinus] at h

@[expose] noncomputable def pdPRot (hK : Nat.card K = 2) (hr : 2 ≤ r) :
    StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1) :=
  ⟨pdRotGL (pdP_polar_ab k), pdP_rot_mem k hK hr⟩

theorem coe_pdPRot (hK : Nat.card K = 2) (hr : 2 ≤ r) :
    (((pdPRot k hK hr : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) =
        pdRotMat (quadMinus (r + 1 + 1) K 1 1) (pdPA K k) (pdPB K k) := rfl

theorem pcOPExt_range_le_centralizer (hK : Nat.card K = 2) (hr : 2 ≤ r) :
    (pcOPExt (K := K) k).range ≤ centralizer {pdPRot k hK hr} := by
  rintro _ ⟨h, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_pcOPExt, coe_pdPRot]
  exact ((isPDFramePlane_pcOP k).rot_commute _).symm

theorem mem_pcOPExt_range_iff (hK : Nat.card K = 2) (hr : 2 ≤ r)
    (g : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
    g ∈ (pcOPExt (K := K) k).range ↔
      ((g : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K k = pdPA K k ∧
      ((g : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K k = pdPB K k := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [coe_pcOPExt]
    exact (isPDFramePlane_pcOP k).ext_fix _
  · rintro ⟨ha, hb⟩
    have hg : (g : GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) ∈
        StatedOmega ⇑(quadMinus (r + 1 + 1) K 1 1) := by
      rw [coe_quadMinus]
      exact g.2
    obtain ⟨h, hh, he⟩ := (isPDFramePlane_pcOP k).exists_eq_of_fix
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (r + 1 + 1) K
        (q2Omega_irreducible_one_one hK))
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (r + 1) K)
      (pd_exists_totallySingular_quadPlus (by omega) K) hg ha hb
    rw [coe_quadPlus] at hh
    exact ⟨⟨h, hh⟩, Subtype.ext (Units.ext he)⟩

theorem le_pcOPExt_range_of_perfect (hK : Nat.card K = 2) (hr : 2 ≤ r)
    {P : Subgroup (StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1))} (hP : ⁅P, P⁆ = P)
    (hPc : P ≤ centralizer {pdPRot k hK hr}) : P ≤ (pcOPExt (K := K) k).range := by
  intro g hg
  have h := (isPDFramePlane_pcOP k).fix_of_perfect hP (pdP_rot_mem k hK hr) hPc hg
  exact (mem_pcOPExt_range_iff k hK hr g).2 h

theorem q2OmMIota_nsElt_eq (hK : Nat.card K = 2) (hr : 2 ≤ r) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK (nsElt k) =
      pdPRot k hK hr := by
  have hirr := q2Omega_irreducible_one_one hK
  have hA : pdPRot k hK hr ∈ fixedSubgroup (kOmMBetaC K (r + 1) 1 1) := by
    rw [mem_fixedSubgroup_kOmMBetaC_iff K (by omega) hirr, coe_pdPRot]
    exact pdRotMat_mulVec_of_polar (pdP_polar_vec_a k) (pdP_polar_vec_b k)
  have hres : kOmMFixRes K (by omega : 3 ≤ r + 1) hirr ⟨_, hA⟩ = nsElt k := by
    apply mat_injective
    rw [mat_apply, coe_kOmMFixRes, mat_nsElt]
    ext a' b'
    rw [Matrix.submatrix_apply]
    change pdRotMat (quadMinus (r + 1 + 1) K 1 1) (pdPA K k) (pdPB K k) (kOmMEmb (r + 1) a')
      (kOmMEmb (r + 1) b') = _
    have hcol : pdRotMat (quadMinus (r + 1 + 1) K 1 1) (pdPA K k) (pdPB K k) (kOmMEmb (r + 1) a')
        (kOmMEmb (r + 1) b') = (pdRotMat (quadMinus (r + 1 + 1) K 1 1) (pdPA K k) (pdPB K k) *ᵥ
          Pi.single (kOmMEmb (r + 1) b') 1) (kOmMEmb (r + 1) a') := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hcol, pdRotMat_mulVec, pdP_polar_a, pdP_polar_b]
    clear hcol
    rcases a' with i | i <;> rcases b' with j | j <;>
      simp [kOmMEmb, pdPA, pdPB, kOmMVec, Pi.single_apply, CFSG.LieType.Steinberg.Sp.blockMat,
        zThreeMat, Matrix.one_apply, CharTwo.neg_eq] <;>
      by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp_all [Pi.single_apply, CharTwo.add_self_eq_zero, eq_comm]
  have hι : q2OmMIota (r := r + 1) (by omega) hirr hK
      (kOmMFixRes K (by omega : 3 ≤ r + 1) hirr ⟨_, hA⟩) = pdPRot k hK hr := by
    have h := (MulEquiv.ofBijective (kOmMFixRes K (by omega : 3 ≤ r + 1) hirr)
      (kOmMFixRes_bijective_two K (by omega) hirr hK)).symm_apply_apply ⟨_, hA⟩
    exact congrArg Subtype.val h
  rw [← hres, hι]

end Levi

section Beta

variable {K : Type} [Field K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

theorem pcOPExt_kOmegaBetaC (a : StatedOmega (StatedQuadPlus (r + 1) K)) :
    pcOPExt k (kOmegaBetaC K r a) = kOmMBetaC K (r + 1) 1 1 (pcOPExt k a) := by
  have h1 : ((kOmegaBetaC K r a : StatedOmega (StatedQuadPlus (r + 1) K)) :
      GL (Fin (r + 1) ⊕ Fin (r + 1)) K) =
      pdSym (quadPlus (r + 1) K) (kOmegaVec K r) * (a : GL _ K) *
        pdSym (quadPlus (r + 1) K) (kOmegaVec K r) :=
    pd_coe_omegaSymmetryAut _ (quadPlus (r + 1) K) (coe_quadPlus (r + 1) K)
      (kOmega_matrixDerivedScalars_eq_bot K r) (kOmega_quadPlus_vec K r) a
  have h2 : ((kOmMBetaC K (r + 1) 1 1 (pcOPExt k a) :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) =
      pdSym (quadMinus (r + 1 + 1) K 1 1) (kOmMVec K (r + 1)) * (pcOPExt k a : GL _ K) *
        pdSym (quadMinus (r + 1 + 1) K 1 1) (kOmMVec K (r + 1)) :=
    pd_coe_omegaSymmetryAut _ (quadMinus (r + 1 + 1) K 1 1) (coe_quadMinus (r + 1 + 1) K 1 1)
      (kOmM_matrixDerivedScalars_eq_bot K (r + 1) 1 1) (kOmM_quadMinus_vec K (r + 1)) _
  apply Subtype.ext
  apply Units.ext
  rw [h2, coe_pcOPExt, h1, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    coe_pcOPExt]
  exact pcExtMat_sym_conj (pcOPProj_mul_pcOPMat k) (pcOP_quad' k) (pcOPMat_mulVec_vec k)
    (kOmega_quadPlus_vec K r) (kOmM_quadMinus_vec K (r + 1)) _

end Beta

section Triple

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

@[expose] def pdPP (j : Fin (r + 1)) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl j : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
    Pi.single (Sum.inr (Sum.inl j) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1

@[expose] def pdPW (o k l m : Fin (r + 1)) :
    Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inr (Sum.inr 1) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
    (pdPP o + pdPP k + pdPP l + pdPP m)

variable {o k l m : Fin (r + 1)}

omit [CharP K 2] in
theorem pdPW_apply_w : pdPW (K := K) o k l m (Sum.inr (Sum.inr 1)) = 1 := by
  simp [pdPW, pdPP]

omit [CharP K 2] in
theorem pdPW_apply_u : pdPW (K := K) o k l m (Sum.inr (Sum.inr 0)) = 0 := by
  simp [pdPW, pdPP]

omit [CharP K 2] in
theorem pdPW_apply_inl (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) (hom : o ≠ m) (hkm : k ≠ m)
    (hlm : l ≠ m) {j : Fin (r + 1)} (hj : j = o ∨ j = k ∨ j = l) :
    pdPW (K := K) o k l m (Sum.inl j) = 1 := by
  rcases hj with rfl | rfl | rfl <;>
    simp [pdPW, pdPP, hok, hol, hkl, hom, hkm, hlm, Ne.symm hok, Ne.symm hol, Ne.symm hkl]

omit [CharP K 2] in
theorem pdPW_apply_inr (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) (hom : o ≠ m) (hkm : k ≠ m)
    (hlm : l ≠ m) {j : Fin (r + 1)} (hj : j = o ∨ j = k ∨ j = l) :
    pdPW (K := K) o k l m (Sum.inr (Sum.inl j)) = 1 := by
  rcases hj with rfl | rfl | rfl <;>
    simp [pdPW, pdPP, hok, hol, hkl, hom, hkm, hlm, Ne.symm hok, Ne.symm hol, Ne.symm hkl]

omit [CharP K 2] in
theorem pdPP_quad (j : Fin (r + 1)) : quadMinus (r + 1 + 1) K 1 1 (pdPP j) = 1 := by
  rw [pdPP, QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)), pdP_single_quad_inl,
    pdP_single_quad_inr, polar_quadMinus_single_inr_inl]
  simp

omit [CharP K 2] in
theorem pdPP_polar (j j' : Fin (r + 1)) (h : j ≠ j') :
    polar (quadMinus (r + 1 + 1) K 1 1) (pdPP j) (pdPP j') = 0 := by
  rw [show (pdPP j' : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) =
    Pi.single (Sum.inl j' : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
      Pi.single (Sum.inr (Sum.inl j') : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1
    from rfl, polar_add_right, polar_quadMinus_single_inl, polar_quadMinus_single_inr_inl]
  simp [pdPP, Ne.symm h]

theorem pdPW_quad (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) (hom : o ≠ m) (hkm : k ≠ m)
    (hlm : l ≠ m) : quadMinus (r + 1 + 1) K 1 1 (pdPW o k l m) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e0 : quadMinus (r + 1 + 1) K 1 1
      (Pi.single (Sum.inr (Sum.inr 1) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1) =
        1 := by
    rw [coe_quadMinus]
    simp [StatedQuadMinus]
  have e1 : polar (quadMinus (r + 1 + 1) K 1 1)
      (Pi.single (Sum.inr (Sum.inr 1) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1)
      (pdPP o + pdPP k + pdPP l + pdPP m) = 0 := by
    rw [polar_comm, polar_quadMinus_single_inr_inr_one]
    simp [pdPP]
  rw [pdPW, QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)), e0, e1,
    QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)),
    QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)),
    QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)), pdPP_quad, pdPP_quad, pdPP_quad,
    pdPP_quad, pdPP_polar o k hok, polar_add_left, pdPP_polar o l hol, pdPP_polar k l hkl,
    polar_add_left, polar_add_left, pdPP_polar o m hom, pdPP_polar k m hkm, pdPP_polar l m hlm]
  linear_combination 2 * h2

theorem pdPW_polar_a (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) (hom : o ≠ m) (hkm : k ≠ m)
    (hlm : l ≠ m) {j : Fin (r + 1)} (hj : j = o ∨ j = k ∨ j = l) :
    polar (quadMinus (r + 1 + 1) K 1 1) (pdPW o k l m) (pdPA K j) = 0 := by
  rw [pdP_polar_a, pdPW_apply_inr hok hol hkl hom hkm hlm hj, pdPW_apply_w,
    CharTwo.add_self_eq_zero]

theorem pdPW_polar_b (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) (hom : o ≠ m) (hkm : k ≠ m)
    (hlm : l ≠ m) {j : Fin (r + 1)} (hj : j = o ∨ j = k ∨ j = l) :
    polar (quadMinus (r + 1 + 1) K 1 1) (pdPW o k l m) (pdPB K j) = 0 := by
  rw [pdP_polar_b, pdPW_apply_inl hok hol hkl hom hkm hlm hj, pdPW_apply_w,
    CharTwo.add_self_eq_zero]

theorem pdPW_polar_vec :
    polar (quadMinus (r + 1 + 1) K 1 1) (kOmMVec K (r + 1)) (pdPW o k l m) = 1 := by
  rw [polar_comm, pdP_polar_vec, pdPW_apply_w]

variable [Finite K]

theorem exists_triple_pcOPExt (hK : Nat.card K = 2) (hr : 3 ≤ r) (hok : o ≠ k) (hol : o ≠ l)
    (hkl : k ≠ l) :
    ∃ a b c : StatedOmega (StatedQuadPlus (r + 1) K), pcOPExt o a = pcOPExt k b ∧
      pcOPExt o a = pcOPExt l c ∧ kOmMBetaC K (r + 1) 1 1 (pcOPExt o a) ≠ pcOPExt o a := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({o, k, l} : Finset (Fin (r + 1)))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      exact (Finset.card_le_three).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  obtain ⟨hmo, hmk, hml⟩ := hm
  have hv : quadMinus (r + 1 + 1) K 1 1 (kOmMVec K (r + 1)) = 1 := kOmM_quadMinus_vec K (r + 1)
  have hw : quadMinus (r + 1 + 1) K 1 1 (pdPW o k l m) = 1 :=
    pdPW_quad hok hol hkl (Ne.symm hmo) (Ne.symm hmk) (Ne.symm hml)
  have hvw : polar (quadMinus (r + 1 + 1) K 1 1) (kOmMVec K (r + 1)) (pdPW o k l m) = 1 :=
    pdPW_polar_vec
  have hmem : pdRotGL hvw ∈ StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1) := by
    have h := pdRotGL_mem_statedOmega hv hw hvw
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (r + 1 + 1) K
        (q2Omega_irreducible_one_one hK))
      (pd_exists_totallySingular_quadMinus (by omega) K 1 1)
    rwa [coe_quadMinus] at h
  set g : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1) := ⟨pdRotGL hvw, hmem⟩ with hg
  have hfix : ∀ j, (j = o ∨ j = k ∨ j = l) → g ∈ (pcOPExt (K := K) j).range := by
    intro j hj
    rw [mem_pcOPExt_range_iff j hK (by omega)]
    refine ⟨pdRotMat_mulVec_of_polar ?_ ?_, pdRotMat_mulVec_of_polar ?_ ?_⟩
    · rw [polar_comm]
      exact pdP_polar_vec_a j
    · rw [polar_comm]
      exact pdPW_polar_a hok hol hkl (Ne.symm hmo) (Ne.symm hmk) (Ne.symm hml) hj
    · rw [polar_comm]
      exact pdP_polar_vec_b j
    · rw [polar_comm]
      exact pdPW_polar_b hok hol hkl (Ne.symm hmo) (Ne.symm hmk) (Ne.symm hml) hj
  obtain ⟨a, ha⟩ := hfix o (Or.inl rfl)
  obtain ⟨b, hb⟩ := hfix k (Or.inr (Or.inl rfl))
  obtain ⟨c, hc⟩ := hfix l (Or.inr (Or.inr rfl))
  refine ⟨a, b, c, ha.trans hb.symm, ha.trans hc.symm, ?_⟩
  rw [ha]
  intro h
  have h1 : g ∈ fixedSubgroup (kOmMBetaC K (r + 1) 1 1) := h
  rw [mem_fixedSubgroup_kOmMBetaC_iff K (by omega) (q2Omega_irreducible_one_one hK)] at h1
  have h2 : pdRotMat (quadMinus (r + 1 + 1) K 1 1) (kOmMVec K (r + 1)) (pdPW o k l m) *ᵥ
      kOmMVec K (r + 1) = pdPW o k l m := pdRotMat_mulVec_a hvw
  have h3 := congrFun (h2.symm.trans h1) (Sum.inr (Sum.inr 0))
  rw [pdPW_apply_u] at h3
  simp [kOmMVec] at h3

end Triple

end CFSG.SeitzReduction.SymplecticPilot
