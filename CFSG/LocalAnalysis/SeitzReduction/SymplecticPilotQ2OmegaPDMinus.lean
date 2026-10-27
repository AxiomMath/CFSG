module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDFrame
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCMinusFrame

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus
  polar_quadPlus_single_inl polar_quadPlus_single_inr)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

section Vectors

variable (K : Type) [Field K] {r : ℕ} (k : Fin (r + 1))

@[expose] def pdMA : Fin (r + 2) ⊕ Fin (r + 2) → K :=
  Pi.single (Sum.inl k.castSucc) 1 + kOmegaVec K (r + 1)

@[expose] def pdMB : Fin (r + 2) ⊕ Fin (r + 2) → K :=
  Pi.single (Sum.inr k.castSucc) 1 + kOmegaVec K (r + 1)

variable {K}

theorem pdM_polar_vec (z : Fin (r + 2) ⊕ Fin (r + 2) → K) :
    polar (quadPlus (r + 2) K) z (kOmegaVec K (r + 1)) =
      z (Sum.inl (Fin.last (r + 1))) + z (Sum.inr (Fin.last (r + 1))) := by
  rw [kOmegaVec, polar_add_right, polar_quadPlus_single_inl, polar_quadPlus_single_inr, add_comm]

theorem pdM_polar_a (z : Fin (r + 2) ⊕ Fin (r + 2) → K) :
    polar (quadPlus (r + 2) K) z (pdMA K k) =
      z (Sum.inr k.castSucc) +
        (z (Sum.inl (Fin.last (r + 1))) + z (Sum.inr (Fin.last (r + 1)))) := by
  rw [pdMA, polar_add_right, polar_quadPlus_single_inl, pdM_polar_vec]

theorem pdM_polar_b (z : Fin (r + 2) ⊕ Fin (r + 2) → K) :
    polar (quadPlus (r + 2) K) z (pdMB K k) =
      z (Sum.inl k.castSucc) +
        (z (Sum.inl (Fin.last (r + 1))) + z (Sum.inr (Fin.last (r + 1)))) := by
  rw [pdMB, polar_add_right, polar_quadPlus_single_inr, pdM_polar_vec]

theorem pdM_single_quad (j : Fin (r + 2) ⊕ Fin (r + 2)) :
    quadPlus (r + 2) K (Pi.single j 1) = 0 := by
  rw [coe_quadPlus]
  rcases j with j | j <;> simp [StatedQuadPlus, Pi.single_apply]

variable [CharP K 2]

omit [CharP K 2] in
theorem pdM_quad_a : quadPlus (r + 2) K (pdMA K k) = 1 := by
  rw [pdMA, QuadraticMap.map_add (⇑(quadPlus (r + 2) K)), pdM_single_quad, kOmega_quadPlus_vec,
    pdM_polar_vec]
  simp [Fin.castSucc_ne_last]

omit [CharP K 2] in
theorem pdM_quad_b : quadPlus (r + 2) K (pdMB K k) = 1 := by
  rw [pdMB, QuadraticMap.map_add (⇑(quadPlus (r + 2) K)), pdM_single_quad, kOmega_quadPlus_vec,
    pdM_polar_vec]
  simp [Fin.castSucc_ne_last]

theorem pdM_polar_ab : polar (quadPlus (r + 2) K) (pdMA K k) (pdMB K k) = 1 := by
  rw [pdM_polar_b]
  simp [pdMA, kOmegaVec, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

theorem pdM_polar_vec_a : polar (quadPlus (r + 2) K) (kOmegaVec K (r + 1)) (pdMA K k) = 0 := by
  rw [pdM_polar_a]
  simp [kOmegaVec, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

theorem pdM_polar_vec_b : polar (quadPlus (r + 2) K) (kOmegaVec K (r + 1)) (pdMB K k) = 0 := by
  rw [pdM_polar_b]
  simp [kOmegaVec, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

end Vectors

section Plane

variable {K : Type} [Field K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

theorem pcOMProj_mulVec_vec : pcOMProj K k *ᵥ kOmegaVec K (r + 1) = kOmMVec K r := by
  rw [← pcOMMat_mulVec_vec k, Matrix.mulVec_mulVec, pcOMProj_mul_pcOMMat, Matrix.one_mulVec]

theorem pcOMProj_mulVec_a : pcOMProj K k *ᵥ pdMA K k = 0 := by
  rw [pdMA, Matrix.mulVec_add, pcOMProj_mulVec_single_k k _ (Or.inl rfl), pcOMProj_mulVec_vec,
    pd_add_self]

theorem pcOMProj_mulVec_b : pcOMProj K k *ᵥ pdMB K k = 0 := by
  rw [pdMB, Matrix.mulVec_add, pcOMProj_mulVec_single_k k _ (Or.inr rfl), pcOMProj_mulVec_vec,
    pd_add_self]

omit [CharP K 2] in
theorem pdM_cases (m : Fin (r + 2)) :
    m = Fin.last (r + 1) ∨ m = k.castSucc ∨ ∃ i : Fin r, m = (k.succAbove i).castSucc := by
  induction m using Fin.lastCases with
  | last => exact Or.inl rfl
  | cast c =>
    rcases Fin.eq_self_or_eq_succAbove k c with h | ⟨i, h⟩
    · exact Or.inr (Or.inl (h ▸ rfl))
    · exact Or.inr (Or.inr ⟨i, h ▸ rfl⟩)

theorem pdM_ker {z : Fin (r + 2) ⊕ Fin (r + 2) → K} (hz : pcOMProj K k *ᵥ z = 0) :
    z = z (Sum.inl k.castSucc) • pdMA K k + z (Sum.inr k.castSucc) • pdMB K k := by
  have h1 : ∀ i : Fin r, z (Sum.inl (k.succAbove i).castSucc) = 0 := fun i => by
    rw [← pcOMProj_mulVec_inl k z i, hz, Pi.zero_apply]
  have h2 : ∀ i : Fin r, z (Sum.inr (k.succAbove i).castSucc) = 0 := fun i => by
    rw [← pcOMProj_mulVec_inr k z i, hz, Pi.zero_apply]
  have hu : z (Sum.inr (Fin.last (r + 1))) + z (Sum.inl k.castSucc) +
      z (Sum.inr k.castSucc) = 0 := by
    rw [← pcOMProj_mulVec_u k z, hz, Pi.zero_apply]
  have hw : z (Sum.inl (Fin.last (r + 1))) + z (Sum.inr (Fin.last (r + 1))) = 0 := by
    rw [← pcOMProj_mulVec_w k z, hz, Pi.zero_apply]
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hN1 : z (Sum.inr (Fin.last (r + 1))) = z (Sum.inl k.castSucc) + z (Sum.inr k.castSucc) := by
    linear_combination hu - (z (Sum.inl k.castSucc) + z (Sum.inr k.castSucc)) * h22
  have hN2 : z (Sum.inl (Fin.last (r + 1))) = z (Sum.inl k.castSucc) + z (Sum.inr k.castSucc) := by
    rw [← hN1]
    linear_combination hw - z (Sum.inr (Fin.last (r + 1))) * h22
  have hne : ∀ i : Fin r, (k.succAbove i).castSucc ≠ k.castSucc := pcOM_sig_ne k
  have hne' : ∀ i : Fin r, (k.succAbove i).castSucc ≠ Fin.last (r + 1) := pcOM_sig_ne_last k
  have hkN : k.castSucc ≠ Fin.last (r + 1) := Fin.castSucc_ne_last k
  funext j
  rcases j with m | m <;> rcases pdM_cases k m with rfl | rfl | ⟨i, rfl⟩ <;>
    simp [pdMA, pdMB, kOmegaVec, hne, hne', hkN, hkN.symm, h1, h2, hN1, hN2]

theorem pcOM_quad' (x : Fin (r + 2) ⊕ Fin (r + 2) → K)
    (y : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2 → K) :
    quadPlus (r + 2) K (x + pcOMMat K k *ᵥ y) - quadPlus (r + 2) K x =
      quadMinus (r + 1) K 1 1 (pcOMProj K k *ᵥ x + y) -
        quadMinus (r + 1) K 1 1 (pcOMProj K k *ᵥ x) := by
  rw [coe_quadPlus, coe_quadMinus]
  exact pcOM_quad k x y

theorem isPDFramePlane_pcOM :
    IsPDFramePlane (pcOMMat K k) (pcOMProj K k) (quadPlus (r + 2) K) (quadMinus (r + 1) K 1 1)
      (pdMA K k) (pdMB K k) :=
  ⟨pcOMProj_mul_pcOMMat k, pcOM_quad' k, pcOMProj_mulVec_a k, pcOMProj_mulVec_b k,
    fun _ hz => ⟨_, _, pdM_ker k hz⟩, pdM_quad_a k, pdM_quad_b k, pdM_polar_ab k⟩

end Plane

section Singular

theorem pd_exists_totallySingular_quadPlus {n : ℕ} (hn : 3 ≤ n) (K : Type) [Field K] :
    ∃ T : Submodule K (Fin n ⊕ Fin n → K), finrank K T = 3 ∧ ∀ x ∈ T, quadPlus n K x = 0 := by
  refine pd_exists_totallySingular_of _ (fun k => .inl (Fin.castLE hn k))
    (fun a b h => Fin.castLE_injective hn (Sum.inl_injective h)) fun v hv => ?_
  rw [coe_quadPlus, StatedQuadPlus]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hv (.inr i) (by rintro ⟨k, hk⟩; exact Sum.inl_ne_inr hk), mul_zero]

theorem pd_exists_totallySingular_quadMinus {n : ℕ} (hn : 4 ≤ n) (K : Type) [Field K] (b c : K) :
    ∃ T : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      finrank K T = 3 ∧ ∀ x ∈ T, quadMinus n K b c x = 0 := by
  have hn' : 3 ≤ n - 1 := by omega
  refine pd_exists_totallySingular_of _ (fun k => .inl (Fin.castLE hn' k))
    (fun a b h => Fin.castLE_injective hn' (Sum.inl_injective h)) fun v hv => ?_
  rw [coe_quadMinus, StatedQuadMinus]
  have h1 : ∀ k : Fin (n - 1) ⊕ Fin 2, v (.inr k) = 0 := fun k =>
    hv (.inr k) (by rintro ⟨j, hj⟩; exact Sum.inl_ne_inr hj)
  simp [h1]

end Singular

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

theorem pdM_rot_mem (hr : 2 ≤ r) :
    pdRotGL (pdM_polar_ab k) ∈ StatedOmega (StatedQuadPlus (r + 2) K) := by
  have h := pdRotGL_mem_statedOmega (pdM_quad_a k) (pdM_quad_b k) (pdM_polar_ab k)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (r + 2) K)
    (pd_exists_totallySingular_quadPlus (by omega) K)
  rwa [coe_quadPlus] at h

@[expose] noncomputable def pdMRot (hr : 2 ≤ r) : StatedOmega (StatedQuadPlus (r + 2) K) :=
  ⟨pdRotGL (pdM_polar_ab k), pdM_rot_mem k hr⟩

theorem coe_pdMRot (hr : 2 ≤ r) :
    (((pdMRot k hr : StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
      Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) =
        pdRotMat (quadPlus (r + 2) K) (pdMA K k) (pdMB K k) := rfl

theorem pcOMExt_range_le_centralizer (hr : 2 ≤ r) :
    (pcOMExt (K := K) k).range ≤ centralizer {pdMRot k hr} := by
  rintro _ ⟨h, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_pcOMExt, coe_pdMRot]
  exact ((isPDFramePlane_pcOM k).rot_commute _).symm

theorem mem_pcOMExt_range_iff (hK : Nat.card K = 2) (hr : 3 ≤ r)
    (g : StatedOmega (StatedQuadPlus (r + 2) K)) :
    g ∈ (pcOMExt (K := K) k).range ↔
      ((g : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMA K k = pdMA K k ∧
      ((g : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMB K k = pdMB K k := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [coe_pcOMExt]
    exact (isPDFramePlane_pcOM k).ext_fix _
  · rintro ⟨ha, hb⟩
    have hg : (g : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) ∈ StatedOmega ⇑(quadPlus (r + 2) K) := by
      rw [coe_quadPlus]
      exact g.2
    obtain ⟨h, hh, he⟩ := (isPDFramePlane_pcOM k).exists_eq_of_fix
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (r + 2) K)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (r + 1) K
        (q2Omega_irreducible_one_one hK))
      (pd_exists_totallySingular_quadMinus (by omega) K 1 1) hg ha hb
    rw [coe_quadMinus] at hh
    exact ⟨⟨h, hh⟩, Subtype.ext (Units.ext he)⟩

theorem le_pcOMExt_range_of_perfect (hK : Nat.card K = 2) (hr : 3 ≤ r)
    {P : Subgroup (StatedOmega (StatedQuadPlus (r + 2) K))} (hP : ⁅P, P⁆ = P)
    (hPc : P ≤ centralizer {pdMRot k (by omega)}) : P ≤ (pcOMExt (K := K) k).range := by
  intro g hg
  have h := (isPDFramePlane_pcOM k).fix_of_perfect hP (pdM_rot_mem k (by omega)) hPc hg
  exact (mem_pcOMExt_range_iff k hK hr g).2 h

theorem q2OmIota_nsElt_eq (hK : Nat.card K = 2) (hr : 3 ≤ r) :
    q2OmIota (r := r + 1) (by omega) hK (by omega) (nsElt k) = pdMRot k (by omega) := by
  have hA : pdMRot k (by omega) ∈ fixedSubgroup (kOmegaBetaC K (r + 1)) := by
    rw [mem_fixedSubgroup_kOmegaBetaC_iff K (by omega), coe_pdMRot]
    exact pdRotMat_mulVec_of_polar (pdM_polar_vec_a k) (pdM_polar_vec_b k)
  have hres : kOmegaFixRes K (by omega : 2 ≤ r + 1) ⟨_, hA⟩ = nsElt k := by
    apply mat_injective
    rw [mat_apply, coe_kOmegaFixRes, mat_nsElt]
    ext a' b'
    rw [Matrix.submatrix_apply]
    change pdRotMat (quadPlus (r + 2) K) (pdMA K k) (pdMB K k) (kOmegaEmb (r + 1) a')
      (kOmegaEmb (r + 1) b') = _
    have hcol : pdRotMat (quadPlus (r + 2) K) (pdMA K k) (pdMB K k) (kOmegaEmb (r + 1) a')
        (kOmegaEmb (r + 1) b') = (pdRotMat (quadPlus (r + 2) K) (pdMA K k) (pdMB K k) *ᵥ
          Pi.single (kOmegaEmb (r + 1) b') 1) (kOmegaEmb (r + 1) a') := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hcol, pdRotMat_mulVec, pdM_polar_a, pdM_polar_b]
    clear hcol
    rcases a' with i | i <;> rcases b' with j | j <;>
      simp [kOmegaEmb, pdMA, pdMB, kOmegaVec, Pi.single_apply, CFSG.LieType.Steinberg.Sp.blockMat,
        zThreeMat, Fin.castSucc_ne_last, Matrix.one_apply, CharTwo.neg_eq] <;>
      by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp_all [Pi.single_apply, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero, eq_comm]
  have hι : q2OmIota (r := r + 1) (by omega) hK (by omega)
      (kOmegaFixRes K (by omega : 2 ≤ r + 1) ⟨_, hA⟩) = pdMRot k (by omega) := by
    have h := (MulEquiv.ofBijective (kOmegaFixRes K (by omega : 2 ≤ r + 1))
      (kOmegaFixRes_bijective_two K (by omega) hK (by omega))).symm_apply_apply ⟨_, hA⟩
    exact congrArg Subtype.val h
  rw [← hres, hι]

end Levi

section Beta

variable {K : Type} [Field K] [CharP K 2] {r : ℕ} (k : Fin (r + 1))

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (plusIndexEquiv minusIndexEquiv)

theorem pcOMExt_kOmMBetaC (a : StatedOmega (StatedQuadMinus (r + 1) K 1 1)) :
    pcOMExt k (kOmMBetaC K r 1 1 a) = kOmegaBetaC K (r + 1) (pcOMExt k a) := by
  have h1 : ((kOmMBetaC K r 1 1 a : StatedOmega (StatedQuadMinus (r + 1) K 1 1)) :
      GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) =
      pdSym (quadMinus (r + 1) K 1 1) (kOmMVec K r) * (a : GL _ K) *
        pdSym (quadMinus (r + 1) K 1 1) (kOmMVec K r) :=
    pd_coe_omegaSymmetryAut _ (quadMinus (r + 1) K 1 1) (coe_quadMinus (r + 1) K 1 1)
      (kOmM_matrixDerivedScalars_eq_bot K r 1 1) (kOmM_quadMinus_vec K r) a
  have h2 : ((kOmegaBetaC K (r + 1) (pcOMExt k a) : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) =
      pdSym (quadPlus (r + 2) K) (kOmegaVec K (r + 1)) * (pcOMExt k a : GL _ K) *
        pdSym (quadPlus (r + 2) K) (kOmegaVec K (r + 1)) :=
    pd_coe_omegaSymmetryAut _ (quadPlus (r + 2) K) (coe_quadPlus (r + 2) K)
      (kOmega_matrixDerivedScalars_eq_bot K (r + 1)) (kOmega_quadPlus_vec K (r + 1)) _
  apply Subtype.ext
  apply Units.ext
  rw [h2, coe_pcOMExt, h1, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    coe_pcOMExt]
  exact pcExtMat_sym_conj (pcOMProj_mul_pcOMMat k) (pcOM_quad' k) (pcOMMat_mulVec_vec k)
    (kOmM_quadMinus_vec K r) (kOmega_quadPlus_vec K (r + 1)) _

end Beta

section Triple

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

@[expose] def pdMP (j : Fin (r + 1)) : Fin (r + 2) ⊕ Fin (r + 2) → K :=
  Pi.single (Sum.inl j.castSucc) 1 + Pi.single (Sum.inr j.castSucc) 1

@[expose] def pdMW (o k l : Fin (r + 1)) : Fin (r + 2) ⊕ Fin (r + 2) → K :=
  Pi.single (Sum.inl (Fin.last (r + 1))) 1 + (pdMP o + pdMP k + pdMP l)

variable {o k l : Fin (r + 1)}

omit [CharP K 2] in
theorem pdMW_apply_inl_last : pdMW (K := K) o k l (Sum.inl (Fin.last (r + 1))) = 1 := by
  simp [pdMW, pdMP, Fin.castSucc_ne_last]

omit [CharP K 2] in
theorem pdMW_apply_inr_last : pdMW (K := K) o k l (Sum.inr (Fin.last (r + 1))) = 0 := by
  simp [pdMW, pdMP, Fin.castSucc_ne_last]

omit [CharP K 2] in
theorem pdMW_apply_inl (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) {j : Fin (r + 1)}
    (hj : j = o ∨ j = k ∨ j = l) : pdMW (K := K) o k l (Sum.inl j.castSucc) = 1 := by
  rcases hj with rfl | rfl | rfl <;>
    simp [pdMW, pdMP, Fin.castSucc_ne_last, hok, hol, hkl, Ne.symm hok,
      Ne.symm hol, Ne.symm hkl]

omit [CharP K 2] in
theorem pdMW_apply_inr (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) {j : Fin (r + 1)}
    (hj : j = o ∨ j = k ∨ j = l) : pdMW (K := K) o k l (Sum.inr j.castSucc) = 1 := by
  rcases hj with rfl | rfl | rfl <;>
    simp [pdMW, pdMP, hok, hol, hkl, Ne.symm hok,
      Ne.symm hol, Ne.symm hkl]

theorem pdMW_polar_a (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) {j : Fin (r + 1)}
    (hj : j = o ∨ j = k ∨ j = l) :
    polar (quadPlus (r + 2) K) (pdMW o k l) (pdMA K j) = 0 := by
  rw [pdM_polar_a, pdMW_apply_inr hok hol hkl hj, pdMW_apply_inl_last, pdMW_apply_inr_last,
    add_zero, CharTwo.add_self_eq_zero]

theorem pdMW_polar_b (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) {j : Fin (r + 1)}
    (hj : j = o ∨ j = k ∨ j = l) :
    polar (quadPlus (r + 2) K) (pdMW o k l) (pdMB K j) = 0 := by
  rw [pdM_polar_b, pdMW_apply_inl hok hol hkl hj, pdMW_apply_inl_last, pdMW_apply_inr_last,
    add_zero, CharTwo.add_self_eq_zero]

omit [CharP K 2] in
theorem pdMW_polar_vec : polar (quadPlus (r + 2) K) (kOmegaVec K (r + 1)) (pdMW o k l) = 1 := by
  rw [polar_comm, pdM_polar_vec, pdMW_apply_inl_last, pdMW_apply_inr_last, add_zero]

omit [CharP K 2] in
theorem pdMP_quad (j : Fin (r + 1)) : quadPlus (r + 2) K (pdMP j) = 1 := by
  rw [pdMP, QuadraticMap.map_add (⇑(quadPlus (r + 2) K)), pdM_single_quad, pdM_single_quad,
    polar_quadPlus_single_inr]
  simp

omit [CharP K 2] in
theorem pdMP_polar (j j' : Fin (r + 1)) (h : j ≠ j') :
    polar (quadPlus (r + 2) K) (pdMP j) (pdMP j') = 0 := by
  rw [show (pdMP j' : Fin (r + 2) ⊕ Fin (r + 2) → K) = Pi.single (Sum.inl j'.castSucc) 1 +
    Pi.single (Sum.inr j'.castSucc) 1 from rfl, polar_add_right, polar_quadPlus_single_inl,
    polar_quadPlus_single_inr]
  simp [pdMP, Ne.symm h]

theorem pdMW_quad (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) :
    quadPlus (r + 2) K (pdMW o k l) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 : polar (quadPlus (r + 2) K) (Pi.single (Sum.inl (Fin.last (r + 1))) 1)
      (pdMP o + pdMP k + pdMP l) = 0 := by
    rw [polar_comm, polar_quadPlus_single_inl]
    simp [pdMP, Fin.castSucc_ne_last]
  rw [pdMW, QuadraticMap.map_add (⇑(quadPlus (r + 2) K)), pdM_single_quad, e1,
    QuadraticMap.map_add (⇑(quadPlus (r + 2) K)), QuadraticMap.map_add (⇑(quadPlus (r + 2) K)),
    pdMP_quad, pdMP_quad, pdMP_quad, pdMP_polar o k hok, polar_add_left, pdMP_polar o l hol,
    pdMP_polar k l hkl]
  linear_combination h2

variable [Finite K]

theorem exists_triple_pcOMExt (hK : Nat.card K = 2) (hr : 3 ≤ r) (hok : o ≠ k) (hol : o ≠ l)
    (hkl : k ≠ l) :
    ∃ a b c : StatedOmega (StatedQuadMinus (r + 1) K 1 1), pcOMExt o a = pcOMExt k b ∧
      pcOMExt o a = pcOMExt l c ∧ kOmegaBetaC K (r + 1) (pcOMExt o a) ≠ pcOMExt o a := by
  have hv : quadPlus (r + 2) K (kOmegaVec K (r + 1)) = 1 := kOmega_quadPlus_vec K (r + 1)
  have hw : quadPlus (r + 2) K (pdMW o k l) = 1 := pdMW_quad hok hol hkl
  have hvw : polar (quadPlus (r + 2) K) (kOmegaVec K (r + 1)) (pdMW o k l) = 1 := pdMW_polar_vec
  have hmem : pdRotGL hvw ∈ StatedOmega (StatedQuadPlus (r + 2) K) := by
    have h := pdRotGL_mem_statedOmega hv hw hvw
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (r + 2) K)
      (pd_exists_totallySingular_quadPlus (by omega) K)
    rwa [coe_quadPlus] at h
  set g : StatedOmega (StatedQuadPlus (r + 2) K) := ⟨pdRotGL hvw, hmem⟩ with hg
  have hfix : ∀ j, (j = o ∨ j = k ∨ j = l) → g ∈ (pcOMExt (K := K) j).range := by
    intro j hj
    rw [mem_pcOMExt_range_iff j hK hr]
    refine ⟨pdRotMat_mulVec_of_polar ?_ ?_, pdRotMat_mulVec_of_polar ?_ ?_⟩
    · rw [polar_comm]
      exact pdM_polar_vec_a j
    · rw [polar_comm]
      exact pdMW_polar_a hok hol hkl hj
    · rw [polar_comm]
      exact pdM_polar_vec_b j
    · rw [polar_comm]
      exact pdMW_polar_b hok hol hkl hj
  obtain ⟨a, ha⟩ := hfix o (Or.inl rfl)
  obtain ⟨b, hb⟩ := hfix k (Or.inr (Or.inl rfl))
  obtain ⟨c, hc⟩ := hfix l (Or.inr (Or.inr rfl))
  refine ⟨a, b, c, ha.trans hb.symm, ha.trans hc.symm, ?_⟩
  rw [ha]
  intro h
  have h1 : g ∈ fixedSubgroup (kOmegaBetaC K (r + 1)) := h
  rw [mem_fixedSubgroup_kOmegaBetaC_iff K (by omega)] at h1
  have h2 : pdRotMat (quadPlus (r + 2) K) (kOmegaVec K (r + 1)) (pdMW o k l) *ᵥ
      kOmegaVec K (r + 1) = pdMW o k l := pdRotMat_mulVec_a hvw
  have h3 := congrFun (h2.symm.trans h1) (Sum.inr (Fin.last (r + 1)))
  rw [pdMW_apply_inr_last] at h3
  simp [kOmegaVec] at h3

end Triple

end CFSG.SeitzReduction.SymplecticPilot
