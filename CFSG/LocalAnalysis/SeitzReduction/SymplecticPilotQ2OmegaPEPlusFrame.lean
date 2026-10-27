module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPESpinM
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDPlus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEAbstract

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (mem_suppGroup_iff parClosed_coords
  mem_coords)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Vectors

variable (K : Type) [Field K] {r : ℕ}

@[expose] def pePU (i : Fin (r + 1)) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K :=
  pdPP (K := K) i + kOmMVec K (r + 1)

variable {K}

theorem pe_polar_pdPP (z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)
    (j : Fin (r + 1)) :
    polar (quadMinus (r + 1 + 1) K 1 1) z (pdPP j) =
      z (Sum.inr (Sum.inl j)) + z (Sum.inl j) := by
  rw [show (pdPP j : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) =
    Pi.single (Sum.inl j : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
      Pi.single (Sum.inr (Sum.inl j) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1
    from rfl, polar_add_right, polar_quadMinus_single_inl, polar_quadMinus_single_inr_inl]

theorem pdPP_apply_plane (i : Fin (r + 1)) (t : Fin 2) :
    (pdPP i : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) (Sum.inr (Sum.inr t)) = 0 := by
  simp [pdPP]

variable [CharP K 2]

theorem pe_polar_pePU (z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K)
    (i : Fin (r + 1)) :
    polar (quadMinus (r + 1 + 1) K 1 1) z (pePU K i) =
      z (Sum.inr (Sum.inl i)) + z (Sum.inl i) + z (Sum.inr (Sum.inr 1)) := by
  rw [pePU, polar_add_right, pe_polar_pdPP, pdP_polar_vec]

theorem pe_quad_pePU (i : Fin (r + 1)) : quadMinus (r + 1 + 1) K 1 1 (pePU K i) = 0 := by
  rw [pePU, QuadraticMap.map_add (⇑(quadMinus (r + 1 + 1) K 1 1)), pdPP_quad, kOmM_quadMinus_vec,
    pdP_polar_vec, pdPP_apply_plane, add_zero, CharTwo.add_self_eq_zero]

theorem pe_polar_pePU_pePU {i j : Fin (r + 1)} (hij : i ≠ j) :
    polar (quadMinus (r + 1 + 1) K 1 1) (pePU K i) (pePU K j) = 0 := by
  rw [pe_polar_pePU]
  simp [pePU, pdPP, kOmMVec, Ne.symm hij]

omit [CharP K 2] in
theorem pe_polar_pePU_pdPP {i m : Fin (r + 1)} (him : i ≠ m) :
    polar (quadMinus (r + 1 + 1) K 1 1) (pePU K i) (pdPP m) = 0 := by
  rw [pe_polar_pdPP]
  simp [pePU, pdPP, kOmMVec, Ne.symm him]

theorem pe_polar_vec_pePU (i : Fin (r + 1)) :
    polar (quadMinus (r + 1 + 1) K 1 1) (kOmMVec K (r + 1)) (pePU K i) = 0 := by
  rw [pe_polar_pePU]
  simp [kOmMVec]

theorem pe_polar_pdPA_pePU {k i : Fin (r + 1)} (hki : k ≠ i) :
    polar (quadMinus (r + 1 + 1) K 1 1) (pdPA K k) (pePU K i) = 0 := by
  rw [pe_polar_pePU]
  simp [pdPA, kOmMVec, Ne.symm hki]

theorem pe_polar_pdPB_pePU {k i : Fin (r + 1)} (hki : k ≠ i) :
    polar (quadMinus (r + 1 + 1) K 1 1) (pdPB K k) (pePU K i) = 0 := by
  rw [pe_polar_pePU]
  simp [pdPB, kOmMVec, Ne.symm hki]

theorem pe_polar_pdPA_pePU_self (i : Fin (r + 1)) :
    polar (quadMinus (r + 1 + 1) K 1 1) (pdPA K i) (pePU K i) = 1 := by
  rw [pe_polar_pePU]
  simp [pdPA, kOmMVec]

theorem pe_polar_pdPB_pePU_self (i : Fin (r + 1)) :
    polar (quadMinus (r + 1 + 1) K 1 1) (pdPB K i) (pePU K i) = 1 := by
  rw [pe_polar_pePU]
  simp [pdPB, kOmMVec]

end Vectors

section Transporter

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2)

@[expose] noncomputable def pePEichSpin {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m)
    (hjm : j ≠ m) : spinGroup (quadMinus (r + 1 + 1) K 1 1) :=
  peEichG (pe_quad_pePU i) (pe_polar_pePU_pePU hij) (pe_polar_pePU_pdPP him)
    (pe_polar_pePU_pdPP hjm) (by rw [pdPP_quad]; exact isUnit_one)

@[expose] noncomputable def pePEich (hr : 2 ≤ r) {i j m : Fin (r + 1)} (hij : i ≠ j)
    (him : i ≠ m) (hjm : j ≠ m) : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1) :=
  peRhoM (n := r + 1 + 1) (by omega) (q2Omega_irreducible_one_one hK) (pePEichSpin hij him hjm)

variable (hr : 2 ≤ r) {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m)

theorem pePEich_mulVec (z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) :
    (((pePEich hK hr hij him hjm : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ z =
      z + polar (quadMinus (r + 1 + 1) K 1 1) z (pePU K i) • pePU K j -
        polar (quadMinus (r + 1 + 1) K 1 1) z (pePU K j) • pePU K i := by
  rw [pePEich, peRhoM_mulVec, pePEichSpin, spinAction_peEichG _ (pe_quad_pePU j)]

theorem pePEich_mulVec_of_polar {z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K}
    (h1 : polar (quadMinus (r + 1 + 1) K 1 1) z (pePU K i) = 0)
    (h2 : polar (quadMinus (r + 1 + 1) K 1 1) z (pePU K j) = 0) :
    (((pePEich hK hr hij him hjm : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ z = z := by
  rw [pePEich_mulVec, h1, h2, zero_smul, zero_smul, add_zero, sub_zero]

theorem pePEich_mem_fixedSubgroup :
    pePEich hK hr hij him hjm ∈ fixedSubgroup (kOmMBetaC K (r + 1) 1 1) := by
  rw [mem_fixedSubgroup_kOmMBetaC_iff K (by omega) (q2Omega_irreducible_one_one hK)]
  exact pePEich_mulVec_of_polar hK hr hij him hjm (pe_polar_vec_pePU i) (pe_polar_vec_pePU j)

theorem pePEich_mem_range {k : Fin (r + 1)} (hki : k ≠ i) (hkj : k ≠ j) :
    pePEich hK hr hij him hjm ∈ (pcOPExt (K := K) k).range :=
  (mem_pcOPExt_range_iff k hK hr _).2
    ⟨pePEich_mulVec_of_polar hK hr hij him hjm (pe_polar_pdPA_pePU hki) (pe_polar_pdPA_pePU hkj),
      pePEich_mulVec_of_polar hK hr hij him hjm (pe_polar_pdPB_pePU hki) (pe_polar_pdPB_pePU hkj)⟩

theorem pePEich_mulVec_a :
    (((pePEich hK hr hij him hjm : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K i =
      Pi.single (Sum.inl i : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP j := by
  rw [pePEich_mulVec, pe_polar_pdPA_pePU_self, pe_polar_pdPA_pePU (Ne.symm hij).symm, one_smul,
    zero_smul, sub_zero, pdPA, pePU]
  rw [show ∀ x y z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K,
    x + y + (z + y) = x + z by intro x y z; rw [add_add_add_comm, pd_add_self, add_zero]]

theorem pePEich_mulVec_b :
    (((pePEich hK hr hij him hjm : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
      GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K i =
      Pi.single (Sum.inr (Sum.inl i) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 +
        pdPP j := by
  rw [pePEich_mulVec, pe_polar_pdPB_pePU_self, pe_polar_pdPB_pePU (Ne.symm hij).symm, one_smul,
    zero_smul, sub_zero, pdPB, pePU]
  rw [show ∀ x y z : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K,
    x + y + (z + y) = x + z by intro x y z; rw [add_add_add_comm, pd_add_self, add_zero]]

end Transporter

section Iota

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2) (hr : 2 ≤ r)
include hK hr

theorem pe_q2OmMIota_kOmMFixRes (A : StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1))
    (hA : A ∈ fixedSubgroup (kOmMBetaC K (r + 1) 1 1)) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
      (kOmMFixRes K (by omega : 3 ≤ r + 1) (q2Omega_irreducible_one_one hK) ⟨A, hA⟩) = A := by
  have h := (MulEquiv.ofBijective (kOmMFixRes K (by omega : 3 ≤ r + 1)
    (q2Omega_irreducible_one_one hK))
    (kOmMFixRes_bijective_two K (by omega) (q2Omega_irreducible_one_one hK) hK)).symm_apply_apply
      ⟨A, hA⟩
  exact congrArg Subtype.val h

@[expose] noncomputable def pePTr {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m)
    (hjm : j ≠ m) : StatedSp (r + 1) K :=
  kOmMFixRes K (by omega : 3 ≤ r + 1) (q2Omega_irreducible_one_one hK)
    ⟨pePEich hK hr hij him hjm, pePEich_mem_fixedSubgroup hK hr hij him hjm⟩

theorem q2OmMIota_pePTr {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m) :
    q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
      (pePTr hK hr hij him hjm) = pePEich hK hr hij him hjm :=
  pe_q2OmMIota_kOmMFixRes hK hr _ _

theorem pe_mem_complSp_of_mem_rangeP {k : Fin (r + 1)} {y : StatedSp (r + 1) K}
    (hy : q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y ∈
      (pcOPExt (K := K) k).range) :
    y ∈ complSp K k := by
  obtain ⟨ha, hb⟩ := (mem_pcOPExt_range_iff k hK hr _).1 hy
  have hfix : q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y ∈
      fixedSubgroup (kOmMBetaC K (r + 1) 1 1) := by
    rw [← range_q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK]
    exact ⟨y, rfl⟩
  have hv := (mem_fixedSubgroup_kOmMBetaC_iff K (by omega) (q2Omega_irreducible_one_one hK) _).1
    hfix
  have he : (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
          Pi.single (Sum.inl k : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 =
        Pi.single (Sum.inl k : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 := by
    rw [pdPA, Matrix.mulVec_add, hv] at ha
    exact add_right_cancel ha
  have hf : (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y :
      StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
        GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
          Pi.single (Sum.inr (Sum.inl k) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 =
        Pi.single (Sum.inr (Sum.inl k) : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) 1 := by
    rw [pdPB, Matrix.mulVec_add, hv] at hb
    exact add_right_cancel hb
  obtain ⟨z, hz1, hz2⟩ := kOmMFixRes_q2OmMIota (r := r + 1) (by omega)
    (q2Omega_irreducible_one_one hK) hK y
  rw [complSp, mem_suppGroup_iff (parClosed_coords k).compl]
  intro t ht r'
  have ht' : t ∈ CFSG.ClassicalInvolution.Models.SymplecticPairs.coords k := by simpa using ht
  rw [← hz2, mat_apply, coe_kOmMFixRes, hz1, Matrix.submatrix_apply]
  have hcol : ∀ c : Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2,
      (((q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y :
        StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
          GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
              (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) c
          (kOmMEmb (r + 1) t) = (Pi.single (kOmMEmb (r + 1) t) 1 : _ → K) c := by
    intro c
    rcases mem_coords.1 ht' with rfl | rfl
    · have h := congrFun he c
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
      exact h
    · have h := congrFun hf c
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
      exact h
  rw [hcol, Pi.single_apply, Matrix.one_apply]
  simp only [(kOmMEmb_injective (r := r + 1)).eq_iff]

end Iota

section Family

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ} {e : L ≃* StatedSp (r + 1) K}

@[expose] noncomputable def pePPhi (Φ : ∀ k : Fin (r + 1),
    StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))) (k : Fin (r + 1)) :
    StatedOmega (StatedQuadPlus (r + 1) K) →* G :=
  (centralizerPerfectCore (modelToG e (nsTorusSp K k))).subtype.comp (Φ k).toMonoidHom

omit [Finite K] [CharP K 2] in
theorem pePPhi_apply {Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadPlus (r + 1) K) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))} (k : Fin (r + 1))
    (g : StatedOmega (StatedQuadPlus (r + 1) K)) :
    pePPhi Φ k g = ((Φ k g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) := rfl

omit [Finite K] in
theorem peAligned_plus {Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadPlus (r + 1) K) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))} (hal : NsOmPlusAligned e Φ) :
    PEAligned (fun k => pcOPExt (K := K) k) (pePPhi Φ) :=
  fun k l g h hgh => hal k l g h hgh

theorem peNormal_plus (hK : Nat.card K = 2) (hr : 2 ≤ r) (hr3 : 3 ≤ r) {t : G}
    {Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    (hΦ : ∀ k, IsNsOmPlusParam hK hr hr3 e t k (Φ k)) :
    PENormal (fun k => pcOPExt (K := K) k) (pePPhi Φ)
      (q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
      (L.subtype.comp e.symm.toMonoidHom) := by
  intro k g y hg
  have hy := pe_mem_complSp_of_mem_rangeP hK hr (k := k) (y := y) ⟨g, hg⟩
  exact (hΦ k).coe_eq_of_pcOPExt_eq hy hg

end Family

end CFSG.SeitzReduction.SymplecticPilot
