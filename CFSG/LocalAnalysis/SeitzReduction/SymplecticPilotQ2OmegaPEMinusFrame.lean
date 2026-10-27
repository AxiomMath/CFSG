module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPESpin
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDMinus
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

@[expose] def peMU (i : Fin (r + 1)) : Fin (r + 2) ⊕ Fin (r + 2) → K :=
  pdMP (K := K) i + kOmegaVec K (r + 1)

variable {K}

theorem pe_polar_pdMP (z : Fin (r + 2) ⊕ Fin (r + 2) → K) (j : Fin (r + 1)) :
    polar (quadPlus (r + 2) K) z (pdMP j) = z (.inr j.castSucc) + z (.inl j.castSucc) := by
  rw [show (pdMP j : Fin (r + 2) ⊕ Fin (r + 2) → K) = Pi.single (Sum.inl j.castSucc) 1 +
    Pi.single (Sum.inr j.castSucc) 1 from rfl, polar_add_right, polar_quadPlus_single_inl,
    polar_quadPlus_single_inr]

theorem pe_polar_peMU (z : Fin (r + 2) ⊕ Fin (r + 2) → K) (i : Fin (r + 1)) :
    polar (quadPlus (r + 2) K) z (peMU K i) =
      z (.inr i.castSucc) + z (.inl i.castSucc) +
        (z (.inl (Fin.last (r + 1))) + z (.inr (Fin.last (r + 1)))) := by
  rw [peMU, polar_add_right, pe_polar_pdMP, pdM_polar_vec]

theorem pdMP_apply_inl (i j : Fin (r + 1)) :
    (pdMP i : Fin (r + 2) ⊕ Fin (r + 2) → K) (.inl j.castSucc) = if j = i then 1 else 0 := by
  simp [pdMP, Pi.single_apply]

theorem pdMP_apply_inr (i j : Fin (r + 1)) :
    (pdMP i : Fin (r + 2) ⊕ Fin (r + 2) → K) (.inr j.castSucc) = if j = i then 1 else 0 := by
  simp [pdMP, Pi.single_apply]

theorem pdMP_apply_inl_last (i : Fin (r + 1)) :
    (pdMP i : Fin (r + 2) ⊕ Fin (r + 2) → K) (.inl (Fin.last (r + 1))) = 0 := by
  simp [pdMP, (Fin.castSucc_ne_last i).symm]

theorem pdMP_apply_inr_last (i : Fin (r + 1)) :
    (pdMP i : Fin (r + 2) ⊕ Fin (r + 2) → K) (.inr (Fin.last (r + 1))) = 0 := by
  simp [pdMP, (Fin.castSucc_ne_last i).symm]

variable [CharP K 2]

theorem pe_quad_peMU (i : Fin (r + 1)) : quadPlus (r + 2) K (peMU K i) = 0 := by
  rw [peMU, QuadraticMap.map_add (⇑(quadPlus (r + 2) K)), pdMP_quad, kOmega_quadPlus_vec,
    pdM_polar_vec, pdMP_apply_inl_last, pdMP_apply_inr_last, add_zero, add_zero,
    CharTwo.add_self_eq_zero]

theorem pe_polar_peMU_peMU {i j : Fin (r + 1)} (hij : i ≠ j) :
    polar (quadPlus (r + 2) K) (peMU K i) (peMU K j) = 0 := by
  rw [pe_polar_peMU]
  simp [peMU, kOmegaVec, pdMP_apply_inl, pdMP_apply_inr, Ne.symm hij, Fin.castSucc_ne_last,
    pdMP_apply_inl_last, pdMP_apply_inr_last, CharTwo.add_self_eq_zero]

omit [CharP K 2] in
theorem pe_polar_peMU_pdMP {i m : Fin (r + 1)} (him : i ≠ m) :
    polar (quadPlus (r + 2) K) (peMU K i) (pdMP m) = 0 := by
  rw [pe_polar_pdMP]
  simp [peMU, kOmegaVec, pdMP_apply_inl, pdMP_apply_inr, Ne.symm him, Fin.castSucc_ne_last]

theorem pe_polar_vec_peMU (i : Fin (r + 1)) :
    polar (quadPlus (r + 2) K) (kOmegaVec K (r + 1)) (peMU K i) = 0 := by
  rw [pe_polar_peMU]
  simp [kOmegaVec, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

theorem pe_polar_pdMA_peMU {k i : Fin (r + 1)} (hki : k ≠ i) :
    polar (quadPlus (r + 2) K) (pdMA K k) (peMU K i) = 0 := by
  rw [pe_polar_peMU]
  simp [pdMA, kOmegaVec, Fin.castSucc_ne_last, Ne.symm hki, CharTwo.add_self_eq_zero]

theorem pe_polar_pdMB_peMU {k i : Fin (r + 1)} (hki : k ≠ i) :
    polar (quadPlus (r + 2) K) (pdMB K k) (peMU K i) = 0 := by
  rw [pe_polar_peMU]
  simp [pdMB, kOmegaVec, Fin.castSucc_ne_last, Ne.symm hki, CharTwo.add_self_eq_zero]

theorem pe_polar_pdMA_peMU_self (i : Fin (r + 1)) :
    polar (quadPlus (r + 2) K) (pdMA K i) (peMU K i) = 1 := by
  rw [pe_polar_peMU]
  simp [pdMA, kOmegaVec, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

theorem pe_polar_pdMB_peMU_self (i : Fin (r + 1)) :
    polar (quadPlus (r + 2) K) (pdMB K i) (peMU K i) = 1 := by
  rw [pe_polar_peMU]
  simp [pdMB, kOmegaVec, Fin.castSucc_ne_last, CharTwo.add_self_eq_zero]

end Vectors

section Transporter

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

@[expose] noncomputable def peMEichSpin {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m)
    (hjm : j ≠ m) : spinGroup (quadPlus (r + 2) K) :=
  peEich (pe_quad_peMU i) (pe_polar_peMU_peMU hij) (pe_polar_peMU_pdMP him)
    (pe_polar_peMU_pdMP hjm) (by rw [pdMP_quad]; exact isUnit_one)

@[expose] noncomputable def peMEich (hr : 1 ≤ r) {i j m : Fin (r + 1)} (hij : i ≠ j)
    (him : i ≠ m) (hjm : j ≠ m) : StatedOmega (StatedQuadPlus (r + 2) K) :=
  peRho (n := r + 2) (by omega) (peMEichSpin hij him hjm)

variable (hr : 1 ≤ r) {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m)

theorem peMEich_mulVec (z : Fin (r + 2) ⊕ Fin (r + 2) → K) :
    (((peMEich hr hij him hjm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ z =
      z + polar (quadPlus (r + 2) K) z (peMU K i) • peMU K j -
        polar (quadPlus (r + 2) K) z (peMU K j) • peMU K i := by
  rw [peMEich, peRho_mulVec, peMEichSpin, spinAction_peEich _ (pe_quad_peMU j)]

theorem peMEich_mulVec_of_polar {z : Fin (r + 2) ⊕ Fin (r + 2) → K}
    (h1 : polar (quadPlus (r + 2) K) z (peMU K i) = 0)
    (h2 : polar (quadPlus (r + 2) K) z (peMU K j) = 0) :
    (((peMEich hr hij him hjm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ z = z := by
  rw [peMEich_mulVec, h1, h2, zero_smul, zero_smul, add_zero, sub_zero]

theorem peMEich_mem_fixedSubgroup :
    peMEich hr hij him hjm ∈ fixedSubgroup (kOmegaBetaC K (r + 1)) := by
  rw [mem_fixedSubgroup_kOmegaBetaC_iff K (by omega)]
  exact peMEich_mulVec_of_polar hr hij him hjm (pe_polar_vec_peMU i) (pe_polar_vec_peMU j)

theorem peMEich_mem_range [Finite K] (hK : Nat.card K = 2) (hr3 : 3 ≤ r) {k : Fin (r + 1)}
    (hki : k ≠ i) (hkj : k ≠ j) : peMEich hr hij him hjm ∈ (pcOMExt (K := K) k).range :=
  (mem_pcOMExt_range_iff k hK hr3 _).2
    ⟨peMEich_mulVec_of_polar hr hij him hjm (pe_polar_pdMA_peMU hki) (pe_polar_pdMA_peMU hkj),
      peMEich_mulVec_of_polar hr hij him hjm (pe_polar_pdMB_peMU hki) (pe_polar_pdMB_peMU hkj)⟩

theorem peMEich_mulVec_a :
    (((peMEich hr hij him hjm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMA K i =
      Pi.single (.inl i.castSucc) 1 + pdMP j := by
  rw [peMEich_mulVec, pe_polar_pdMA_peMU_self, pe_polar_pdMA_peMU (Ne.symm hij).symm, one_smul,
    zero_smul, sub_zero, pdMA, peMU]
  rw [show ∀ x y z : Fin (r + 2) ⊕ Fin (r + 2) → K, x + y + (z + y) = x + z by
    intro x y z; rw [add_add_add_comm, pd_add_self, add_zero]]

theorem peMEich_mulVec_b :
    (((peMEich hr hij him hjm : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMB K i =
      Pi.single (.inr i.castSucc) 1 + pdMP j := by
  rw [peMEich_mulVec, pe_polar_pdMB_peMU_self, pe_polar_pdMB_peMU (Ne.symm hij).symm, one_smul,
    zero_smul, sub_zero, pdMB, peMU]
  rw [show ∀ x y z : Fin (r + 2) ⊕ Fin (r + 2) → K, x + y + (z + y) = x + z by
    intro x y z; rw [add_add_add_comm, pd_add_self, add_zero]]

end Transporter

section Iota

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2) (hr3 : 3 ≤ r)
include hK hr3

theorem pe_q2OmIota_kOmegaFixRes (A : StatedOmega (StatedQuadPlus (r + 2) K))
    (hA : A ∈ fixedSubgroup (kOmegaBetaC K (r + 1))) :
    q2OmIota (r := r + 1) (by omega) hK (by omega)
      (kOmegaFixRes K (by omega : 2 ≤ r + 1) ⟨A, hA⟩) = A := by
  have h := (MulEquiv.ofBijective (kOmegaFixRes K (by omega : 2 ≤ r + 1))
    (kOmegaFixRes_bijective_two K (by omega) hK (by omega))).symm_apply_apply ⟨A, hA⟩
  exact congrArg Subtype.val h

omit hK in
@[expose] noncomputable def peMTr {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m)
    (hjm : j ≠ m) : StatedSp (r + 1) K :=
  kOmegaFixRes K (by omega : 2 ≤ r + 1)
    ⟨peMEich (by omega) hij him hjm, peMEich_mem_fixedSubgroup (by omega) hij him hjm⟩

theorem q2OmIota_peMTr {i j m : Fin (r + 1)} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m) :
    q2OmIota (r := r + 1) (by omega) hK (by omega) (peMTr hr3 hij him hjm) =
      peMEich (by omega) hij him hjm :=
  pe_q2OmIota_kOmegaFixRes hK hr3 _ _

theorem pe_mem_complSp_of_mem_range {k : Fin (r + 1)} {y : StatedSp (r + 1) K}
    (hy : q2OmIota (r := r + 1) (by omega) hK (by omega) y ∈ (pcOMExt (K := K) k).range) :
    y ∈ complSp K k := by
  obtain ⟨ha, hb⟩ := (mem_pcOMExt_range_iff k hK hr3 _).1 hy
  have hfix : q2OmIota (r := r + 1) (by omega) hK (by omega) y ∈
      fixedSubgroup (kOmegaBetaC K (r + 1)) := by
    rw [← range_q2OmIota (r := r + 1) (by omega) hK (by omega)]
    exact ⟨y, rfl⟩
  have hv := (mem_fixedSubgroup_kOmegaBetaC_iff K (by omega) _).1 hfix
  have he : (((q2OmIota (r := r + 1) (by omega) hK (by omega) y :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          Pi.single (Sum.inl k.castSucc) 1 = Pi.single (Sum.inl k.castSucc) 1 := by
    rw [pdMA, Matrix.mulVec_add, hv] at ha
    exact add_right_cancel ha
  have hf : (((q2OmIota (r := r + 1) (by omega) hK (by omega) y :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ
          Pi.single (Sum.inr k.castSucc) 1 = Pi.single (Sum.inr k.castSucc) 1 := by
    rw [pdMB, Matrix.mulVec_add, hv] at hb
    exact add_right_cancel hb
  obtain ⟨z, hz1, hz2⟩ := kOmegaFixRes_q2OmIota (r := r + 1) (by omega) hK (by omega) y
  rw [complSp, mem_suppGroup_iff (parClosed_coords k).compl]
  intro t ht r'
  have ht' : t ∈ CFSG.ClassicalInvolution.Models.SymplecticPairs.coords k := by simpa using ht
  rw [← hz2, mat_apply, coe_kOmegaFixRes, hz1, Matrix.submatrix_apply]
  have hcol : ∀ c : Fin (r + 2) ⊕ Fin (r + 2),
      (((q2OmIota (r := r + 1) (by omega) hK (by omega) y :
        StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
          Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) c
          (kOmegaEmb (r + 1) t) = (Pi.single (kOmegaEmb (r + 1) t) 1 : _ → K) c := by
    intro c
    rcases mem_coords.1 ht' with rfl | rfl
    · have h := congrFun he c
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
      exact h
    · have h := congrFun hf c
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
      exact h
  rw [hcol, Pi.single_apply, Matrix.one_apply]
  simp only [(kOmegaEmb_injective (r := r + 1)).eq_iff]

end Iota

section Family

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ} {e : L ≃* StatedSp (r + 1) K}

@[expose] noncomputable def peMPhi (Φ : ∀ k : Fin (r + 1),
    StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))) (k : Fin (r + 1)) :
    StatedOmega (StatedQuadMinus (r + 1) K 1 1) →* G :=
  (centralizerPerfectCore (modelToG e (nsTorusSp K k))).subtype.comp (Φ k).toMonoidHom

omit [Finite K] [CharP K 2] in
theorem peMPhi_apply {Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))} (k : Fin (r + 1))
    (g : StatedOmega (StatedQuadMinus (r + 1) K 1 1)) :
    peMPhi Φ k g = ((Φ k g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) := rfl

omit [Finite K] in
theorem peAligned_minus {Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))} (hal : NsOmMinusAligned e Φ) :
    PEAligned (fun k => pcOMExt (K := K) k) (peMPhi Φ) :=
  fun k l g h hgh => hal k l g h hgh

theorem peNormal_minus (hK : Nat.card K = 2) (hr3 : 3 ≤ r) {t : G}
    {Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    (hΦ : ∀ k, IsNsOmMinusParam hK hr3 e t k (Φ k)) :
    PENormal (fun k => pcOMExt (K := K) k) (peMPhi Φ)
      (q2OmIota (r := r + 1) (by omega) hK (by omega)) (L.subtype.comp e.symm.toMonoidHom) := by
  intro k g y hg
  have hy := pe_mem_complSp_of_mem_range hK hr3 (k := k) (y := y) ⟨g, hg⟩
  exact (hΦ k).coe_eq_of_pcOMExt_eq hy hg

end Family

end CFSG.SeitzReduction.SymplecticPilot
