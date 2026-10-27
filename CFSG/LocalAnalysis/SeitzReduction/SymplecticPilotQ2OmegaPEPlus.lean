module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEPlusPlace
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Global

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hK : Nat.card K = 2)
  (hn : 4 ≤ r + 1 + 1)

theorem peRhoM_peShortWord (hr : 2 ≤ r) :
    peRhoM hn (q2Omega_irreducible_one_one hK)
        (peShortWord (r + 1 + 1) (q2Omega_irreducible_one_one hK)
          ((Fin.last r : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) =
      pdPRot (Fin.last r) hK hr := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  apply Units.ext
  refine pd_matrix_ext_mulVec fun x => ?_
  rw [peRhoM_mulVec, spinAction_peShortWord, coe_pdPRot, pdRotMat_mulVec, pdP_polar_a,
    pdP_polar_b]
  funext c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pdPA, pdPB, kOmMVec]
  linear_combination -(x (Sum.inl ((Fin.last r : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) +
    x (Sum.inr (Sum.inr 1))) * ((Pi.single (Sum.inr (Sum.inr 0)) (1 : K) :
      Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2 → K) c) * h2

variable {k : Fin (r + 1)} (hk : k.val + 1 < r + 1)
include hk

theorem peRhoM_minusWeyl_mulVec_vec :
    (((peRhoM hn (q2Omega_irreducible_one_one hK)
      (minusWeyl (r + 1 + 1) (q2Omega_irreducible_one_one hK) (k : Fin (r + 1 + 1 - 1))) :
        StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
          GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
              (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ kOmMVec K (r + 1) =
      kOmMVec K (r + 1) := by
  rw [peRhoM_mulVec, kOmMVec, ← pe_planeVec_planeOne,
    spinAction_minusWeyl_planeVec (q2Omega_irreducible_one_one hK)
      (show (k : Fin (r + 1 + 1 - 1)).val + 1 < r + 1 + 1 - 1 by omega) planeOne]

theorem peRhoM_minusWeyl_mulVec_pdPA :
    (((peRhoM hn (q2Omega_irreducible_one_one hK)
      (minusWeyl (r + 1 + 1) (q2Omega_irreducible_one_one hK) (k : Fin (r + 1 + 1 - 1))) :
        StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
          GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
              (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K ⟨k.val + 1, hk⟩ =
      pdPA K k := by
  rw [pdPA, Matrix.mulVec_add, peRhoM_minusWeyl_mulVec_vec hK hn hk, peRhoM_mulVec]
  have h := spinAction_minusWeyl_minusVec (n := r + 1 + 1) (q2Omega_irreducible_one_one hK)
    (show (k : Fin (r + 1 + 1 - 1)).val + 1 < r + 1 + 1 - 1 by omega)
    (((⟨k.val + 1, hk⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) true
  rw [minusVec_true, eVec] at h
  rw [h]
  have hs : Equiv.swap (k : Fin (r + 1 + 1 - 1)) ⟨k.val + 1, by omega⟩
      (((⟨k.val + 1, hk⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) = (k : Fin (r + 1 + 1 - 1)) :=
    Equiv.swap_apply_right _ _
  rw [hs, minusVec_true, eVec, pdPA]

theorem peRhoM_minusWeyl_mulVec_pdPB :
    (((peRhoM hn (q2Omega_irreducible_one_one hK)
      (minusWeyl (r + 1 + 1) (q2Omega_irreducible_one_one hK) (k : Fin (r + 1 + 1 - 1))) :
        StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
          GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
              (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K ⟨k.val + 1, hk⟩ =
      pdPB K k := by
  rw [pdPB, Matrix.mulVec_add, peRhoM_minusWeyl_mulVec_vec hK hn hk, peRhoM_mulVec]
  have h := spinAction_minusWeyl_minusVec (n := r + 1 + 1) (q2Omega_irreducible_one_one hK)
    (show (k : Fin (r + 1 + 1 - 1)).val + 1 < r + 1 + 1 - 1 by omega)
    (((⟨k.val + 1, hk⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) false
  rw [minusVec_false, fVec] at h
  rw [h]
  have hs : Equiv.swap (k : Fin (r + 1 + 1 - 1)) ⟨k.val + 1, by omega⟩
      (((⟨k.val + 1, hk⟩ : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) = (k : Fin (r + 1 + 1 - 1)) :=
    Equiv.swap_apply_right _ _
  rw [hs, minusVec_false, fVec, pdPB]

theorem peRhoM_minusWeyl_mem_fixed :
    peRhoM hn (q2Omega_irreducible_one_one hK)
        (minusWeyl (r + 1 + 1) (q2Omega_irreducible_one_one hK) (k : Fin (r + 1 + 1 - 1))) ∈
      fixedSubgroup (kOmMBetaC K (r + 1) 1 1) := by
  rw [mem_fixedSubgroup_kOmMBetaC_iff K (by omega) (q2Omega_irreducible_one_one hK)]
  exact peRhoM_minusWeyl_mulVec_vec hK hn hk

theorem peRhoM_minusWeyl_mul_pdPRot (hr : 2 ≤ r) :
    peRhoM hn (q2Omega_irreducible_one_one hK)
        (minusWeyl (r + 1 + 1) (q2Omega_irreducible_one_one hK) (k : Fin (r + 1 + 1 - 1))) *
        pdPRot ⟨k.val + 1, hk⟩ hK hr =
      pdPRot k hK hr * peRhoM hn (q2Omega_irreducible_one_one hK)
        (minusWeyl (r + 1 + 1) (q2Omega_irreducible_one_one hK) (k : Fin (r + 1 + 1 - 1))) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_pdPRot, coe_pdPRot]
  have hiso : ∀ z, quadMinus (r + 1 + 1) K 1 1 ((((peRhoM hn (q2Omega_irreducible_one_one hK)
      (minusWeyl (r + 1 + 1) (q2Omega_irreducible_one_one hK) (k : Fin (r + 1 + 1 - 1))) :
        StatedOmega (StatedQuadMinus (r + 1 + 1) K 1 1)) :
          GL (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2)
              (Fin (r + 1 + 1 - 1) ⊕ Fin (r + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ z) =
      quadMinus (r + 1 + 1) K 1 1 z := fun z => by
    rw [coe_quadMinus]
    exact pd_isometry_of_mem_statedOmega (peRhoM hn (q2Omega_irreducible_one_one hK) _).2 z
  rw [pe_mul_pdRotMat hiso, peRhoM_minusWeyl_mulVec_pdPA hK hn hk,
    peRhoM_minusWeyl_mulVec_pdPB hK hn hk]

end Global

section Family

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ} (hK : Nat.card K = 2) (hr : 4 ≤ r) (hn : 4 ≤ r + 1 + 1) {e : L ≃* StatedSp (r + 1) K}
  (Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadPlus (r + 1) K) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k)))

@[expose] noncomputable def pePFamily :
    ∀ J, (minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J →* G :=
  peFamily (minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK))
    (fun k => pcOPExt (K := K) k) (pePPhi Φ)
    (q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
    (L.subtype.comp e.symm.toMonoidHom) (peRhoM hn (q2Omega_irreducible_one_one hK))
    (fun J => pePIdx hr J.1) (fun J => pePTrJ hr hK J.1) (fun k => pcOPExt_injective k)
    (fun J x => peP_place hK hr hn J x)

theorem pePFamily_apply (J : {J : Finset (Fin (r + 1 + 1 - 1)) // J.card ≤ 2})
    (x : (minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    {g : StatedOmega (StatedQuadPlus (r + 1) K)}
    (hg : pcOPExt (pePIdx hr J.1) g =
      (q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
        (pePTrJ hr hK J.1))⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x *
        q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
          (pePTrJ hr hK J.1)) :
    pePFamily hK hr hn Φ J x = ((e.symm (pePTrJ hr hK J.1) : L) : G) *
      pePPhi Φ (pePIdx hr J.1) g * (((e.symm (pePTrJ hr hK J.1) : L) : G))⁻¹ :=
  peFamily_apply (D := minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK))
    (ext := fun k => pcOPExt (K := K) k) (Φ := pePPhi Φ)
    (iota := q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
    (ε := L.subtype.comp e.symm.toMonoidHom) (ρ := peRhoM hn (q2Omega_irreducible_one_one hK))
    (idx := fun J => pePIdx hr J.1) (tr := fun J => pePTrJ hr hK J.1)
    (hinj := fun k => pcOPExt_injective k) (hmem := fun J x => peP_place hK hr hn J x) J x hg

theorem pePFamily_apply_iota {t : G}
    (hΦ : ∀ k, IsNsOmPlusParam hK (by omega) (by omega) e t k (Φ k))
    (J : {J : Finset (Fin (r + 1 + 1 - 1)) // J.card ≤ 2})
    (x : (minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    {z : StatedSp (r + 1) K}
    (hz : peRhoM hn (q2Omega_irreducible_one_one hK)
        (x : spinGroup (quadMinus (r + 1 + 1) K 1 1)) =
      q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK z) :
    pePFamily hK hr hn Φ J x = ((e.symm z : L) : G) := by
  obtain ⟨g, hg⟩ := peP_place hK hr hn J x
  rw [pePFamily_apply hK hr hn Φ J x hg]
  refine peTrans_value_iota (peNormal_plus hK (by omega) (by omega) hΦ) ?_
  rw [hg, hz]

theorem isCompatible_pePFamily {t : G}
    (hΦ : ∀ k, IsNsOmPlusParam hK (by omega) (by omega) e t k (Φ k))
    (hal : NsOmPlusAligned e Φ) :
    CFSG.LieType.CurtisTits.IsCompatible
      (minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam
      (pePFamily hK hr hn Φ) :=
  isCompatible_peFamily (D := minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK))
    (ext := fun k => pcOPExt (K := K) k) (Φ := pePPhi Φ)
    (iota := q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
    (ε := L.subtype.comp e.symm.toMonoidHom) (ρ := peRhoM hn (q2Omega_irreducible_one_one hK))
    (idx := fun J => pePIdx hr J.1) (tr := fun J => pePTrJ hr hK J.1)
    (hinj := fun k => pcOPExt_injective k) (hmem := fun J x => peP_place hK hr hn J x)
    (peAligned_plus hal) (peNormal_plus hK (by omega) (by omega) hΦ)
    fun I J hIJ hI => peP_compat hK hr I J hIJ hI

theorem range_pePFamily_le (J : {J : Finset (Fin (r + 1 + 1 - 1)) // J.card ≤ 2}) :
    (pePFamily hK hr hn Φ J).range ≤ nsGlobal e := by
  refine range_peFamily_le (D := minusDatum (r + 1 + 1) (q2Omega_irreducible_one_one hK))
    (ext := fun k => pcOPExt (K := K) k) (Φ := pePPhi Φ)
    (iota := q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
    (ε := L.subtype.comp e.symm.toMonoidHom) (ρ := peRhoM hn (q2Omega_irreducible_one_one hK))
    (idx := fun J => pePIdx hr J.1) (tr := fun J => pePTrJ hr hK J.1)
    (hinj := fun k => pcOPExt_injective k) (hmem := fun J x => peP_place hK hr hn J x)
    (fun i => ?_) ?_ J
  · rintro _ ⟨g, rfl⟩
    rw [nsGlobal_def]
    exact le_iSup (fun k : Fin (r + 1) => centralizerPerfectCore (modelToG e (nsTorusSp K k))) i
      (Φ i g).2
  · rintro _ ⟨y, rfl⟩
    exact le_nsGlobal hK (by omega) e (e.symm y).2

end Family

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {r : ℕ}

theorem nsOmegaCTData_plus_of_aligned (hK : Nat.card K = 2) (hr : 4 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G)
    (Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k)))
    (hΦ : ∀ k, IsNsOmPlusParam hK (by omega) (by omega) e t k (Φ k))
    (hal : NsOmPlusAligned e Φ) :
    NsOmegaCTData e .omegaPlus := by
  have hr2 : 2 ≤ r := by omega
  have hr3 : 3 ≤ r := by omega
  have hn : 4 ≤ r + 1 + 1 := by omega
  have hirr := q2Omega_irreducible_one_one hK
  have hJ₀ : ({((Fin.last r : Fin (r + 1)) : Fin (r + 1 + 1 - 1))} :
      Finset (Fin (r + 1 + 1 - 1))).card ≤ 2 := by simp
  have hw₀ : peShortWord (r + 1 + 1) hirr ((Fin.last r : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) ∈
      (minusDatum (r + 1 + 1) hirr).leviAmalgam ⟨_, hJ₀⟩ :=
    peShortWord_mem_levi hirr (by simp) (Finset.mem_singleton_self _)
  have hρw₀ : peRhoM hn hirr
      (peShortWord (r + 1 + 1) hirr ((Fin.last r : Fin (r + 1)) : Fin (r + 1 + 1 - 1))) =
      q2OmMIota (r := r + 1) (by omega) hirr hK (nsElt (Fin.last r)) := by
    rw [q2OmMIota_nsElt_eq (Fin.last r) hK hr2]
    exact peRhoM_peShortWord hK hn hr2
  have hφw₀ : pePFamily hK hr hn Φ ⟨_, hJ₀⟩ ⟨_, hw₀⟩ = ((e.symm (nsElt (Fin.last r)) : L) : G) :=
    pePFamily_apply_iota hK hr hn Φ hΦ _ _ hρw₀
  have hnt : ∃ J, ∃ x, pePFamily hK hr hn Φ J x ≠ 1 := by
    refine ⟨⟨_, hJ₀⟩, ⟨_, hw₀⟩, ?_⟩
    rw [hφw₀]
    intro h
    apply nsElt_ne_one (K := K) (Fin.last r)
    apply e.symm.injective
    rw [map_one]
    exact Subtype.ext h
  have hadm : StatedLieAdmissible .POmegaMinus (r + 1 + 1) 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega⟩
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨ψ, hψinj, hψrange, hψφ⟩ := exists_ct_of_compatible
    (CFSG.LieType.CurtisTits.curtisTitsConclusion_spinMinus.{0} (F := K) hirr hadm hK1)
    (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn hirr)
    (pePFamily hK hr hn Φ) (isCompatible_pePFamily hK hr hn Φ hΦ hal) hnt
  have hrot : ∀ k : Fin (r + 1), ψ ((peRhoMEquiv hn hirr).symm (pdPRot k hK hr2)) =
      ((e.symm (nsElt k) : L) : G) := by
    refine pe_forall_of_last ?_ ?_
    · have h1 : (peRhoMEquiv hn hirr).symm (pdPRot (Fin.last r) hK hr2) =
          peShortWord (r + 1 + 1) hirr ((Fin.last r : Fin (r + 1)) : Fin (r + 1 + 1 - 1)) := by
        rw [MulEquiv.symm_apply_eq, peRhoMEquiv_apply, peRhoM_peShortWord hK hn hr2]
      rw [h1, ← hφw₀]
      exact hψφ ⟨_, hJ₀⟩ ⟨_, hw₀⟩
    · intro k hk ih
      have hfix := peRhoM_minusWeyl_mem_fixed (K := K) hK hn hk
      set w := kOmMFixRes K (by omega : 3 ≤ r + 1) hirr ⟨_, hfix⟩ with hwdef
      have hιw : q2OmMIota (r := r + 1) (by omega) hirr hK w =
          peRhoM hn hirr (minusWeyl (r + 1 + 1) hirr (k : Fin (r + 1 + 1 - 1))) :=
        pe_q2OmMIota_kOmMFixRes hK hr2 _ hfix
      have hJ₁ : ({(k : Fin (r + 1 + 1 - 1))} : Finset (Fin (r + 1 + 1 - 1))).card ≤ 2 := by simp
      have hn₁ : minusWeyl (r + 1 + 1) hirr (k : Fin (r + 1 + 1 - 1)) ∈
          (minusDatum (r + 1 + 1) hirr).leviAmalgam ⟨_, hJ₁⟩ :=
        minusWeyl_mem_levi hirr (Finset.mem_singleton_self _)
      have hψn : ψ (minusWeyl (r + 1 + 1) hirr (k : Fin (r + 1 + 1 - 1))) =
          ((e.symm w : L) : G) := by
        rw [show minusWeyl (r + 1 + 1) hirr (k : Fin (r + 1 + 1 - 1)) =
          ((⟨_, hn₁⟩ : (minusDatum (r + 1 + 1) hirr).leviAmalgam ⟨_, hJ₁⟩) :
            spinGroup (quadMinus (r + 1 + 1) K 1 1)) from rfl, hψφ]
        exact pePFamily_apply_iota hK hr hn Φ hΦ _ _ hιw.symm
      have hconj := peRhoM_minusWeyl_mul_pdPRot (K := K) hK hn hk hr2
      have hP : pdPRot k hK hr2 = peRhoM hn hirr (minusWeyl (r + 1 + 1) hirr
          (k : Fin (r + 1 + 1 - 1))) * pdPRot ⟨k.val + 1, hk⟩ hK hr2 *
            (peRhoM hn hirr (minusWeyl (r + 1 + 1) hirr (k : Fin (r + 1 + 1 - 1))))⁻¹ := by
        rw [hconj, mul_inv_cancel_right]
      have hsymm : (peRhoMEquiv hn hirr).symm (pdPRot k hK hr2) =
          minusWeyl (r + 1 + 1) hirr (k : Fin (r + 1 + 1 - 1)) *
            (peRhoMEquiv hn hirr).symm (pdPRot ⟨k.val + 1, hk⟩ hK hr2) *
              (minusWeyl (r + 1 + 1) hirr (k : Fin (r + 1 + 1 - 1)))⁻¹ := by
        rw [MulEquiv.symm_apply_eq, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
          peRhoMEquiv_apply, hP]
      have hw : w * nsElt ⟨k.val + 1, hk⟩ * w⁻¹ = nsElt (K := K) k := by
        apply q2OmMIota_injective (r := r + 1) (by omega) hirr hK
        rw [map_mul, map_mul, map_inv, hιw, q2OmMIota_nsElt_eq _ hK hr2,
          q2OmMIota_nsElt_eq _ hK hr2, ← hP]
      rw [hsymm, map_mul, map_mul, map_inv, hψn, ih, ← hw]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hE : ∀ k : Fin (r + 1), centralizerPerfectCore (modelToG e (nsTorusSp K k)) ≤ ψ.range := by
    intro k
    have hFinj : Function.Injective (pePPhi Φ k) :=
      Subtype.val_injective.comp (Φ k).injective
    have hFrange : (pePPhi Φ k).range = centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
      ext y
      constructor
      · rintro ⟨m, rfl⟩
        exact (Φ k m).2
      · intro hy
        exact ⟨(Φ k).symm ⟨y, hy⟩, by rw [pePPhi_apply, MulEquiv.apply_symm_apply]⟩
    have : Finite (StatedOmega (StatedQuadPlus (r + 1) K)) := Finite.of_injective _ hFinj
    have hperfM : ⁅(⊤ : Subgroup (StatedOmega (StatedQuadPlus (r + 1) K))),
        (⊤ : Subgroup (StatedOmega (StatedQuadPlus (r + 1) K)))⁆ =
          (⊤ : Subgroup (StatedOmega (StatedQuadPlus (r + 1) K))) := by
      apply Subgroup.map_injective hFinj
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hFrange,
        F4Pilot.commutator_centralizerPerfectCore]
    set f := (peRhoMEquiv hn hirr).symm.toMonoidHom.comp (pcOPExt (K := K) k) with hfdef
    have hfinj : Function.Injective f :=
      (peRhoMEquiv hn hirr).symm.injective.comp (pcOPExt_injective k)
    have hA : ⁅f.range, f.range⁆ = f.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperfM]
    have hAz : f.range.map ψ ≤ centralizer ({((e.symm (nsElt k) : L) : G)} : Set G) := by
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff, ← hrot k, ← map_mul, ← map_mul]
      congr 1
      apply (peRhoMEquiv hn hirr).injective
      have hc := pcOPExt_range_le_centralizer (K := K) k hK hr2 ⟨m, rfl⟩
      rw [mem_centralizer_singleton_iff] at hc
      simp only [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
        MulEquiv.apply_symm_apply]
      exact hc
    have hΦz : (pePPhi Φ k).range =
        perfectCore (centralizer ({((e.symm (nsElt k) : L) : G)} : Set G)) := by
      rw [hFrange, F4Pilot.centralizerPerfectCore_def, nsTorusSp, centralizer_modelToG_zpowers]
    have hcard : Nat.card (StatedOmega (StatedQuadPlus (r + 1) K)) ≤ Nat.card f.range :=
      (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).le
    rw [← hFrange]
    exact range_le_range_of_perfect_centralizer hψinj hA hAz hΦz hcard
  refine ⟨1, 1, hirr, pePFamily hK hr hn Φ, isCompatible_pePFamily hK hr hn Φ hΦ hal, ?_⟩
  refine le_antisymm (iSup_le fun J => range_pePFamily_le hK hr hn Φ J) ?_
  rw [← hψrange, nsGlobal_def]
  exact iSup_le hE

theorem spTwoOmegaPlusPlaceInput_holds : SpTwoOmegaPlusPlaceInput := by
  intro G _ _ L _ r K _ _ _ hK hr e t _ _ _ Φ hΦ hal
  exact nsOmegaCTData_plus_of_aligned hK hr e t Φ hΦ hal

end Main

end CFSG.SeitzReduction.SymplecticPilot
