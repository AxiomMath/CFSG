module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEMinusPlace

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Rot

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem pe_mul_pdRotMat {Q : QuadraticForm K (ι → K)} {g : Matrix ι ι K}
    (hg : ∀ z, Q (g *ᵥ z) = Q z) (a b : ι → K) :
    g * pdRotMat Q a b = pdRotMat Q (g *ᵥ a) (g *ᵥ b) * g := by
  have hpol : ∀ x y, polar Q (g *ᵥ x) (g *ᵥ y) = polar Q x y := fun x y => by
    rw [polar, polar, ← Matrix.mulVec_add, hg, hg, hg]
  refine pd_matrix_ext_mulVec fun x => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pdRotMat_mulVec, pdRotMat_mulVec, hpol,
    hpol, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_add]

end Rot

section Global

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

theorem peRho_peTorusWord (hr : 2 ≤ r) (hn : 3 ≤ r + 2) :
    peRho hn (peTorusWord K hn (Fin.last r).castSucc (Fin.last (r + 1))) =
      pdMRot (Fin.last r) hr := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  apply Units.ext
  refine pd_matrix_ext_mulVec fun x => ?_
  rw [peRho_mulVec, spinAction_peTorusWord hn (by simp) (by simp), coe_pdMRot, pdRotMat_mulVec,
    pdM_polar_a, pdM_polar_b]
  funext c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pdMA, pdMB, kOmegaVec]
  linear_combination -(x (Sum.inl (Fin.last r).castSucc) + (x (Sum.inl (Fin.last (r + 1))) +
    x (Sum.inr (Fin.last (r + 1))))) * ((Pi.single (Sum.inl (Fin.last (r + 1))) (1 : K) :
      Fin (r + 2) ⊕ Fin (r + 2) → K) c + (Pi.single (Sum.inr (Fin.last (r + 1))) (1 : K) :
        Fin (r + 2) ⊕ Fin (r + 2) → K) c) * h2

end Global

section Weyl

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hn : 3 ≤ r + 2) {k : Fin (r + 1)}
  (hk : k.val + 1 < r + 1)
include hk

omit [Finite K] in
theorem peRho_weylD_mulVec (m : Fin (r + 2)) (s : Bool) :
    (((peRho hn (weylD K hn k.castSucc) : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ plusVec (r + 2) K m s =
      plusVec (r + 2) K (Equiv.swap k.castSucc ⟨k.val + 1, by omega⟩ m) s := by
  rw [peRho_mulVec, spinAction_weylD_of_lt hn (k := k.castSucc) (by simp; omega)]
  rfl

theorem pe_swap_last : Equiv.swap k.castSucc ⟨k.val + 1, by omega⟩ (Fin.last (r + 1)) =
    Fin.last (r + 1) :=
  Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp; omega))
    (Fin.ne_of_val_ne (by simp; omega))

omit [Finite K] in
theorem peRho_weylD_mulVec_vec :
    (((peRho hn (weylD K hn k.castSucc) : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ kOmegaVec K (r + 1) = kOmegaVec K (r + 1) := by
  rw [kOmegaVec, Matrix.mulVec_add, ← plusVec_true, ← plusVec_false, peRho_weylD_mulVec hn hk,
    peRho_weylD_mulVec hn hk, pe_swap_last hk]

omit [Finite K] in
theorem peRho_weylD_mulVec_pdMA :
    (((peRho hn (weylD K hn k.castSucc) : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMA K ⟨k.val + 1, hk⟩ = pdMA K k := by
  rw [pdMA, Matrix.mulVec_add, peRho_weylD_mulVec_vec hn hk, ← plusVec_true,
    peRho_weylD_mulVec hn hk]
  have h : Equiv.swap k.castSucc ⟨k.val + 1, by omega⟩ (⟨k.val + 1, hk⟩ : Fin (r + 1)).castSucc =
      k.castSucc := by
    rw [show (⟨k.val + 1, hk⟩ : Fin (r + 1)).castSucc = (⟨k.val + 1, by omega⟩ : Fin (r + 2)) from
      rfl, Equiv.swap_apply_right]
  rw [h, plusVec_true, pdMA]

omit [Finite K] in
theorem peRho_weylD_mulVec_pdMB :
    (((peRho hn (weylD K hn k.castSucc) : StatedOmega (StatedQuadPlus (r + 2) K)) :
      GL (Fin (r + 2) ⊕ Fin (r + 2)) K) : Matrix (Fin (r + 2) ⊕ Fin (r + 2))
        (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ pdMB K ⟨k.val + 1, hk⟩ = pdMB K k := by
  rw [pdMB, Matrix.mulVec_add, peRho_weylD_mulVec_vec hn hk, ← plusVec_false,
    peRho_weylD_mulVec hn hk]
  have h : Equiv.swap k.castSucc ⟨k.val + 1, by omega⟩ (⟨k.val + 1, hk⟩ : Fin (r + 1)).castSucc =
      k.castSucc := by
    rw [show (⟨k.val + 1, hk⟩ : Fin (r + 1)).castSucc = (⟨k.val + 1, by omega⟩ : Fin (r + 2)) from
      rfl, Equiv.swap_apply_right]
  rw [h, plusVec_false, pdMB]

omit [Finite K] in
theorem peRho_weylD_mem_fixed :
    peRho hn (weylD K hn k.castSucc) ∈ fixedSubgroup (kOmegaBetaC K (r + 1)) := by
  rw [mem_fixedSubgroup_kOmegaBetaC_iff K (by omega)]
  exact peRho_weylD_mulVec_vec hn hk

theorem peRho_weylD_mul_pdMRot (hr : 2 ≤ r) :
    peRho hn (weylD K hn k.castSucc) * pdMRot ⟨k.val + 1, hk⟩ hr =
      pdMRot k hr * peRho hn (weylD K hn k.castSucc) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_pdMRot, coe_pdMRot]
  have hiso : ∀ z, quadPlus (r + 2) K ((((peRho hn (weylD K hn k.castSucc) :
      StatedOmega (StatedQuadPlus (r + 2) K)) : GL (Fin (r + 2) ⊕ Fin (r + 2)) K) :
        Matrix (Fin (r + 2) ⊕ Fin (r + 2)) (Fin (r + 2) ⊕ Fin (r + 2)) K) *ᵥ z) =
      quadPlus (r + 2) K z := fun z => by
    rw [coe_quadPlus]
    exact pd_isometry_of_mem_statedOmega (peRho hn (weylD K hn k.castSucc)).2 z
  rw [pe_mul_pdRotMat hiso, peRho_weylD_mulVec_pdMA hn hk, peRho_weylD_mulVec_pdMB hn hk]

end Weyl

theorem pe_forall_of_last {N : ℕ} {P : Fin (N + 1) → Prop} (hlast : P (Fin.last N))
    (hstep : ∀ (k : Fin (N + 1)) (hk : k.val + 1 < N + 1), P ⟨k.val + 1, hk⟩ → P k)
    (k : Fin (N + 1)) : P k := by
  obtain ⟨d, hd⟩ : ∃ d, d = N - k.val := ⟨_, rfl⟩
  induction d generalizing k with
  | zero =>
    have : k = Fin.last N := Fin.ext (by simp; omega)
    exact this ▸ hlast
  | succ d ih =>
    have hk1 : k.val + 1 < N + 1 := by omega
    exact hstep k hk1 (ih ⟨k.val + 1, hk1⟩ (by simp; omega))

section Family

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ} (hK : Nat.card K = 2) (hr : 4 ≤ r) (hn : 3 ≤ r + 2) {e : L ≃* StatedSp (r + 1) K}
  (Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k)))

@[expose] noncomputable def peMFamily :
    ∀ J, (plusDatum (r + 2) K hn).leviAmalgam J →* G :=
  peFamily (plusDatum (r + 2) K hn) (fun k => pcOMExt (K := K) k) (peMPhi Φ)
    (q2OmIota (r := r + 1) (by omega) hK (by omega)) (L.subtype.comp e.symm.toMonoidHom)
    (peRho hn) (fun J => peMIdx hr J.1) (fun J => peMTrJ hr J.1) (fun k => pcOMExt_injective k)
    (fun J x => peM_place hK hr hn J x)

theorem peMFamily_apply (J : {J : Finset (Fin (r + 2)) // J.card ≤ 2})
    (x : (plusDatum (r + 2) K hn).leviAmalgam J) {g : StatedOmega (StatedQuadMinus (r + 1) K 1 1)}
    (hg : pcOMExt (peMIdx hr J.1) g =
      (q2OmIota (r := r + 1) (by omega) hK (by omega) (peMTrJ hr J.1))⁻¹ * peRho hn x *
        q2OmIota (r := r + 1) (by omega) hK (by omega) (peMTrJ hr J.1)) :
    peMFamily hK hr hn Φ J x = ((e.symm (peMTrJ hr J.1) : L) : G) * peMPhi Φ (peMIdx hr J.1) g *
      (((e.symm (peMTrJ hr J.1) : L) : G))⁻¹ :=
  peFamily_apply (D := plusDatum (r + 2) K hn) (ext := fun k => pcOMExt (K := K) k)
    (Φ := peMPhi Φ) (iota := q2OmIota (r := r + 1) (by omega) hK (by omega))
    (ε := L.subtype.comp e.symm.toMonoidHom) (ρ := peRho hn) (idx := fun J => peMIdx hr J.1)
    (tr := fun J => peMTrJ hr J.1) (hinj := fun k => pcOMExt_injective k)
    (hmem := fun J x => peM_place hK hr hn J x) J x hg

theorem peMFamily_apply_iota {t : G} (hΦ : ∀ k, IsNsOmMinusParam hK (by omega) e t k (Φ k))
    (J : {J : Finset (Fin (r + 2)) // J.card ≤ 2}) (x : (plusDatum (r + 2) K hn).leviAmalgam J)
    {z : StatedSp (r + 1) K}
    (hz : peRho hn (x : spinGroup (quadPlus (r + 2) K)) =
      q2OmIota (r := r + 1) (by omega) hK (by omega) z) :
    peMFamily hK hr hn Φ J x = ((e.symm z : L) : G) := by
  obtain ⟨g, hg⟩ := peM_place hK hr hn J x
  rw [peMFamily_apply hK hr hn Φ J x hg]
  refine peTrans_value_iota (peNormal_minus hK (by omega) hΦ) ?_
  rw [hg, hz]

theorem isCompatible_peMFamily {t : G} (hΦ : ∀ k, IsNsOmMinusParam hK (by omega) e t k (Φ k))
    (hal : NsOmMinusAligned e Φ) :
    CFSG.LieType.CurtisTits.IsCompatible (plusDatum (r + 2) K hn).leviAmalgam
      (peMFamily hK hr hn Φ) :=
  isCompatible_peFamily (D := plusDatum (r + 2) K hn) (ext := fun k => pcOMExt (K := K) k)
    (Φ := peMPhi Φ) (iota := q2OmIota (r := r + 1) (by omega) hK (by omega))
    (ε := L.subtype.comp e.symm.toMonoidHom) (ρ := peRho hn) (idx := fun J => peMIdx hr J.1)
    (tr := fun J => peMTrJ hr J.1) (hinj := fun k => pcOMExt_injective k)
    (hmem := fun J x => peM_place hK hr hn J x) (peAligned_minus hal)
    (peNormal_minus hK (by omega) hΦ) fun I J hIJ hI => peM_compat hK hr I J hIJ hI

theorem range_peMFamily_le (J : {J : Finset (Fin (r + 2)) // J.card ≤ 2}) :
    (peMFamily hK hr hn Φ J).range ≤ nsGlobal e := by
  refine range_peFamily_le (D := plusDatum (r + 2) K hn) (ext := fun k => pcOMExt (K := K) k)
    (Φ := peMPhi Φ) (iota := q2OmIota (r := r + 1) (by omega) hK (by omega))
    (ε := L.subtype.comp e.symm.toMonoidHom) (ρ := peRho hn) (idx := fun J => peMIdx hr J.1)
    (tr := fun J => peMTrJ hr J.1) (hinj := fun k => pcOMExt_injective k)
    (hmem := fun J x => peM_place hK hr hn J x) (fun i => ?_) ?_ J
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

theorem nsOmegaCTData_minus_of_aligned (hK : Nat.card K = 2) (hr : 4 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G)
    (Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k)))
    (hΦ : ∀ k, IsNsOmMinusParam hK (by omega) e t k (Φ k)) (hal : NsOmMinusAligned e Φ) :
    NsOmegaCTData e .omegaMinus := by
  have hr3 : 3 ≤ r := by omega
  have hn : 3 ≤ r + 2 := by omega
  have hJ₀ : ({(Fin.last r).castSucc, Fin.last (r + 1)} : Finset (Fin (r + 2))).card ≤ 2 :=
    Finset.card_le_two
  have hw₀ : peTorusWord K hn (Fin.last r).castSucc (Fin.last (r + 1)) ∈
      (plusDatum (r + 2) K hn).leviAmalgam ⟨_, hJ₀⟩ :=
    peTorusWord_mem_levi hn (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hρw₀ : peRho hn (peTorusWord K hn (Fin.last r).castSucc (Fin.last (r + 1))) =
      q2OmIota (r := r + 1) (by omega) hK (by omega) (nsElt (Fin.last r)) := by
    rw [q2OmIota_nsElt_eq (Fin.last r) hK hr3]
    exact peRho_peTorusWord (by omega) hn
  have hφw₀ : peMFamily hK hr hn Φ ⟨_, hJ₀⟩ ⟨_, hw₀⟩ = ((e.symm (nsElt (Fin.last r)) : L) : G) :=
    peMFamily_apply_iota hK hr hn Φ hΦ _ _ hρw₀
  have hnt : ∃ J, ∃ x, peMFamily hK hr hn Φ J x ≠ 1 := by
    refine ⟨⟨_, hJ₀⟩, ⟨_, hw₀⟩, ?_⟩
    rw [hφw₀]
    intro h
    apply nsElt_ne_one (K := K) (Fin.last r)
    apply e.symm.injective
    rw [map_one]
    exact Subtype.ext h
  have hadm : StatedLieAdmissible .POmegaPlus (r + 2) 2 1 := ⟨Nat.prime_two, le_rfl, by omega⟩
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨ψ, hψinj, hψrange, hψφ⟩ := exists_ct_of_compatible
    (CFSG.LieType.CurtisTits.curtisTitsConclusion_spinPlus.{0} (F := K) hadm hK1 hn)
    (q2Omega_center_spinGroup_quadPlus_eq_bot hn) (peMFamily hK hr hn Φ)
    (isCompatible_peMFamily hK hr hn Φ hΦ hal) hnt
  have hrot : ∀ k : Fin (r + 1), ψ ((peRhoEquiv hn).symm (pdMRot k (by omega))) =
      ((e.symm (nsElt k) : L) : G) := by
    refine pe_forall_of_last ?_ ?_
    · have h1 : (peRhoEquiv hn).symm (pdMRot (Fin.last r) (by omega)) =
          peTorusWord K hn (Fin.last r).castSucc (Fin.last (r + 1)) := by
        rw [MulEquiv.symm_apply_eq, peRhoEquiv_apply, peRho_peTorusWord (by omega) hn]
      rw [h1, ← hφw₀]
      exact hψφ ⟨_, hJ₀⟩ ⟨_, hw₀⟩
    · intro k hk ih
      have hfix := peRho_weylD_mem_fixed (K := K) hn hk
      set w := kOmegaFixRes K (by omega : 2 ≤ r + 1) ⟨_, hfix⟩ with hwdef
      have hιw : q2OmIota (r := r + 1) (by omega) hK (by omega) w =
          peRho hn (weylD K hn k.castSucc) := pe_q2OmIota_kOmegaFixRes hK hr3 _ hfix
      have hJ₁ : ({k.castSucc} : Finset (Fin (r + 2))).card ≤ 2 := by simp
      have hn₁ : weylD K hn k.castSucc ∈ (plusDatum (r + 2) K hn).leviAmalgam ⟨_, hJ₁⟩ :=
        weylD_mem_levi hn (Finset.mem_singleton_self _)
      have hψn : ψ (weylD K hn k.castSucc) = ((e.symm w : L) : G) := by
        rw [show weylD K hn k.castSucc = ((⟨_, hn₁⟩ : (plusDatum (r + 2) K hn).leviAmalgam
          ⟨_, hJ₁⟩) : spinGroup (quadPlus (r + 2) K)) from rfl, hψφ]
        exact peMFamily_apply_iota hK hr hn Φ hΦ _ _ hιw.symm
      have hconj := peRho_weylD_mul_pdMRot (K := K) hn hk (by omega)
      have hP : pdMRot k (by omega) = peRho hn (weylD K hn k.castSucc) *
          pdMRot ⟨k.val + 1, hk⟩ (by omega) * (peRho hn (weylD K hn k.castSucc))⁻¹ := by
        rw [hconj, mul_inv_cancel_right]
      have hsymm : (peRhoEquiv hn).symm (pdMRot k (by omega)) = weylD K hn k.castSucc *
          (peRhoEquiv hn).symm (pdMRot ⟨k.val + 1, hk⟩ (by omega)) *
            (weylD K hn k.castSucc)⁻¹ := by
        rw [MulEquiv.symm_apply_eq, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
          peRhoEquiv_apply, hP]
      have hw : w * nsElt ⟨k.val + 1, hk⟩ * w⁻¹ = nsElt (K := K) k := by
        apply q2OmIota_injective (r := r + 1) (by omega) hK (by omega)
        rw [map_mul, map_mul, map_inv, hιw, q2OmIota_nsElt_eq _ hK hr3,
          q2OmIota_nsElt_eq _ hK hr3, ← hP]
      rw [hsymm, map_mul, map_mul, map_inv, hψn, ih, ← hw]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hE : ∀ k : Fin (r + 1), centralizerPerfectCore (modelToG e (nsTorusSp K k)) ≤ ψ.range := by
    intro k
    have hFinj : Function.Injective (peMPhi Φ k) :=
      Subtype.val_injective.comp (Φ k).injective
    have hFrange : (peMPhi Φ k).range = centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
      ext y
      constructor
      · rintro ⟨m, rfl⟩
        exact (Φ k m).2
      · intro hy
        exact ⟨(Φ k).symm ⟨y, hy⟩, by rw [peMPhi_apply, MulEquiv.apply_symm_apply]⟩
    have : Finite (StatedOmega (StatedQuadMinus (r + 1) K 1 1)) := Finite.of_injective _ hFinj
    have hperfM : ⁅(⊤ : Subgroup (StatedOmega (StatedQuadMinus (r + 1) K 1 1))),
        (⊤ : Subgroup (StatedOmega (StatedQuadMinus (r + 1) K 1 1)))⁆ =
          (⊤ : Subgroup (StatedOmega (StatedQuadMinus (r + 1) K 1 1))) := by
      apply Subgroup.map_injective hFinj
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hFrange,
        F4Pilot.commutator_centralizerPerfectCore]
    set f := (peRhoEquiv hn).symm.toMonoidHom.comp (pcOMExt (K := K) k) with hfdef
    have hfinj : Function.Injective f :=
      (peRhoEquiv hn).symm.injective.comp (pcOMExt_injective k)
    have hA : ⁅f.range, f.range⁆ = f.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperfM]
    have hAz : f.range.map ψ ≤ centralizer ({((e.symm (nsElt k) : L) : G)} : Set G) := by
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff, ← hrot k, ← map_mul, ← map_mul]
      congr 1
      apply (peRhoEquiv hn).injective
      have hc := pcOMExt_range_le_centralizer (K := K) k (by omega) ⟨m, rfl⟩
      rw [mem_centralizer_singleton_iff] at hc
      simp only [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
        MulEquiv.apply_symm_apply]
      exact hc
    have hΦz : (peMPhi Φ k).range =
        perfectCore (centralizer ({((e.symm (nsElt k) : L) : G)} : Set G)) := by
      rw [hFrange, F4Pilot.centralizerPerfectCore_def, nsTorusSp, centralizer_modelToG_zpowers]
    have hcard : Nat.card (StatedOmega (StatedQuadMinus (r + 1) K 1 1)) ≤ Nat.card f.range :=
      (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).le
    rw [← hFrange]
    exact range_le_range_of_perfect_centralizer hψinj hA hAz hΦz hcard
  refine ⟨hn, peMFamily hK hr hn Φ, isCompatible_peMFamily hK hr hn Φ hΦ hal, ?_⟩
  refine le_antisymm (iSup_le fun J => range_peMFamily_le hK hr hn Φ J) ?_
  rw [← hψrange, nsGlobal_def]
  exact iSup_le hE

theorem spTwoOmegaMinusPlaceInput_holds : SpTwoOmegaMinusPlaceInput := by
  intro G _ _ L _ r K _ _ _ hK hr e t _ _ _ Φ hΦ hal
  exact nsOmegaCTData_minus_of_aligned hK hr e t Φ hΦ hal

end Main

end CFSG.SeitzReduction.SymplecticPilot
