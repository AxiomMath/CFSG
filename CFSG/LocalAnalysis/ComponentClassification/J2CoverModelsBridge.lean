module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferAutomorphism
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsRigid

public section

namespace CFSG.ComponentClassification.J2Cover.Models

open CFSG.ComponentClassification.CentralCover CFSG.Monster.B.Co2

theorem outerU_eq_outerArr : outerU = J2Cover.outerArr := by decide +kernel

theorem gA_eq_permA : gA = J2Cover.permA := by
  rw [gA_eq, ← J2Cover.actionHom_a]
  rfl

theorem gB_eq_permB : gB = J2Cover.permB := by
  rw [gB_eq, ← J2Cover.actionHom_b]
  rfl

theorem P_eq_autP : P = J2Cover.P := by
  rw [P_eq, gA_eq_permA, gB_eq_permB]
  rfl

theorem uOut_eq_permU : uOut = J2Cover.permU := by
  rw [uOut, outerU_eq_outerArr]
  rfl

theorem bOut_eq_permU : bOut = J2Cover.permB * J2Cover.permU * J2Cover.permB⁻¹ := by
  rw [bOut_eq, uOut_eq_permU, gB_eq_permB]

noncomputable abbrev Sp : Subgroup P := S.subgroupOf P

@[expose] noncomputable def eS : Sp ≃* S := Subgroup.subgroupOfEquivOfLe S_le_P

theorem coe_eS (s : Sp) : ((eS s : S) : Perm315) = ((s : P) : Perm315) :=
  Subgroup.subgroupOfEquivOfLe_apply_coe S_le_P s

theorem incl_eS (s : Sp) : incl (eS s) = (s : P) := Subtype.ext (by rw [incl_coe, coe_eS])

theorem coe_eS_symm (s : S) : ((eS.symm s : Sp) : P) = incl s := by
  rw [← incl_eS, MulEquiv.apply_symm_apply]

theorem incl_mem_Sp (s : S) : incl s ∈ Sp := by
  rw [Subgroup.mem_subgroupOf, incl_coe]
  exact s.2

@[expose] noncomputable def repF (i : Fin 4725) : P := repP i

theorem rep_mul_eq_P (i : Fin 4725) (g : P) :
    repF i * g = incl (factor i g) * repF (cosetAct i g) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, incl_coe]
    exact rep_mul_eq i g)

theorem isRightTransversal : IsRightTransversal Sp repF := by
  intro g
  obtain ⟨⟨k, i⟩, hki⟩ := tv_surjective g
  have hg : g = incl (elt k) * repF i := Subtype.ext (by
    rw [← hki, tv_coe, Subgroup.coe_mul, incl_coe]
    rfl)
  refine ⟨i, ?_, fun j hj => ?_⟩
  · change g * (repF i)⁻¹ ∈ Sp
    rw [hg, mul_inv_cancel_right]
    exact incl_mem_Sp _
  · change g * (repF j)⁻¹ ∈ Sp at hj
    rw [Subgroup.mem_subgroupOf] at hj
    obtain ⟨x, hx, hxe⟩ := exists_elt hj
    have h1 : (elt (⟨x, hx⟩ : Fin 128) : Perm315) * rep j = (elt k : Perm315) * rep i := by
      rw [show ((elt ((⟨x, hx⟩ : Fin 128) : ℕ)) : Perm315) = _ from hxe, hg]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, incl_coe, repF, repP_coe]
      group
    exact (tv_injective h1).2

theorem act_eq (i : Fin 4725) (g : P) : isRightTransversal.act i g = cosetAct i g :=
  isRightTransversal.act_eq_of_eq (incl_mem_Sp _) (rep_mul_eq_P i g)

theorem coef_eq (i : Fin 4725) (g : P) : isRightTransversal.coef i g = eS.symm (factor i g) :=
  Subtype.ext (by
    rw [isRightTransversal.coe_coef_eq_of_eq (incl_mem_Sp _) (rep_mul_eq_P i g), coe_eS_symm])

@[expose] noncomputable def fN : CentralCover.NormCocycle Sp where
  toFun s t := fCoc (eS s) (eS t)
  map_one_left t := by rw [map_one]; exact isNormCocycle_fCoc.1 _
  map_one_right s := by rw [map_one]; exact isNormCocycle_fCoc.2.1 _
  cocycle a b c := by rw [map_mul, map_mul]; exact isNormCocycle_fCoc.2.2 _ _ _

theorem fN_apply (s t : Sp) : fN s t = fCoc (eS s) (eS t) := rfl

theorem transfer₂_eq (h : S → S → ZMod 2) (g k : P) :
    isRightTransversal.transfer₂ (fun s t => h (eS s) (eS t)) g k = transfer h g k := by
  simp only [IsRightTransversal.transfer₂_apply, coef_eq, act_eq, MulEquiv.apply_symm_apply]
  rfl

@[expose] noncomputable def muN (s : Sp) : ZMod 2 := muCoch (eS s)

theorem transfer₂_add_coboundary_mu (s t : Sp) :
    isRightTransversal.transfer₂ fN s t + coboundary muN s t = fN s t := by
  have h := transfer_fCoc (eS s) (eS t)
  rw [incl_eS, incl_eS] at h
  rw [show isRightTransversal.transfer₂ fN s t =
      isRightTransversal.transfer₂ (fun s t => fCoc (eS s) (eS t)) s t from rfl, transfer₂_eq,
    coboundary_apply, fN_apply, muN, muN, muN, map_mul]
  rw [cob] at h
  exact h

abbrev RfN : Type := CocycleExtension fN

@[expose] noncomputable def rfEquiv : RfN ≃* Rf where
  toFun x := ⟨x.fst, eS x.snd⟩
  invFun y := ⟨y.e, eS.symm y.g⟩
  left_inv x := CocycleExtension.ext rfl (eS.symm_apply_apply x.snd)
  right_inv y := CocExt.ext rfl (eS.apply_symm_apply y.g)
  map_mul' x y := CocExt.ext (by
      change x.fst + y.fst + fN x.snd y.snd = x.fst + y.fst + fNorm.toFun (eS x.snd) (eS y.snd)
      rfl) (map_mul eS x.snd y.snd)

theorem rfEquiv_e (x : RfN) : (rfEquiv x).e = x.fst := rfl

theorem rfEquiv_g (x : RfN) : (rfEquiv x).g = eS x.snd := rfl

theorem rfEquiv_symm_fst (y : Rf) : (rfEquiv.symm y).fst = y.e := rfl

theorem rfEquiv_symm_snd (y : Rf) : (rfEquiv.symm y).snd = eS.symm y.g := rfl

theorem rfEquiv_mk_one_one : rfEquiv ⟨1, 1⟩ = CocExt.central :=
  CocExt.ext rfl (map_one eS)

@[expose] noncomputable def tauN : RfN ≃* RfN := rfEquiv.trans (tauR.trans rfEquiv.symm)

theorem rfEquiv_tauN (x : RfN) : rfEquiv (tauN x) = tauR (rfEquiv x) := by
  change rfEquiv (rfEquiv.symm (tauR (rfEquiv x))) = _
  rw [MulEquiv.apply_symm_apply]

theorem tauN_snd (x : RfN) : ((tauN x).snd : P) = betaP x.snd := by
  have h := congrArg CocExt.g (rfEquiv_tauN x)
  rw [rfEquiv_g, tauR_g, rfEquiv_g] at h
  rw [← incl_eS, h, incl_betaS, incl_eS]

theorem tauN_apply (x : RfN) :
    tauN x = ⟨x.fst + lamCoch (eS x.snd), eS.symm (betaS (eS x.snd))⟩ :=
  rfl

theorem betaP_repF (i : Fin 4725) : betaP (repF i) = incl (aElt i) * repF (sigmaIdx i) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, incl_coe]
    exact betaP_repP i)

theorem autIndex_eq (i : Fin 4725) : isRightTransversal.autIndex betaP i = sigmaIdx i :=
  isRightTransversal.autIndex_eq_of_eq betaP (incl_mem_Sp (aElt i)) (betaP_repF i)

theorem autCoef_eq (i : Fin 4725) : isRightTransversal.autCoef betaP i = eS.symm (aElt i) :=
  Subtype.ext ((isRightTransversal.coe_autCoef_eq_of_eq betaP (incl_mem_Sp (aElt i))
    (betaP_repF i)).trans (coe_eS_symm _).symm)

theorem rfEquiv_mk (e : ZMod 2) (s : S) : rfEquiv ⟨e, eS.symm s⟩ = ⟨e, s⟩ :=
  CocExt.ext rfl (eS.apply_symm_apply s)

theorem transportSum_eq (g : P) : isRightTransversal.transportSum betaP tauN g = bigLam g := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [IsRightTransversal.transportCoord, autCoef_eq, autCoef_eq, coef_eq, act_eq, cCoef, cMul,
    ← rfEquiv_e, map_mul, map_mul, map_inv, rfEquiv_tauN, rfEquiv_mk, rfEquiv_mk, rfEquiv_mk]
  rfl

theorem inducedAut_eq (s : Sp) : inducedAut tauN_snd s = eS.symm (betaS (eS s)) :=
  Subtype.ext (by rw [coe_inducedAut, coe_eS_symm, incl_betaS, incl_eS])

theorem restrictAut_eq_tauN :
    isRightTransversal.restrictAut tauN_snd muN transfer₂_add_coboundary_mu = tauN := by
  ext x
  · rw [IsRightTransversal.restrictAut_apply, tauN_apply, inducedAut_eq, transportSum_eq]
    change x.fst + bigLam x.snd + muCoch (eS x.snd) + muCoch (eS (eS.symm (betaS (eS x.snd)))) =
      x.fst + lamCoch (eS x.snd)
    rw [MulEquiv.apply_symm_apply, lamCoch_eq (eS x.snd), incl_eS, add_assoc, add_assoc,
      add_assoc]
  · rw [IsRightTransversal.restrictAut_apply, tauN_apply, inducedAut_eq]

theorem transport_beta {E : Type*} [Group E] [Group.IsPerfect E] {π : E →* P} {z : E}
    (hπ : IsCentralDoubleExt π z) (ι : Sp.comap π ≃* RfN) (hι : ∀ x, ((ι x).snd : P) = π x) :
    ∃ ι' : Sp.comap π ≃* RfN, (∀ x : Sp.comap π, ((ι' x).snd : P) = π x) ∧
      ((ι'.symm ⟨1, 1⟩ : Sp.comap π) : E) = z ∧
      ∀ φ : E ≃* E, (∀ x, π (φ x) = betaP (π x)) →
        ∀ (x : E) (hx : π x ∈ Sp) (hφx : π (φ x) ∈ Sp), ι' ⟨φ x, hφx⟩ = tauN (ι' ⟨x, hx⟩) := by
  have hodd : Odd (Fintype.card (Fin 4725)) := by
    rw [Fintype.card_fin]
    decide
  obtain ⟨-, -, -, -, -, -, Ψ, -, -, -, ι', hι', hz, -, hact⟩ :=
    isRightTransversal.odd_index_central_double_cover_transfer_and_automorphism_transport hodd
      tauN_snd muN transfer₂_add_coboundary_mu hπ ι hι
  refine ⟨ι', fun x => by rw [hι'], hz, fun φ hφ x hx hφx => ?_⟩
  rw [hact φ hφ x hx hφx, restrictAut_eq_tauN]

theorem card_RfN : Nat.card RfN = 256 := by
  rw [Nat.card_congr rfEquiv.toEquiv, card_Rf]

theorem mem_center_RfN (x : RfN) :
    x ∈ Subgroup.center RfN ↔ rfEquiv x ∈ Subgroup.center Rf := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h y
    obtain ⟨w, rfl⟩ := rfEquiv.surjective y
    rw [← map_mul, ← map_mul, h w]
  · intro h y
    apply rfEquiv.injective
    rw [map_mul, map_mul, h (rfEquiv y)]

theorem center_RfN (x : RfN) :
    x ∈ Subgroup.center RfN ↔ x = 1 ∨ x = rfEquiv.symm zR ∨ x = ⟨1, 1⟩ ∨
      x = rfEquiv.symm (zR * CocExt.central) := by
  rw [mem_center_RfN, mem_center_Rf, ← rfEquiv.injective.eq_iff, map_one,
    ← rfEquiv.injective.eq_iff, MulEquiv.apply_symm_apply, ← rfEquiv.injective.eq_iff (b := ⟨1, 1⟩),
    rfEquiv_mk_one_one, ← rfEquiv.injective.eq_iff, MulEquiv.apply_symm_apply]

theorem aut_fix_center_RfN (φ : RfN ≃* RfN) : ∀ x ∈ Subgroup.center RfN, φ x = x := by
  intro x hx
  have h := aut_fix_center_Rf (rfEquiv.symm.trans (φ.trans rfEquiv)) (rfEquiv x)
    ((mem_center_RfN x).1 hx)
  change rfEquiv (φ (rfEquiv.symm (rfEquiv x))) = rfEquiv x at h
  rw [MulEquiv.symm_apply_apply] at h
  exact rfEquiv.injective h

theorem tauN_mk_one_one : tauN ⟨1, 1⟩ = ⟨1, 1⟩ := by
  apply rfEquiv.injective
  rw [rfEquiv_tauN, rfEquiv_mk_one_one, tauR_central]

theorem tauN_tauN (x : RfN) : tauN (tauN x) = x := by
  apply rfEquiv.injective
  rw [rfEquiv_tauN, rfEquiv_tauN, tauR_tauR]


@[expose] noncomputable def TwistExt.congr {R R' : Type*} [Group R] [Group R'] {D : TwistData R}
    {D' : TwistData R'} (φ : R ≃* R') (hτ : ∀ x, φ (D.τ x) = D'.τ (φ x)) (hz : φ D.z = D'.z)
    (hε : D.ε = D'.ε) : TwistExt D ≃* TwistExt D' where
  toFun p := ⟨φ p.x, p.e⟩
  invFun q := ⟨φ.symm q.x, q.e⟩
  left_inv p := TwistExt.ext (φ.symm_apply_apply p.x) rfl
  right_inv q := TwistExt.ext (φ.apply_symm_apply q.x) rfl
  map_mul' p q := by
    have hτp : ∀ (e : ZMod 2) (y : R), φ (TwistExt.tauPow D e y) = TwistExt.tauPow D' e (φ y) := by
      intro e y
      rcases TwistExt.zmod_two_cases e with rfl | rfl
      · rw [TwistExt.tauPow_zero, TwistExt.tauPow_zero]
      · rw [TwistExt.tauPow_one, TwistExt.tauPow_one, hτ]
    have hzp : ∀ k : ZMod 2, φ (TwistExt.zPow D k) = TwistExt.zPow D' k := by
      intro k
      rcases TwistExt.zmod_two_cases k with rfl | rfl
      · rw [TwistExt.zPow_zero, TwistExt.zPow_zero, map_one]
      · rw [TwistExt.zPow_one, TwistExt.zPow_one, hz]
    refine TwistExt.ext ?_ rfl
    change φ (p.x * TwistExt.tauPow D p.e q.x * TwistExt.zPow D (D.ε * p.e * q.e)) =
      φ p.x * TwistExt.tauPow D' p.e (φ q.x) * TwistExt.zPow D' (D'.ε * p.e * q.e)
    rw [map_mul, map_mul, hτp, hzp, hε]

@[expose] noncomputable def tDataN (ε : ZMod 2) : TwistData RfN where
  τ := tauN
  z := ⟨1, 1⟩
  ε := ε
  τ_τ := tauN_tauN
  τ_z := tauN_mk_one_one
  z_mul x := (Subgroup.mem_center_iff.1 (CocycleExtension.mk_one_mem_center 1) x).symm
  z_z := by rw [CocycleExtension.mk_mul_mk, fN.map_one_left, mul_one, show (1 : ZMod 2) + 1 + 0 = 0
    by decide]; rfl

abbrev TepsN (ε : ZMod 2) : Type := TwistExt (tDataN ε)

@[expose] noncomputable def tEquiv (ε : ZMod 2) : TepsN ε ≃* Teps ε :=
  TwistExt.congr rfEquiv rfEquiv_tauN rfEquiv_mk_one_one rfl

theorem aut_fix_center_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ φ : H ≃* H, ∀ x ∈ Subgroup.center H, φ x = x) (φ : G ≃* G) :
    ∀ x ∈ Subgroup.center G, φ x = x := by
  intro x hx
  have hx' : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx w]
  have h1 := h (e.symm.trans (φ.trans e)) (e x) hx'
  change e (φ (e.symm (e x))) = e x at h1
  rw [MulEquiv.symm_apply_apply] at h1
  exact e.injective h1

theorem card_TepsN (ε : ZMod 2) : Nat.card (TepsN ε) = 512 := by
  rw [Nat.card_congr (tEquiv ε).toEquiv, card_Teps]

theorem aut_fix_center_TN0 (φ : TepsN 0 ≃* TepsN 0) :
    ∀ x ∈ Subgroup.center (TepsN 0), φ x = x :=
  aut_fix_center_of_mulEquiv (tEquiv 0) aut_fix_center_T0 φ

theorem aut_fix_center_TN1 (φ : TepsN 1 ≃* TepsN 1) :
    ∀ x ∈ Subgroup.center (TepsN 1), φ x = x :=
  aut_fix_center_of_mulEquiv (tEquiv 1) aut_fix_center_T1 φ


@[expose] noncomputable def hN (j : ℕ) (s t : Sp) : ZMod 2 := hCoc j (eS s) (eS t)

@[expose] noncomputable def bN (j : ℕ) (s : Sp) : ZMod 2 := bCoch j (eS s)

theorem exists_eq_coboundary_add_sum (k : CentralCover.NormCocycle Sp) :
    ∃ (b : Sp → ZMod 2) (ε : Fin 6 → ZMod 2), ∀ s t,
      k s t = coboundary b s t + ∑ j : Fin 6, ε j * hN j s t := by
  have hk : IsNormCocycle (fun s t : S => k (eS.symm s) (eS.symm t)) := by
    refine ⟨fun t => ?_, fun s => ?_, fun a b c => ?_⟩
    · change k (eS.symm 1) (eS.symm t) = 0
      rw [map_one]
      exact k.map_one_left _
    · change k (eS.symm s) (eS.symm 1) = 0
      rw [map_one]
      exact k.map_one_right _
    · change k (eS.symm a) (eS.symm b) + k (eS.symm (a * b)) (eS.symm c) =
        k (eS.symm b) (eS.symm c) + k (eS.symm a) (eS.symm (b * c))
      rw [map_mul, map_mul]
      exact k.cocycle _ _ _
  obtain ⟨b, ε, h⟩ := exists_eq_cob_add_sum _ hk
  refine ⟨fun s => b (eS s), ε, fun s t => ?_⟩
  have := h (eS s) (eS t)
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at this
  rw [this, coboundary_apply, cob, map_mul]
  rfl

theorem transfer₂_hN {j : ℕ} (hj : j < 6) (s t : Sp) :
    isRightTransversal.transfer₂ (hN j) s t = eFlag j * fN s t + coboundary (bN j) s t := by
  rw [show isRightTransversal.transfer₂ (hN j) s t =
      isRightTransversal.transfer₂ (fun s t => hCoc j (eS s) (eS t)) s t from rfl, transfer₂_eq,
    ← incl_eS s, ← incl_eS t, transfer_hCoc hj, fN_apply, coboundary_apply, bN, bN, bN,
    map_mul]
  rfl

theorem fN_not_coboundary : ¬ ∃ b : Sp → ZMod 2, ∀ s t, fN s t = coboundary b s t := by
  rintro ⟨b, hb⟩
  refine fCoc_not_cob ⟨fun s => b (eS.symm s), fun s t => ?_⟩
  have := hb (eS.symm s) (eS.symm t)
  rw [fN_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  rw [this, coboundary_apply, cob, map_mul]

theorem fN_diag (s : Sp) (hs : orderOf s = 2) :
    (fixCount ((s : P) : Perm315) = 11 ∧ fN s s = 0) ∨
      (fixCount ((s : P) : Perm315) = 15 ∧ fN s s = 1) := by
  have h := fCoc_diag (eS s) (by
    rw [← hs]
    exact orderOf_injective eS.toMonoidHom eS.injective s)
  rw [coe_eS] at h
  exact h

@[expose] noncomputable def zN : Sp := eS.symm (elt 4)

theorem coe_zN : ((zN : P) : Perm315) = elt 4 := by rw [zN, coe_eS_symm, incl_coe]

theorem center_RfN' (x : RfN) :
    x ∈ Subgroup.center RfN ↔ x = 1 ∨ x = ⟨0, zN⟩ ∨ x = ⟨1, 1⟩ ∨ x = ⟨1, zN⟩ := by
  rw [center_RfN]
  have h1 : rfEquiv.symm zR = ⟨0, zN⟩ := rfl
  have h2 : rfEquiv.symm (zR * CocExt.central) = ⟨1, zN⟩ := by
    rw [zR_mul_central]
    rfl
  rw [h1, h2]

end CFSG.ComponentClassification.J2Cover.Models
