module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1SetupBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup CFSG.Semidihedral.CentralQuotients

theorem dihedralGroup_two_mul_comm : ∀ a b : DihedralGroup 2, a * b = b * a := by
  decide

theorem dihedralGroup_two_mul_self : ∀ a : DihedralGroup 2, a * a = 1 := by
  decide

theorem dihedralGroup_eq_of_mem_center {M : ℕ} (hM : Even M) (hM2 : M ≠ 2)
    {b : DihedralGroup M} (hb : b ∈ Subgroup.center (DihedralGroup M)) (hb1 : b ≠ 1) :
    b = DihedralGroup.r ((M / 2 : ℕ) : ZMod M) := by
  rw [DihedralGroup.center_eq_closure_of_even_ne_two hM hM2] at hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  obtain ⟨m, hm⟩ := hM
  have h0 : (m : ZMod M) + (m : ZMod M) = 0 := by
    rw [← Nat.cast_add, ← hm, ZMod.natCast_self]
  rw [show M / 2 = m by omega, DihedralGroup.r_zpow] at hb1 ⊢
  rcases Int.even_or_odd k with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · exfalso
    apply hb1
    rw [← DihedralGroup.r_zero]
    congr 1
    push_cast
    linear_combination (l : ZMod M) * h0
  · congr 1
    push_cast
    linear_combination (l : ZMod M) * h0

theorem dihedralGroup_r_eq_half {M : ℕ} [NeZero M] (hM : Even M) {i : ZMod M}
    (h : DihedralGroup.r i * DihedralGroup.r i = 1) (h1 : DihedralGroup.r i ≠ 1) :
    i = ((M / 2 : ℕ) : ZMod M) := by
  rw [DihedralGroup.r_mul_r, ← DihedralGroup.r_zero, DihedralGroup.r.injEq] at h
  rw [Ne, ← DihedralGroup.r_zero, DihedralGroup.r.injEq] at h1
  have hval : (i.val + i.val) % M = 0 := by rw [← ZMod.val_add, h, ZMod.val_zero]
  have hlt := ZMod.val_lt i
  have hpos : i.val ≠ 0 := fun h0 => h1 ((ZMod.val_eq_zero i).mp h0)
  have hsum : i.val + i.val = M :=
    Nat.eq_of_dvd_of_lt_two_mul (by omega) (Nat.dvd_of_mod_eq_zero hval) (by omega)
  rw [← ZMod.natCast_zmod_val i]
  congr 1
  obtain ⟨m, hm⟩ := hM
  omega

abbrev dihedralProdMap (M : ℕ) :
    QuaternionGroup 2 × QuaternionGroup M →* DihedralGroup 2 × DihedralGroup M :=
  (quaternionToDihedral 2).prodMap (quaternionToDihedral M)

theorem dihedralProdMap_surjective {M : ℕ} (hM : M ≠ 0) :
    Function.Surjective (dihedralProdMap M) := by
  have : NeZero M := ⟨hM⟩
  rintro ⟨d₁, d₂⟩
  obtain ⟨x, hx⟩ := quaternionToDihedral_surjective 2 d₁
  obtain ⟨y, hy⟩ := quaternionToDihedral_surjective M d₂
  exact ⟨(x, y), by simp [hx, hy]⟩

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

omit [Finite J] in
theorem coe_symm_eq_iff {K : Subgroup J} {H : Type*} [Group H] (φ : K ≃* H) (y : H) {k : J}
    (hk : k ∈ K) : ((φ.symm y : K) : J) = k ↔ y = φ ⟨k, hk⟩ :=
  (Subtype.ext_iff (a1 := φ.symm y) (a2 := ⟨k, hk⟩)).symm.trans φ.symm_apply_eq

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

noncomputable def phiR (hb : CaseB1 Q B T L M) : partCLeft T L ≃* QuaternionGroup 2 :=
  hb.partC.quaternion.some

noncomputable def phiP (hb : CaseB1 Q B T L M) : partCRight T L ≃* QuaternionGroup M :=
  hb.quaternion.some

noncomputable def thetaX (hb : CaseB1 Q B T L M) :
    QuaternionGroup 2 →* J ⧸ Subgroup.center J :=
  ((QuotientGroup.mk' (Subgroup.center J)).comp (partCLeft T L).subtype).comp
    hb.phiR.symm.toMonoidHom

noncomputable def thetaD (hb : CaseB1 Q B T L M) :
    QuaternionGroup M →* J ⧸ Subgroup.center J :=
  ((QuotientGroup.mk' (Subgroup.center J)).comp (partCRight T L).subtype).comp
    hb.phiP.symm.toMonoidHom

theorem thetaX_mem (hb : CaseB1 Q B T L M) (x : QuaternionGroup 2) : hb.thetaX x ∈ b1X T L :=
  ⟨_, (hb.phiR.symm x).2, rfl⟩

theorem thetaD_mem (hb : CaseB1 Q B T L M) (y : QuaternionGroup M) : hb.thetaD y ∈ b1D T L :=
  ⟨_, (hb.phiP.symm y).2, rfl⟩

theorem thetaX_eq_one_iff (hb : CaseB1 Q B T L M) (x : QuaternionGroup 2) :
    hb.thetaX x = 1 ↔ quaternionToDihedral 2 x = 1 := by
  rw [← MonoidHom.mem_ker (f := quaternionToDihedral 2), quaternionToDihedral_ker,
    mem_nativeQuaternionZ_iff (by norm_num), Nat.cast_ofNat,
    ← quaternion_map_eq hb.phiR hb.partC.mem_left hb.partC.order]
  change ((hb.phiR.symm x : partCLeft T L) : J ⧸ Subgroup.center J) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, hb.setting.mem_center_iff, coe_symm_eq_iff _ _ (one_mem _),
    coe_symm_eq_iff _ _ hb.partC.mem_left, show hb.phiR ⟨1, one_mem _⟩ = 1 from map_one _]

theorem thetaD_eq_one_iff (hb : CaseB1 Q B T L M) (y : QuaternionGroup M) :
    hb.thetaD y = 1 ↔ quaternionToDihedral M y = 1 := by
  have : NeZero M := ⟨hb.ne_zero⟩
  rw [← MonoidHom.mem_ker (f := quaternionToDihedral M), quaternionToDihedral_ker,
    mem_nativeQuaternionZ_iff (Nat.one_le_iff_ne_zero.mpr hb.ne_zero),
    ← hb.partC.map_centralElt_right hb.phiP]
  change ((hb.phiP.symm y : partCRight T L) : J ⧸ Subgroup.center J) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, hb.setting.mem_center_iff, coe_symm_eq_iff _ _ (one_mem _),
    coe_symm_eq_iff _ _ hb.partC.mem_right, show hb.phiP ⟨1, one_mem _⟩ = 1 from map_one _]

noncomputable def thetaJ (hb : CaseB1 Q B T L M) :
    QuaternionGroup 2 × QuaternionGroup M →* J ⧸ Subgroup.center J :=
  hb.thetaX.noncommCoprod hb.thetaD fun x y =>
    hb.commute_of_mem_X_of_mem_D (hb.thetaX_mem x) (hb.thetaD_mem y)

theorem thetaJ_mem (hb : CaseB1 Q B T L M) (w : QuaternionGroup 2 × QuaternionGroup M) :
    hb.thetaJ w ∈ b1S T := by
  rw [thetaJ, MonoidHom.noncommCoprod_apply]
  exact (b1S T).mul_mem (hb.X_le_S (hb.thetaX_mem w.1)) (hb.D_le_S (hb.thetaD_mem w.2))

noncomputable def theta (hb : CaseB1 Q B T L M) :
    QuaternionGroup 2 × QuaternionGroup M →* b1S T :=
  hb.thetaJ.codRestrict (b1S T) hb.thetaJ_mem

theorem coe_theta (hb : CaseB1 Q B T L M) (w : QuaternionGroup 2 × QuaternionGroup M) :
    (hb.theta w : J ⧸ Subgroup.center J) = hb.thetaX w.1 * hb.thetaD w.2 := by
  rw [theta, MonoidHom.codRestrict_apply]
  exact MonoidHom.noncommCoprod_apply _ _ _ w

theorem theta_surjective (hb : CaseB1 Q B T L M) : Function.Surjective hb.theta := by
  rintro ⟨s, hs⟩
  obtain ⟨x, hx, d, hd, rfl⟩ := hb.exists_mul_of_mem_S hs
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨p, hp, rfl⟩ := hd
  refine ⟨(hb.phiR ⟨q, hq⟩, hb.phiP ⟨p, hp⟩), Subtype.ext ?_⟩
  rw [hb.coe_theta]
  simp [thetaX, thetaD]

theorem coe_theta_mem_X_iff (hb : CaseB1 Q B T L M) (w : QuaternionGroup 2 × QuaternionGroup M) :
    (hb.theta w : J ⧸ Subgroup.center J) ∈ b1X T L ↔ quaternionToDihedral M w.2 = 1 := by
  rw [hb.coe_theta, Subgroup.mul_mem_cancel_left _ (hb.thetaX_mem w.1), ← hb.thetaD_eq_one_iff]
  exact ⟨fun h => hb.eq_one_of_mem_X_of_mem_D h (hb.thetaD_mem w.2), fun h => h ▸ one_mem _⟩

theorem coe_theta_mem_D_iff (hb : CaseB1 Q B T L M) (w : QuaternionGroup 2 × QuaternionGroup M) :
    (hb.theta w : J ⧸ Subgroup.center J) ∈ b1D T L ↔ quaternionToDihedral 2 w.1 = 1 := by
  rw [hb.coe_theta, Subgroup.mul_mem_cancel_right _ (hb.thetaD_mem w.2), ← hb.thetaX_eq_one_iff]
  exact ⟨fun h => hb.eq_one_of_mem_X_of_mem_D (hb.thetaX_mem w.1) h, fun h => h ▸ one_mem _⟩

theorem ker_theta (hb : CaseB1 Q B T L M) : hb.theta.ker = (dihedralProdMap M).ker := by
  ext ⟨x, y⟩
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← OneMemClass.coe_eq_one, hb.coe_theta,
    MonoidHom.coe_prodMap, Prod.map_apply, Prod.mk_eq_one, ← hb.thetaX_eq_one_iff,
    ← hb.thetaD_eq_one_iff]
  constructor
  · intro h
    have hx : hb.thetaX x = 1 := hb.eq_one_of_mem_X_of_mem_D (hb.thetaX_mem x) (by
      rw [eq_inv_of_mul_eq_one_left h]
      exact (b1D T L).inv_mem (hb.thetaD_mem y))
    refine ⟨hx, ?_⟩
    rwa [hx, one_mul] at h
  · rintro ⟨hx, hy⟩
    rw [hx, hy, one_mul]

noncomputable def psi (hb : CaseB1 Q B T L M) : b1S T ≃* DihedralGroup 2 × DihedralGroup M :=
  (QuotientGroup.quotientKerEquivOfSurjective hb.theta hb.theta_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hb.ker_theta).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (dihedralProdMap_surjective hb.ne_zero)))

theorem psi_theta (hb : CaseB1 Q B T L M) (w : QuaternionGroup 2 × QuaternionGroup M) :
    hb.psi (hb.theta w) = dihedralProdMap M w := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective hb.theta hb.theta_surjective).symm
      (hb.theta w) = (w : _ ⧸ hb.theta.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [psi, MulEquiv.trans_apply, h1]
  rfl

theorem mem_X_iff_psi (hb : CaseB1 Q B T L M) (s : b1S T) :
    (s : J ⧸ Subgroup.center J) ∈ b1X T L ↔ (hb.psi s).2 = 1 := by
  obtain ⟨w, rfl⟩ := hb.theta_surjective s
  rw [hb.psi_theta, hb.coe_theta_mem_X_iff]
  rfl

theorem mem_D_iff_psi (hb : CaseB1 Q B T L M) (s : b1S T) :
    (s : J ⧸ Subgroup.center J) ∈ b1D T L ↔ (hb.psi s).1 = 1 := by
  obtain ⟨w, rfl⟩ := hb.theta_surjective s
  rw [hb.psi_theta, hb.coe_theta_mem_D_iff]
  rfl

theorem psi_symm_mem_X_iff (hb : CaseB1 Q B T L M) (w : DihedralGroup 2 × DihedralGroup M) :
    ((hb.psi.symm w : b1S T) : J ⧸ Subgroup.center J) ∈ b1X T L ↔ w.2 = 1 := by
  rw [hb.mem_X_iff_psi, MulEquiv.apply_symm_apply]

theorem psi_symm_mem_D_iff (hb : CaseB1 Q B T L M) (w : DihedralGroup 2 × DihedralGroup M) :
    ((hb.psi.symm w : b1S T) : J ⧸ Subgroup.center J) ∈ b1D T L ↔ w.1 = 1 := by
  rw [hb.mem_D_iff_psi, MulEquiv.apply_symm_apply]

theorem psi_symm_mem_X (hb : CaseB1 Q B T L M) (a : DihedralGroup 2) :
    ((hb.psi.symm (a, 1) : b1S T) : J ⧸ Subgroup.center J) ∈ b1X T L :=
  (hb.psi_symm_mem_X_iff _).mpr rfl

theorem psi_symm_mem_D (hb : CaseB1 Q B T L M) (b : DihedralGroup M) :
    ((hb.psi.symm (1, b) : b1S T) : J ⧸ Subgroup.center J) ∈ b1D T L :=
  (hb.psi_symm_mem_D_iff _).mpr rfl

theorem coe_psi_symm_eq_mul (hb : CaseB1 Q B T L M) (a : DihedralGroup 2)
    (b : DihedralGroup M) : ((hb.psi.symm (a, b) : b1S T) : J ⧸ Subgroup.center J) =
      ((hb.psi.symm (a, 1) : b1S T) : J ⧸ Subgroup.center J) *
        ((hb.psi.symm (1, b) : b1S T) : J ⧸ Subgroup.center J) := by
  rw [← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
