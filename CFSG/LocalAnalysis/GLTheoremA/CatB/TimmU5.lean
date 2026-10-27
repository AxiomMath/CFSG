module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmOmega
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

open Matrix CFSG.Open Subgroup CFSG.LocalAnalysis.GLTheoremA.S8

variable {w : ℕ}

theorem comm_of_scalar_conj {n : ℕ} (a : GL (Fin n) F4) (T : Matrix (Fin n) (Fin n) F4)
    (hT : T * T = 1) (c : F4) (hn : 0 < n)
    (hc : (a : Matrix (Fin n) (Fin n) F4) * T = (c • (1 : Matrix (Fin n) (Fin n) F4)) *
      (T * (a : Matrix (Fin n) (Fin n) F4))) :
    (a : Matrix (Fin n) (Fin n) F4) * T = T * (a : Matrix (Fin n) (Fin n) F4) := by
  set A : Matrix (Fin n) (Fin n) F4 := (a : Matrix (Fin n) (Fin n) F4) with hA
  set B : Matrix (Fin n) (Fin n) F4 := ((a⁻¹ : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4) with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : B * A = 1 := by
    rw [hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc' : A * T = c • (T * A) := by rw [hc, smul_mul, one_mul]
  have hconj : A * T * B = c • T := by
    rw [hc', smul_mul, Matrix.mul_assoc, hAB, Matrix.mul_one]
  have hsq : (A * T * B) * (A * T * B) = 1 := by
    calc (A * T * B) * (A * T * B) = A * T * (B * A) * T * B := by simp only [Matrix.mul_assoc]
      _ = A * T * T * B := by rw [hBA, Matrix.mul_one]
      _ = A * (T * T) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT, Matrix.mul_one, hAB]
  rw [hconj] at hsq
  have hc2 : (c * c) • (1 : Matrix (Fin n) (Fin n) F4) = 1 := by
    have h : c • T * c • T = (c * c) • (T * T) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h, hT] at hsq
    exact hsq
  have hcc : c * c = 1 := by
    have h := congrFun (congrFun hc2 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using h
  have hc1 : c = 1 := eq_one_of_sq_eq_one (by rw [sq]; exact hcc)
  rw [hc', hc1, one_smul]

theorem scalar_val {n : ℕ} (c : F4ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) F4) :
      Matrix (Fin n) (Fin n) F4) = (c : F4) • 1 := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, Matrix.one_apply]

theorem mk_commute_iff {n : ℕ} [NeZero n] (A τ : GL (Fin n) F4)
    (hτ : (τ : Matrix (Fin n) (Fin n) F4) * (τ : Matrix (Fin n) (Fin n) F4) = 1) :
    ProjGenLinGroup.mk τ * ProjGenLinGroup.mk A = ProjGenLinGroup.mk A * ProjGenLinGroup.mk τ ↔
      A * τ = τ * A := by
  constructor
  · intro h
    rw [← map_mul, ← map_mul] at h
    have h' := QuotientGroup.eq.1 h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at h'
    obtain ⟨c, hc⟩ := h'
    have key : (τ * A) * ((τ * A)⁻¹ * (A * τ)) = A * τ := mul_inv_cancel_left _ _
    rw [← hc] at key
    have hkeyM : (A : Matrix (Fin n) (Fin n) F4) * (τ : Matrix (Fin n) (Fin n) F4) =
        (c : F4) • ((τ : Matrix (Fin n) (Fin n) F4) * (A : Matrix (Fin n) (Fin n) F4)) := by
      have := congrArg (fun g : GL (Fin n) F4 => (g : Matrix (Fin n) (Fin n) F4)) key
      simp only [Units.val_mul, scalar_val] at this
      rw [← this, Matrix.mul_smul, Matrix.mul_one]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    apply comm_of_scalar_conj A (τ : Matrix (Fin n) (Fin n) F4) hτ (c : F4) (NeZero.pos n)
    rw [hkeyM, Matrix.smul_mul, Matrix.one_mul]
  · intro h
    rw [← map_mul, ← map_mul, h]

theorem tau0_mem_statedSU : tau0GL w ∈ StatedSU (w + 2) 2 F4 := by
  rw [statedSU_two_eq]
  exact tau0GL_mem

theorem mk_mem_timmesfeldPSU (A : GL (Fin (w + 2)) F4) (hA : A ∈ StatedSU (w + 2) 2 F4) :
    ProjGenLinGroup.mk A ∈ timmesfeldPSU (w + 2) := by
  rw [CFSG.GF2Type.timmesfeldPSU_eq_map]
  exact Subgroup.mem_map_of_mem _ hA

theorem exists_mk_of_mem_timmesfeldPSU (y : ProjGenLinGroup (Fin (w + 2)) F4)
    (hy : y ∈ timmesfeldPSU (w + 2)) :
    ∃ A ∈ StatedSU (w + 2) 2 F4, ProjGenLinGroup.mk A = y := by
  rw [CFSG.GF2Type.timmesfeldPSU_eq_map] at hy
  obtain ⟨A, hA, hAy⟩ := Subgroup.mem_map.1 hy
  exact ⟨A, hA, hAy⟩

@[expose] noncomputable def tP (w : ℕ) : ↥(timmesfeldPSU (w + 2)) :=
  ⟨ProjGenLinGroup.mk (tau0GL w), mk_mem_timmesfeldPSU _ tau0_mem_statedSU⟩

@[expose] noncomputable def Cbar (w : ℕ) : Subgroup ↥(timmesfeldPSU (w + 2)) :=
  Subgroup.centralizer ({tP w} : Set ↥(timmesfeldPSU (w + 2)))

theorem stab_le_SU (w : ℕ) (x : GL (Fin (w + 2)) F4) (hx : x ∈ stabSU w) :
    x ∈ StatedSU (w + 2) 2 F4 := by
  rw [statedSU_two_eq]
  exact (Subgroup.mem_inf.1 hx).1

noncomputable def mkStab (w : ℕ) : ↥(stabSU w) →* ProjGenLinGroup (Fin (w + 2)) F4 :=
  ProjGenLinGroup.mk.comp (stabSU w).subtype

theorem mkStab_mem (x : ↥(stabSU w)) : mkStab w x ∈ timmesfeldPSU (w + 2) :=
  mk_mem_timmesfeldPSU _ (stab_le_SU w _ x.2)

noncomputable def psi0 (w : ℕ) : ↥(stabSU w) →* ↥(timmesfeldPSU (w + 2)) :=
  (mkStab w).codRestrict (timmesfeldPSU (w + 2)) mkStab_mem

theorem psi0_mem_Cbar (x : ↥(stabSU w)) : psi0 w x ∈ Cbar w := by
  unfold Cbar
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  apply Subtype.ext
  show ProjGenLinGroup.mk (tau0GL w) * ProjGenLinGroup.mk (x : GL (Fin (w + 2)) F4) =
    ProjGenLinGroup.mk (x : GL (Fin (w + 2)) F4) * ProjGenLinGroup.mk (tau0GL w)
  rw [mk_commute_iff _ _ (by rw [tau0GL_val, tau0_mul_self])]
  obtain ⟨-, -, μ, hμ⟩ := (mem_stabSU_iff (x : GL (Fin (w + 2)) F4)).1 x.2
  exact (mem_centralizer_tau0_iff _ (Subgroup.mem_inf.1 x.2).1).2 ⟨μ, hμ⟩

theorem psi0_surjective_onto_Cbar : ∀ y : ↥(Cbar w), ∃ x : ↥(stabSU w), psi0 w x = y.1 := by
  rintro ⟨y, hy⟩
  have hc := (Subgroup.mem_centralizer_iff.1 hy) (tP w) (Set.mem_singleton _)
  obtain ⟨A, hA, hAy⟩ := exists_mk_of_mem_timmesfeldPSU (y : ProjGenLinGroup (Fin (w + 2)) F4)
    y.2
  have hc' : ProjGenLinGroup.mk (tau0GL w) * ProjGenLinGroup.mk A =
      ProjGenLinGroup.mk A * ProjGenLinGroup.mk (tau0GL w) := by
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at this
    rw [hAy]
    exact this
  have hτ : (tau0GL w : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) * (tau0GL w : Matrix _ _ F4) = 1 := by
    rw [tau0GL_val, tau0_mul_self]
  have hcomm := (mk_commute_iff A (tau0GL w) hτ).1 hc'
  have hAsu : A ∈ suSub (w + 2) := by
    rw [← statedSU_two_eq]
    exact hA
  obtain ⟨μ, hμ⟩ := (mem_centralizer_tau0_iff A hAsu).1 hcomm
  have hAstab : A ∈ stabSU w := (mem_stabSU_iff A).2 ⟨hAsu.1, hAsu.2, μ, hμ⟩
  refine ⟨⟨A, hAstab⟩, ?_⟩
  apply Subtype.ext
  exact hAy

noncomputable def psi (w : ℕ) : ↥(stabSU w) →* ↥(Cbar w) :=
  (psi0 w).codRestrict (Cbar w) psi0_mem_Cbar

theorem psi_surjective (w : ℕ) : Function.Surjective (psi w) := by
  intro y
  obtain ⟨x, hx⟩ := psi0_surjective_onto_Cbar y
  exact ⟨x, Subtype.ext hx⟩

theorem psi_eq_one_mk (x : ↥(stabSU w)) (h : psi w x = 1) :
    ProjGenLinGroup.mk (x : GL (Fin (w + 2)) F4) = 1 := by
  have h1 : ((psi w x : ↥(Cbar w)) : ↥(timmesfeldPSU (w + 2))) = 1 := congrArg Subtype.val h
  have h2 : (psi0 w x : ↥(timmesfeldPSU (w + 2))) = 1 := h1
  exact congrArg Subtype.val h2

theorem mk_eq_one_mem_scalars (g : GL (Fin (w + 2)) F4) (h : ProjGenLinGroup.mk g = 1) :
    g ∈ StatedScalars (Fin (w + 2)) F4 := by
  have hker : g ∈ (ProjGenLinGroup.mk : GL (Fin (w + 2)) F4 →* _).ker := MonoidHom.mem_ker.2 h
  rw [ProjGenLinGroup.ker_mk, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hker
  exact hker

noncomputable def Phi (w : ℕ) : ↥(stabSU w) →* PGU w :=
  (mkY w).comp rhoHom

theorem rhoM_smul_one (c : F4) :
    rhoM (c • (1 : Matrix (Fin (w + 2)) (Fin (w + 2)) F4)) = c • (1 : Matrix (Fin w) (Fin w) F4) := by
  ext i j
  simp [rhoM, Matrix.one_apply, Wc, Matrix.smul_apply]

theorem rhoGL_mem_scalars_of_scalar (x : ↥(stabSU w))
    (h : (x : GL (Fin (w + 2)) F4) ∈ StatedScalars (Fin (w + 2)) F4) :
    rhoGL x ∈ StatedScalars (Fin w) F4 := by
  obtain ⟨c, hc⟩ := (mem_statedScalars_iff _).1 h
  rw [mem_statedScalars_iff]
  refine ⟨c, ?_⟩
  rw [rhoGL_val, hc, rhoM_smul_one]

theorem Phi_eq_one_of_mk_eq_one (x : ↥(stabSU w)) (h : ProjGenLinGroup.mk (x : GL (Fin (w + 2)) F4) = 1) :
    Phi w x = 1 := by
  unfold Phi
  rw [MonoidHom.comp_apply, mkY_eq_one_iff, rhoHom_val]
  exact rhoGL_mem_scalars_of_scalar x (mk_eq_one_mem_scalars _ h)

theorem psi_ker_le (w : ℕ) : (psi w).ker ≤ (Phi w).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  exact Phi_eq_one_of_mk_eq_one x (psi_eq_one_mk x hx)

noncomputable def fbar (w : ℕ) : ↥(Cbar w) →* PGU w :=
  (QuotientGroup.lift (psi w).ker (Phi w) (psi_ker_le w)).comp
    (QuotientGroup.quotientKerEquivOfSurjective (psi w) (psi_surjective w)).symm.toMonoidHom

theorem fbar_psi (x : ↥(stabSU w)) : fbar w (psi w x) = Phi w x := by
  unfold fbar
  have h : (QuotientGroup.quotientKerEquivOfSurjective (psi w) (psi_surjective w)).symm (psi w x) =
      (x : ↥(stabSU w) ⧸ (psi w).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [h]
  rfl

instance finite_GL_F4 (n : ℕ) : Finite (GL (Fin n) F4) := by
  haveI : Finite (Matrix (Fin n) (Fin n) F4) := inferInstance
  exact Finite.of_injective (fun g : GL (Fin n) F4 => (g : Matrix (Fin n) (Fin n) F4))
    (fun g h hgh => Units.ext hgh)

instance finite_PSU_ambient (w : ℕ) : Finite ↥(timmesfeldPSU (w + 2)) := by
  haveI : Finite (ProjGenLinGroup (Fin (w + 2)) F4) := by
    unfold ProjGenLinGroup
    infer_instance
  exact Subtype.finite

instance finite_Cbar (w : ℕ) : Finite ↥(Cbar w) := Subtype.finite

theorem coprime_ker_fbar (hw : 12 ≤ w) : Nat.Coprime 5 (Nat.card (fbar w).ker) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
  intro h5
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(fbar w).ker) 5 h5
  have hy5 : y ^ 5 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  set z : ↥(Cbar w) := (y : ↥(Cbar w)) with hz
  have hz5 : z ^ 5 = 1 := by
    have := congrArg Subtype.val hy5
    simpa using this
  have hfz : fbar w z = 1 := MonoidHom.mem_ker.1 y.2
  obtain ⟨a, ha⟩ := psi_surjective w z
  have ha5 : psi w (a ^ 5) = 1 := by rw [map_pow, ha, hz5]
  have hmk5 : ProjGenLinGroup.mk ((a ^ 5 : ↥(stabSU w)) : GL (Fin (w + 2)) F4) = 1 :=
    psi_eq_one_mk _ ha5
  have hsc5 : ((a ^ 5 : ↥(stabSU w)) : GL (Fin (w + 2)) F4) ∈ StatedScalars (Fin (w + 2)) F4 :=
    mk_eq_one_mem_scalars _ hmk5
  have h3 : ((a ^ 5 : ↥(stabSU w)) : GL (Fin (w + 2)) F4) ^ 3 = 1 := scalar_cube_eq_one _ hsc5
  have hA15 : (a ^ 5) ^ 3 = 1 := Subtype.ext (by simpa [Subgroup.coe_pow] using h3)
  set x : ↥(stabSU w) := a ^ 6 with hx
  have hx5 : x ^ 5 = 1 := by
    have key : (a ^ 6) ^ 5 = ((a ^ 5) ^ 3) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]
    rw [hx, key, hA15, one_pow]
  have hpsix : psi w x = z := by
    rw [hx, map_pow, ha]
    rw [pow_succ, hz5, one_mul]
  have hPhix : Phi w x = 1 := by
    rw [← fbar_psi, hpsix, hfz]
  have hsc : rhoGL x ∈ StatedScalars (Fin w) F4 := by
    unfold Phi at hPhix
    rw [MonoidHom.comp_apply, mkY_eq_one_iff] at hPhix
    exact hPhix
  obtain ⟨c, hc⟩ := (mem_statedScalars_iff _).1 hsc
  rw [rhoGL_val] at hc
  have hx5' : (x : GL (Fin (w + 2)) F4) ^ 5 = 1 := by
    have := congrArg Subtype.val hx5
    simpa [Subgroup.coe_pow] using this
  have hx1 : x = 1 := Subtype.ext (eq_one_of_pow_five (by omega : 0 < w) x.2 (c := (c : F4))
    c.ne_zero hc hx5')
  have hz1 : z = 1 := by
    rw [← hpsix, hx1, map_one]
  have hy1 : y = 1 := Subtype.ext (by
    have : (y : ↥(Cbar w)) = 1 := hz1
    simpa using this)
  rw [hy1, orderOf_one] at hy
  norm_num at hy

theorem fbar_surjective (w : ℕ) : Function.Surjective (fbar w) := by
  intro y
  obtain ⟨b, hb⟩ := mkY_surjective w y
  obtain ⟨a, ha⟩ := rhoHom_surjective b
  refine ⟨psi w a, ?_⟩
  rw [fbar_psi]
  unfold Phi
  rw [MonoidHom.comp_apply, ha, hb]

theorem quotient_core_iso (p : ℕ) [Fact p.Prime] {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (f : X →* Y) (hf : Function.Surjective f) (hk : Nat.Coprime p (Nat.card f.ker)) :
    Nonempty (X ⧸ CFSG.pPrimeCore p X ≃* Y ⧸ CFSG.pPrimeCore p Y) := by
  have hnd : ¬ p ∣ Nat.card f.ker := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hk
  obtain ⟨hcomap, hmap⟩ := CFSG.prime_complement_kernel_core_preimage f hf hnd
  let g : X →* Y ⧸ CFSG.pPrimeCore p Y := (QuotientGroup.mk' _).comp f
  have hg : Function.Surjective g := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨a, rfl⟩ := hf x
    exact ⟨a, rfl⟩
  have hker : g.ker = CFSG.pPrimeCore p X := by
    rw [← hcomap]
    ext x
    rw [MonoidHom.mem_ker]
    simp only [g, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_comap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

theorem isSimpleGroup_oPrimeRes_Cbar (hw : 12 ≤ w) :
    IsSimpleGroup ↥(oPrimeRes 5 (↥(Cbar w) ⧸ CFSG.pPrimeCore 5 ↥(Cbar w))) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := quotient_core_iso 5 (fbar w) (fbar_surjective w) (coprime_ker_fbar hw)
  have hT := isSimpleGroup_oPrimeRes_PGU hw
  have hK : Nat.Coprime 5 (Nat.card (CFSG.pPrimeCore 5 (PGU w))) :=
    CFSG.pPrimeCore_coprime_card
  have hY := CFSG.LocalAnalysis.GLTheoremA.Timm.isSimpleGroup_oPrimeRes_quotient hK hT
  exact CFSG.LocalAnalysis.GLTheoremA.Timm.isSimpleGroup_oPrimeRes_of_mulEquiv e hY


end CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

end
