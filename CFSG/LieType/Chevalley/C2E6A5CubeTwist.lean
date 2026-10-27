module

public import CFSG.LieType.Chevalley.C2E6A5CubeFaithful
import all CFSG.Fischer.F4
public import CFSG.LieType.Chevalley.C2E6StandardBetaStar

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.ExteriorCube exteriorPower Set Matrix
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def J6 : Matrix (Fin 6) (Fin 6) K := Matrix.of fun i j => if j = Fin.rev i then 1 else 0

theorem J6_mul_J6 : J6 * J6 = 1 := by
  decide

theorem J6_transpose : J6ᵀ = J6 := by
  decide

theorem coeSL_mul (a b : SpecialLinearGroup (Fin 6) K) :
    ((a * b : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (a : Matrix (Fin 6) (Fin 6) K) * (b : Matrix (Fin 6) (Fin 6) K) := rfl

theorem coeSL_one :
    ((1 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := rfl

@[expose] def thetaFun (g : SpecialLinearGroup (Fin 6) K) : SpecialLinearGroup (Fin 6) K :=
  ⟨J6 * ((g⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ * J6, by
    rw [det_mul, det_mul, det_transpose, (g⁻¹).2, mul_one, ← det_mul, J6_mul_J6, det_one]⟩

theorem coe_thetaFun (g : SpecialLinearGroup (Fin 6) K) :
    (thetaFun g : Matrix (Fin 6) (Fin 6) K) =
      J6 * ((g⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ * J6 := rfl

theorem thetaFun_mul (g h : SpecialLinearGroup (Fin 6) K) :
    thetaFun (g * h) = thetaFun g * thetaFun h := by
  apply Subtype.ext
  change (thetaFun (g * h) : Matrix (Fin 6) (Fin 6) K) =
    (thetaFun g : Matrix (Fin 6) (Fin 6) K) * (thetaFun h : Matrix (Fin 6) (Fin 6) K)
  rw [coe_thetaFun, coe_thetaFun, coe_thetaFun, _root_.mul_inv_rev, coeSL_mul, transpose_mul]
  calc J6 * (((g⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ *
        ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ) * J6 =
      J6 * ((g⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ * (J6 * J6) *
        ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ * J6 := by
        rw [J6_mul_J6, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

@[expose] def thetaSL : SpecialLinearGroup (Fin 6) K →* SpecialLinearGroup (Fin 6) K :=
  MonoidHom.mk' thetaFun thetaFun_mul

theorem coe_thetaSL (g : SpecialLinearGroup (Fin 6) K) :
    (thetaSL g : Matrix (Fin 6) (Fin 6) K) =
      J6 * ((g⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ * J6 := rfl

theorem J6_transvection_J6 : ∀ (t : Fin 5) (c : K),
    J6 * (Matrix.transvection t.castSucc t.succ (-c))ᵀ * J6 =
      Matrix.transvection (Fin.rev t).castSucc (Fin.rev t).succ c ∧
    J6 * (Matrix.transvection t.succ t.castSucc (-c))ᵀ * J6 =
      Matrix.transvection (Fin.rev t).succ (Fin.rev t).castSucc c := by
  decide

theorem thetaSL_upAdj (t : Fin 5) (c : K) : thetaSL (upAdj t c) = upAdj (Fin.rev t) c := by
  apply Subtype.ext
  change (thetaSL (upAdj t c) : Matrix (Fin 6) (Fin 6) K) = (upAdj (Fin.rev t) c : Matrix _ _ K)
  rw [coe_thetaSL, upAdj, SpecialLinearGroup.transvection_inv]
  exact (J6_transvection_J6 t c).1

theorem thetaSL_downAdj (t : Fin 5) (c : K) : thetaSL (downAdj t c) = downAdj (Fin.rev t) c := by
  apply Subtype.ext
  change (thetaSL (downAdj t c) : Matrix (Fin 6) (Fin 6) K) =
    (downAdj (Fin.rev t) c : Matrix _ _ K)
  rw [coe_thetaSL, downAdj, SpecialLinearGroup.transvection_inv]
  exact (J6_transvection_J6 t c).2

abbrev barSL : SpecialLinearGroup (Fin 6) K →* SpecialLinearGroup (Fin 6) K :=
  SpecialLinearGroup.map barHom

theorem coe_barSL (g : SpecialLinearGroup (Fin 6) K) :
    (barSL g : Matrix (Fin 6) (Fin 6) K) = (g : Matrix (Fin 6) (Fin 6) K).map bar := rfl

theorem map_transvection_bar : ∀ (t : Fin 5) (c : K),
    (Matrix.transvection t.castSucc t.succ c).map bar =
      Matrix.transvection t.castSucc t.succ (bar c) ∧
    (Matrix.transvection t.succ t.castSucc c).map bar =
      Matrix.transvection t.succ t.castSucc (bar c) := by
  decide

theorem barSL_upAdj (t : Fin 5) (c : K) : barSL (upAdj t c) = upAdj t (bar c) :=
  Subtype.ext (map_transvection_bar t c).1

theorem barSL_downAdj (t : Fin 5) (c : K) : barSL (downAdj t c) = downAdj t (bar c) :=
  Subtype.ext (map_transvection_bar t c).2

theorem twistHom_id_eq (g : ModGL Tag.E6 K) :
    twistHom TwistTag.E6 K (RingHom.id K) g = diagE6GL * g * diagE6GL⁻¹ := by
  have h : Units.map (entrywiseHom (RingHom.id K)) g = g :=
    Units.ext (entrywise_id (g : Module.End K (RootModule Tag.E6 K)))
  change diagE6GL * Units.map (entrywiseHom (RingHom.id K)) g * diagE6GL⁻¹ = _
  rw [h]

theorem diagE6GL_conj_xUnit
    (i : Fin Tag.E6.rank) (c : K) :
    diagE6GL * xUnit Tag.E6 K i c * diagE6GL⁻¹ = xUnit Tag.E6 K (TwistTag.E6.perm i) c :=
  (twistHom_id_eq _).symm.trans (twistHom_xUnit TwistTag.E6 K (RingHom.id K) i c)

theorem diagE6GL_conj_yUnit
    (i : Fin Tag.E6.rank) (c : K) :
    diagE6GL * yUnit Tag.E6 K i c * diagE6GL⁻¹ = yUnit Tag.E6 K (TwistTag.E6.perm i) c :=
  (twistHom_id_eq _).symm.trans (twistHom_yUnit TwistTag.E6 K (RingHom.id K) i c)

theorem perm_jA_val : ∀ t : Fin 5, (TwistTag.E6.perm (jA t)).val = (jA (Fin.rev t)).val := by
  decide

theorem perm_jA (t : Fin 5) : TwistTag.E6.perm (jA t) = jA (Fin.rev t) := Fin.ext (perm_jA_val t)

theorem conj_mem_groupA
    {g : ModGL Tag.E6 K} (hg : g ∈ groupA) :
    diagE6GL * g * diagE6GL⁻¹ ∈ groupA := by
  have hle : groupA ≤ groupA.comap (MulAut.conj diagE6GL).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        diagE6GL_conj_xUnit, perm_jA]
      exact xUnit_mem_groupA _ c
    · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        diagE6GL_conj_yUnit, perm_jA]
      exact yUnit_mem_groupA _ c
  exact hle hg

@[expose] def conjA :
    groupA →* groupA :=
  MonoidHom.mk' (fun g => ⟨diagE6GL * g * diagE6GL⁻¹, conj_mem_groupA g.2⟩) fun g h =>
    Subtype.ext (by
      change diagE6GL * ((g : ModGL Tag.E6 K) * h) * diagE6GL⁻¹ =
        diagE6GL * g * diagE6GL⁻¹ * (diagE6GL * h * diagE6GL⁻¹)
      group)

theorem coe_conjA
    (g : groupA) :
    ((conjA g : groupA) : ModGL Tag.E6 K) = diagE6GL * g * diagE6GL⁻¹ := rfl

@[expose] def betaA :
    groupA →* groupA :=
  MonoidHom.mk' (fun g => ⟨betaGL g, betaGL_mem_subsystemGroup g.2⟩) fun g h =>
    Subtype.ext (map_mul betaGL (g : ModGL Tag.E6 K) h)

theorem coe_betaA
    (g : groupA) : ((betaA g : groupA) : ModGL Tag.E6 K) = betaGL g := rfl

theorem liftA_upAdj
    (t : Fin 5) (c : K) :
    liftA (upAdj t c) = ⟨xUnit Tag.E6 K (jA t) c, xUnit_mem_groupA t c⟩ :=
  liftA_eq_of_psiA_eq (psiA_xUnit t c)

theorem liftA_downAdj
    (t : Fin 5) (c : K) :
    liftA (downAdj t c) = ⟨yUnit Tag.E6 K (jA t) c, yUnit_mem_groupA t c⟩ :=
  liftA_eq_of_psiA_eq (psiA_yUnit t c)

theorem psiA_conjA_liftA :
    psiA.comp (conjA.comp liftA) = (cubeHom (K := K)).comp thetaSL := by
  refine MonoidHom.eq_of_eqOn_dense closure_adjSet ?_
  rintro _ ⟨t, c, rfl | rfl⟩
  · simp only [MonoidHom.comp_apply, liftA_upAdj, thetaSL_upAdj]
    rw [← psiA_xUnit]
    congr 1
    apply Subtype.ext
    rw [coe_conjA, diagE6GL_conj_xUnit, perm_jA]
  · simp only [MonoidHom.comp_apply, liftA_downAdj, thetaSL_downAdj]
    rw [← psiA_yUnit]
    congr 1
    apply Subtype.ext
    rw [coe_conjA, diagE6GL_conj_yUnit, perm_jA]

theorem psiA_betaA_liftA
    : psiA.comp (betaA.comp liftA) = (cubeHom (K := K)).comp barSL := by
  refine MonoidHom.eq_of_eqOn_dense closure_adjSet ?_
  rintro _ ⟨t, c, rfl | rfl⟩
  · simp only [MonoidHom.comp_apply, liftA_upAdj, barSL_upAdj]
    rw [← psiA_xUnit]
    congr 1
    apply Subtype.ext
    rw [coe_betaA, betaGL_xUnit]
    rfl
  · simp only [MonoidHom.comp_apply, liftA_downAdj, barSL_downAdj]
    rw [← psiA_yUnit]
    congr 1
    apply Subtype.ext
    rw [coe_betaA, betaGL_yUnit]
    rfl

theorem psiA_conjA
    {g : groupA} {h : SpecialLinearGroup (Fin 6) K} (hgh : psiA g = cubeHom h) :
    psiA (conjA g) = cubeHom (thetaSL h) := by
  rw [← liftA_eq_of_psiA_eq hgh]
  exact congrArg (fun F => F h) psiA_conjA_liftA

theorem psiA_betaA
    {g : groupA} {h : SpecialLinearGroup (Fin 6) K} (hgh : psiA g = cubeHom h) :
    psiA (betaA g) = cubeHom (barSL h) := by
  rw [← liftA_eq_of_psiA_eq hgh]
  exact congrArg (fun F => F h) psiA_betaA_liftA

abbrev tauSL : SpecialLinearGroup (Fin 6) K →* SpecialLinearGroup (Fin 6) K :=
  thetaSL.comp barSL

@[expose] def SU6 : Subgroup (SpecialLinearGroup (Fin 6) K) :=
  MonoidHom.eqLocus tauSL (MonoidHom.id _)

theorem tauSL_tauSL (h : SpecialLinearGroup (Fin 6) K) : tauSL (tauSL h) = h := by
  have key : tauSL.comp tauSL = MonoidHom.id (SpecialLinearGroup (Fin 6) K) := by
    refine MonoidHom.eq_of_eqOn_dense closure_adjSet ?_
    rintro _ ⟨t, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, barSL_upAdj, thetaSL_upAdj,
        Fin.rev_rev, bar_bar]
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, barSL_downAdj, thetaSL_downAdj,
        Fin.rev_rev, bar_bar]
  exact congrArg (fun F => F h) key

theorem scalar_facts : ∀ c : Kˣ,
    (scalar (Fin 6) (c : K)).map bar * scalar (Fin 6) (((c ^ 2)⁻¹ : Kˣ) : K) = 1 ∧
      J6 * (scalar (Fin 6) (((c ^ 2)⁻¹ : Kˣ) : K))ᵀ * J6 = scalar (Fin 6) (c : K) := by
  decide

theorem tauSL_of_mem_scalars {z : SpecialLinearGroup (Fin 6) K}
    (hz : z ∈ LinearFlag.scalars 6 K) : tauSL z = z := by
  obtain ⟨c, hc6, hcz⟩ := LinearFlag.mem_scalars.mp hz
  have hc2 : ((c ^ 2)⁻¹) ^ 6 = 1 := by rw [inv_pow, ← pow_mul, show 2 * 6 = 6 * 2 from rfl,
    pow_mul, hc6, one_pow, inv_one]
  have hinv : (barSL z)⁻¹ = LinearFlag.scalarElement ((c ^ 2)⁻¹) hc2 := by
    refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
    change (barSL z : Matrix (Fin 6) (Fin 6) K) *
      (LinearFlag.scalarElement ((c ^ 2)⁻¹) hc2 : Matrix (Fin 6) (Fin 6) K) = 1
    rw [coe_barSL, hcz, LinearFlag.coe_scalarElement]
    exact (scalar_facts c).1
  apply Subtype.ext
  change (thetaSL (barSL z) : Matrix (Fin 6) (Fin 6) K) = (z : Matrix (Fin 6) (Fin 6) K)
  rw [coe_thetaSL, hinv, LinearFlag.coe_scalarElement, hcz]
  exact (scalar_facts c).2

theorem mem_SU6_iff (h : SpecialLinearGroup (Fin 6) K) :
    h ∈ SU6 ↔ ((h : Matrix (Fin 6) (Fin 6) K).map bar)ᵀ * J6 * (h : Matrix (Fin 6) (Fin 6) K) =
      J6 := by
  set X : Matrix (Fin 6) (Fin 6) K := (barSL h : Matrix (Fin 6) (Fin 6) K)
  set Y : Matrix (Fin 6) (Fin 6) K :=
    (((barSL h)⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  have hYX : Y * X = 1 := by
    change (((barSL h)⁻¹ * barSL h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1
    rw [inv_mul_cancel]
    rfl
  have hXY : X * Y = 1 := by
    change ((barSL h * (barSL h)⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1
    rw [mul_inv_cancel]
    rfl
  have hmem : h ∈ SU6 ↔ J6 * Yᵀ * J6 = (h : Matrix (Fin 6) (Fin 6) K) := by
    change tauSL h = h ↔ _
    constructor
    · intro e
      exact congrArg (fun g : SpecialLinearGroup (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) e
    · intro e
      exact Subtype.ext e
  rw [hmem, ← coe_barSL]
  change J6 * Yᵀ * J6 = (h : Matrix (Fin 6) (Fin 6) K) ↔
    Xᵀ * J6 * (h : Matrix (Fin 6) (Fin 6) K) = J6
  constructor
  · intro e
    rw [← e]
    calc Xᵀ * J6 * (J6 * Yᵀ * J6) = Xᵀ * (J6 * J6) * Yᵀ * J6 := by
          simp only [Matrix.mul_assoc]
      _ = (Y * X)ᵀ * J6 := by rw [J6_mul_J6, Matrix.mul_one, transpose_mul]
      _ = J6 := by rw [hYX, transpose_one, Matrix.one_mul]
  · intro e
    calc J6 * Yᵀ * J6 = J6 * Yᵀ * (Xᵀ * J6 * (h : Matrix (Fin 6) (Fin 6) K)) := by rw [e]
      _ = J6 * (X * Y)ᵀ * J6 * (h : Matrix (Fin 6) (Fin 6) K) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (h : Matrix (Fin 6) (Fin 6) K) := by
          rw [hXY, transpose_one, Matrix.mul_one, J6_mul_J6, Matrix.one_mul]

theorem tauSL_eq_of_cubeHom_eq {h : SpecialLinearGroup (Fin 6) K}
    (e : cubeHom (tauSL h) = cubeHom h) : tauSL h = h := by
  rw [eq_comm, cubeHom_eq_cubeHom_iff] at e
  set z := h⁻¹ * tauSL h with hz
  have hτz : tauSL z = z := tauSL_of_mem_scalars e
  have hzh : tauSL h = h * z := by rw [hz, mul_inv_cancel_left]
  have hz2 : z * z = 1 := by
    have h1 := tauSL_tauSL h
    rw [hzh, map_mul, hzh, hτz, mul_assoc] at h1
    exact mul_left_cancel (h1.trans (mul_one h).symm)
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨c, -, hcz⟩ := LinearFlag.mem_scalars.mp e
    have hzc : z = LinearFlag.scalarElement c (by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul,
      units_pow_three, one_pow]) := Subtype.ext hcz
    rw [hzc]
    apply Subtype.ext
    change ((LinearFlag.scalarElement c _ : SpecialLinearGroup (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) ^ 3 = 1
    rw [LinearFlag.coe_scalarElement, ← map_pow, ← Units.val_pow_eq_pow_val, units_pow_three,
      Units.val_one, map_one]
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2, inv_one, one_mul]
  rw [hzh, hz1, mul_one]

theorem groupA_le_adjointGroup
    : groupA ≤ adjointGroup Tag.E6 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  · exact xUnit_mem_adjointGroup i c
  · exact yUnit_mem_adjointGroup i c

theorem mem_stdFixedGroup_iff
    {g : groupA} {h : SpecialLinearGroup (Fin 6) K}
    (hgh : psiA g = cubeHom h) : (g : ModGL Tag.E6 K) ∈ stdFixedGroup ↔ h ∈ SU6 := by
  have hF : twistHom TwistTag.E6 K barHom (g : ModGL Tag.E6 K) =
      ((conjA (betaA g) : groupA) : ModGL Tag.E6 K) := by
    rw [twistHom_eq_conj, coe_conjA, coe_betaA]
  have hψ := psiA_conjA (psiA_betaA hgh)
  constructor
  · intro hΓ
    have hfix := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).mp hΓ).2
    have e : conjA (betaA g) = g := Subtype.ext (hF.symm.trans hfix)
    change tauSL h = h
    refine tauSL_eq_of_cubeHom_eq ?_
    rw [MonoidHom.comp_apply, ← hψ, e, hgh]
  · intro hSU
    have e : psiA (conjA (betaA g)) = psiA g := by
      rw [hψ, hgh]
      exact congrArg cubeHom hSU
    have e' : conjA (betaA g) = g := psiA_injective e
    refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).mpr
      ⟨groupA_le_adjointGroup g.2, ?_⟩
    rw [hF, e']

theorem map_psiA_stdFixedGroup :
    (stdFixedGroup.subgroupOf groupA).map psiA = SU6.map (cubeHom (K := K)) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨h, hh⟩ : psiA g ∈ (cubeHom (K := K)).range := by
      rw [← range_psiA]
      exact ⟨g, rfl⟩
    exact ⟨h, (mem_stdFixedGroup_iff hh.symm).mp hg, hh⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact ⟨liftA h, (mem_stdFixedGroup_iff (psiA_liftA h)).mpr hh, psiA_liftA h⟩

theorem scalars_le_SU6 : LinearFlag.scalars 6 K ≤ SU6 := fun _ hz => tauSL_of_mem_scalars hz

theorem scalars_le_diagSL : LinearFlag.scalars 6 K ≤ diagSL := by
  intro z hz
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp hz
  exact mem_diagSL.mpr ⟨fun _ => (c : K), hc⟩

end CFSG.LieType.Chevalley.C2E6Std
