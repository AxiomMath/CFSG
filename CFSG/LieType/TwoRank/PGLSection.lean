module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

import Mathlib.LinearAlgebra.Trace

public section

namespace CFSG.LieType.TwoRank

open Matrix
open Module

private lemma toLin'_scalar_mulVec {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]
    (a : F) (w : n → F) : Matrix.toLin' (Matrix.scalar n a) w = a • w := by
  rw [show Matrix.scalar n a = a • (1 : Matrix n n F) by
        rw [Matrix.scalar_apply, smul_eq_diagonal_mul, mul_one],
    Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]

private lemma toLin'_scalar {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]
    (a : F) :
    Matrix.toLin' (Matrix.scalar n a) = a • (1 : (n → F) →ₗ[F] (n → F)) := by
  apply LinearMap.ext
  intro w
  rw [toLin'_scalar_mulVec, LinearMap.smul_apply, Module.End.one_apply]

private lemma exists_invariant_line {F : Type*} [Field F] [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n] (hn : Fintype.card n = 4)
    {g₀ : GL n F} (hg₀ : ProjGenLinGroup.mk g₀ ≠ 1)
    (htr : (g₀ : Matrix n n F).trace ≠ 0)
    (lam : Fˣ) (hlam : (g₀ : Matrix n n F) ^ 2 = (lam : F) • 1) :
    ∃ L : Submodule F (n → F), finrank F L = 1 ∧
      (∀ y : GL n F, Commute y g₀ →
        ∀ v ∈ L, Matrix.toLin' (y : Matrix n n F) v ∈ L) := by
  classical
  set T : (n → F) →ₗ[F] (n → F) := Matrix.toLin' (g₀ : Matrix n n F) with hT
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (lam : F) (by norm_num : 0 < 2)
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : 2 ≠ 0)] at hμ
    exact lam.ne_zero hμ.symm
  have h2μ : 2 * μ ≠ 0 := mul_ne_zero h2 hμ0
  have hT2 : T * T = (μ ^ 2) • (1 : (n → F) →ₗ[F] (n → F)) := by
    rw [hT, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← sq, hlam,
      show (lam : F) • (1 : Matrix n n F) = Matrix.scalar n (lam : F) by
        rw [Matrix.scalar_apply, smul_eq_diagonal_mul, mul_one],
      toLin'_scalar, ← hμ]
  have hTT : ∀ v : n → F, T (T v) = (μ ^ 2) • v := by
    intro v
    have := congrArg (fun f : (n → F) →ₗ[F] (n → F) => f v) hT2
    simpa [Module.End.mul_apply] using this
  have hAnn_apply : ∀ v : n → F, (T - μ • 1) ((T + μ • 1) v) = 0 := by
    intro v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul, hTT v]
    rw [smul_sub, smul_smul, sq]
    abel
  have hAnn'_apply : ∀ v : n → F, (T + μ • 1) ((T - μ • 1) v) = 0 := by
    intro v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_sub, map_smul, hTT v]
    rw [smul_add, smul_smul, sq]
    abel
  set Vp : Submodule F (n → F) := LinearMap.ker (T - μ • 1) with hVp
  set Vm : Submodule F (n → F) := LinearMap.ker (T + μ • 1) with hVm
  set P : (n → F) →ₗ[F] (n → F) := (2 * μ)⁻¹ • (T + μ • 1) with hP
  have h2μP : (2 * μ) • P = T + μ • 1 := by
    rw [hP, smul_smul, mul_inv_cancel₀ h2μ, one_smul]
  have hPmem : ∀ v, P v ∈ Vp := by
    intro v
    rw [hVp, LinearMap.mem_ker, hP, LinearMap.smul_apply, map_smul, hAnn_apply v, smul_zero]
  have hPfix : ∀ v ∈ Vp, P v = v := by
    intro v hv
    rw [hVp, LinearMap.mem_ker] at hv
    have hTv : T v = μ • v := by
      have := hv
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      exact sub_eq_zero.mp this
    rw [hP, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, hTv, ← add_smul, ← two_mul, smul_smul, inv_mul_cancel₀ h2μ, one_smul]
  have hPproj : LinearMap.IsProj Vp P := ⟨hPmem, hPfix⟩
  have hkerP : LinearMap.ker P = Vm := by
    ext v
    rw [hVm, LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hv
      have h2' : (2 * μ)⁻¹ • ((T + μ • 1) v) = 0 := by
        rwa [hP, LinearMap.smul_apply] at hv
      rcases smul_eq_zero.mp h2' with h | h
      · exact absurd h (inv_ne_zero h2μ)
      · exact h
    · intro hv
      rw [hP, LinearMap.smul_apply, hv, smul_zero]
  have hcompl : IsCompl Vp Vm := by
    rw [← hkerP]
    exact hPproj.isCompl
  have hdim : finrank F Vp + finrank F Vm = 4 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl, Module.finrank_fintype_fun_eq_card, hn]
  have hT_ne : T + μ • 1 ≠ 0 := by
    intro h
    have hT_eq : T = -(μ • (1 : (n → F) →ₗ[F] (n → F))) := by
      rw [eq_neg_iff_add_eq_zero]
      exact h
    have hneg : -(μ • (1 : (n → F) →ₗ[F] (n → F))) = algebraMap F _ (-μ) := by
      rw [map_neg (algebraMap F ((n → F) →ₗ[F] (n → F)))]
      rfl
    have hmat : (g₀ : Matrix n n F) = Matrix.scalar n (-μ) := by
      have h2' := congrArg (LinearMap.toMatrix' (R := F)) hT_eq
      rw [hT, LinearMap.toMatrix'_toLin', hneg] at h2'
      rwa [LinearMap.toMatrix'_algebraMap] at h2'
    have hcenter : g₀ ∈ Subgroup.center (GL n F) := by
      rw [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      exact ⟨-μ, hmat.symm⟩
    exact hg₀ (ProjGenLinGroup.mk_eq_one.mpr hcenter)
  have hT_ne' : T - μ • 1 ≠ 0 := by
    intro h
    have hT_eq : T = μ • (1 : (n → F) →ₗ[F] (n → F)) := by
      rwa [sub_eq_zero] at h
    have hmat : (g₀ : Matrix n n F) = Matrix.scalar n μ := by
      have h2' := congrArg (LinearMap.toMatrix' (R := F)) hT_eq
      rw [hT, LinearMap.toMatrix'_toLin'] at h2'
      rw [show μ • (1 : (n → F) →ₗ[F] (n → F)) = algebraMap F _ μ by
            rw [Module.algebraMap_end_eq_smul_id, Module.End.one_eq_id]] at h2'
      rwa [LinearMap.toMatrix'_algebraMap] at h2'
    have hcenter : g₀ ∈ Subgroup.center (GL n F) := by
      rw [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      exact ⟨μ, hmat.symm⟩
    exact hg₀ (ProjGenLinGroup.mk_eq_one.mpr hcenter)
  have hVp_ne : Vp ≠ ⊥ := by
    intro hbot
    have hle : LinearMap.range (T + μ • 1) ≤ Vp := by
      rintro w ⟨v, rfl⟩
      rw [hVp, LinearMap.mem_ker]
      exact hAnn_apply v
    rw [hbot] at hle
    exact hT_ne (LinearMap.range_eq_bot.mp (le_bot_iff.mp hle))
  have hVm_ne : Vm ≠ ⊥ := by
    intro hbot
    have hle : LinearMap.range (T - μ • 1) ≤ Vm := by
      rintro w ⟨v, rfl⟩
      rw [hVm, LinearMap.mem_ker]
      exact hAnn'_apply v
    rw [hbot] at hle
    exact hT_ne' (LinearMap.range_eq_bot.mp (le_bot_iff.mp hle))
  have hT' : T = (2 * μ) • P - μ • 1 := by
    rw [h2μP, add_sub_cancel_right]
  have htrace : (g₀ : Matrix n n F).trace = μ * (2 * (finrank F Vp : F) - 4) := by
    have htrT : (g₀ : Matrix n n F).trace = LinearMap.trace F (n → F) T := by
      rw [hT, Matrix.trace_toLin'_eq]
    have h1 : LinearMap.trace F (n → F) ((2 * μ) • P)
        = (2 * μ) • LinearMap.trace F (n → F) P :=
      map_smul (LinearMap.trace F (n → F)) (2 * μ) P
    have h2 : LinearMap.trace F (n → F) (T + μ • 1)
        = LinearMap.trace F (n → F) T + LinearMap.trace F (n → F) (μ • 1) :=
      map_add (LinearMap.trace F (n → F)) T (μ • 1)
    have h3 : LinearMap.trace F (n → F) (μ • (1 : (n → F) →ₗ[F] (n → F)))
        = μ • LinearMap.trace F (n → F) 1 :=
      map_smul (LinearMap.trace F (n → F)) μ 1
    have htr : (2 * μ) • LinearMap.trace F (n → F) P
        = LinearMap.trace F (n → F) T + μ * (finrank F (n → F) : F) := by
      rw [← h1, h2μP, h2, h3, LinearMap.trace_one, smul_eq_mul]
    rw [hPproj.trace] at htr
    rw [Module.finrank_fintype_fun_eq_card, hn] at htr
    have hTval : LinearMap.trace F (n → F) T
        = (2 * μ) * (finrank F Vp : F) - μ * 4 := by
      rw [eq_sub_iff_add_eq]
      rw [smul_eq_mul] at htr
      exact htr.symm
    rw [htrT, hTval]
    ring
  have hfp_ne_zero : finrank F Vp ≠ 0 := by
    intro h
    exact hVp_ne (Submodule.subsingleton_iff_eq_bot.mp
      ((Module.finrank_eq_zero_iff_of_free (R := F) (M := Vp)).mp h))
  have hfm_ne_zero : finrank F Vm ≠ 0 := by
    intro h
    exact hVm_ne (Submodule.subsingleton_iff_eq_bot.mp
      ((Module.finrank_eq_zero_iff_of_free (R := F) (M := Vm)).mp h))
  have hfp_ne_two : finrank F Vp ≠ 2 := fun h =>
    htr (by rw [htrace, h]; ring)
  have hpres : ∀ (L : Submodule F (n → F)) (ν : F), L = LinearMap.ker (T - ν • 1) →
      ∀ y : GL n F, Commute y g₀ →
        ∀ v ∈ L, Matrix.toLin' (y : Matrix n n F) v ∈ L := by
    intro L ν hL y hy v hv
    rw [hL, LinearMap.mem_ker] at hv ⊢
    have hTv : T v = ν • v := by
      have := hv
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      exact sub_eq_zero.mp this
    have hmat : (y : Matrix n n F) * (g₀ : Matrix n n F)
        = (g₀ : Matrix n n F) * (y : Matrix n n F) := by
      have := congrArg (fun u : GL n F => (u : Matrix n n F)) hy
      simpa using this
    have hcommT : Matrix.toLin' (y : Matrix n n F) * T
        = T * Matrix.toLin' (y : Matrix n n F) := by
      rw [hT]
      simp only [Module.End.mul_eq_comp]
      rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hmat]
    have key : T (Matrix.toLin' (y : Matrix n n F) v)
        = Matrix.toLin' (y : Matrix n n F) (T v) := by
      rw [← Module.End.mul_apply, ← hcommT, Module.End.mul_apply]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, key, hTv, map_smul,
      sub_self]
  rcases eq_or_ne (finrank F Vp) 1 with h1 | h1
  · exact ⟨Vp, h1, fun y hy => hpres Vp μ hVp y hy⟩
  · have hVm' : Vm = LinearMap.ker (T - (-μ) • 1) := by
      have hS : T - (-μ) • (1 : (n → F) →ₗ[F] (n → F)) = T + μ • 1 := by
        apply LinearMap.ext
        intro v
        simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
          Module.End.one_apply, neg_smul, sub_neg_eq_add]
      rw [hVm, hS]
    have hVm1 : finrank F Vm = 1 := by omega
    exact ⟨Vm, hVm1, fun y hy => hpres Vm (-μ) hVm' y hy⟩

theorem exists_section_of_trace_ne_zero {F : Type*} [Field F] [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n] (hn : Fintype.card n = 4)
    (E : Subgroup (ProjGenLinGroup n F)) [IsElementaryAbelian 2 E] {g₀ : GL n F}
    (hg₀E : ProjGenLinGroup.mk g₀ ∈ E) (hg₀ : ProjGenLinGroup.mk g₀ ≠ 1)
    (htr : trace (g₀ : Matrix n n F) ≠ 0) :
    ∃ φ : E →* GL n F, ∀ e : E, ProjGenLinGroup.mk (φ e) = e := by
  classical
  have hcomm : ∀ y : GL n F, ProjGenLinGroup.mk y ∈ E → Commute y g₀ := by
    intro y hyE
    have hcy : Commute (ProjGenLinGroup.mk y) (ProjGenLinGroup.mk g₀) := by
      have := mul_comm' (⟨ProjGenLinGroup.mk y, hyE⟩ : E) ⟨ProjGenLinGroup.mk g₀, hg₀E⟩
      exact congrArg Subtype.val this
    have h1 : ProjGenLinGroup.mk (y * g₀ * y⁻¹ * g₀⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcy.eq]
      group
    have hcenter : y * g₀ * y⁻¹ * g₀⁻¹ ∈ Subgroup.center (GL n F) :=
      ProjGenLinGroup.mk_eq_one.mp h1
    obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcenter
    have hmat : ((y * g₀ * y⁻¹ : GL n F) : Matrix n n F)
        = Matrix.scalar n c * (g₀ : Matrix n n F) := by
      have hz : (y * g₀ * y⁻¹ : GL n F) = (y * g₀ * y⁻¹ * g₀⁻¹) * g₀ := by group
      calc ((y * g₀ * y⁻¹ : GL n F) : Matrix n n F)
          = (((y * g₀ * y⁻¹ * g₀⁻¹) * g₀ : GL n F) : Matrix n n F) :=
              congrArg (fun u : GL n F => (u : Matrix n n F)) hz
        _ = ((y * g₀ * y⁻¹ * g₀⁻¹ : GL n F) : Matrix n n F) * (g₀ : Matrix n n F) := by
              rw [GeneralLinearGroup.coe_mul]
        _ = Matrix.scalar n c * (g₀ : Matrix n n F) := by rw [hc]
    have htr_eq : (g₀ : Matrix n n F).trace = c * (g₀ : Matrix n n F).trace := by
      have h1' := Matrix.trace_units_conj y (g₀ : Matrix n n F)
      have h2' : ((y * g₀ * y⁻¹ : GL n F) : Matrix n n F).trace
          = (g₀ : Matrix n n F).trace := by simpa using h1'
      rw [hmat] at h2'
      have h3 : (Matrix.scalar n c * (g₀ : Matrix n n F)).trace
          = c * (g₀ : Matrix n n F).trace := by
        rw [Matrix.scalar_apply, ← smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]
      rw [h3] at h2'
      exact h2'.symm
    have hc1 : c = 1 := by
      have h : (c - 1) * (g₀ : Matrix n n F).trace = 0 := by
        rw [sub_mul, one_mul, ← htr_eq, sub_self]
      rcases mul_eq_zero.mp h with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' htr
    have hyg : y * g₀ * y⁻¹ = g₀ := by
      have hz : (y * g₀ * y⁻¹ : GL n F) = (y * g₀ * y⁻¹ * g₀⁻¹) * g₀ := by group
      have hz1 : (y * g₀ * y⁻¹ * g₀⁻¹ : GL n F) = 1 := by
        apply Units.ext
        rw [← hc, hc1]
        simp
      rw [hz, hz1, one_mul]
    refine (commute_iff_eq y g₀).mpr ?_
    calc y * g₀ = (y * g₀ * y⁻¹) * y := by group
      _ = g₀ * y := by rw [hyg]
  have hsq_center : g₀ ^ 2 ∈ Subgroup.center (GL n F) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (ProjGenLinGroup.mk g₀) hg₀E
  obtain ⟨lam, hlam⟩ : ∃ lam : Fˣ, GeneralLinearGroup.scalar n lam = g₀ ^ 2 := by
    have := hsq_center
    rwa [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at this
  have hlam_mat : (g₀ : Matrix n n F) ^ 2 = (lam : F) • 1 := by
    have h : ((g₀ ^ 2 : GL n F) : Matrix n n F) = Matrix.scalar n (lam : F) := by
      rw [← hlam]; simp
    rw [Matrix.scalar_apply] at h
    rw [show (g₀ : Matrix n n F) ^ 2 = diagonal (fun _ => (lam : F)) by
      rw [← h]; simp]
    rw [smul_eq_diagonal_mul, mul_one]
  obtain ⟨L, hLrank, hLinv⟩ := exists_invariant_line h2 hn hg₀ htr lam hlam_mat
  obtain ⟨v₀, hv₀_ne, hv₀_span⟩ := (finrank_eq_one_iff' (K := F) (V := L)).mp hLrank
  have hv₀_vec : (v₀ : n → F) ≠ 0 := fun h => hv₀_ne (Subtype.ext h)
  have hex : ∀ e : E, ∃! y : GL n F,
      ProjGenLinGroup.mk y = (e : ProjGenLinGroup n F) ∧
        Matrix.toLin' (y : Matrix n n F) (v₀ : n → F) = (v₀ : n → F) := by
    intro e
    obtain ⟨y, hy⟩ := ProjGenLinGroup.mk_surjective (e : ProjGenLinGroup n F)
    have hyE : ProjGenLinGroup.mk y ∈ E := by rw [hy]; exact e.property
    have hcy : Commute y g₀ := hcomm y hyE
    have hmem : Matrix.toLin' (y : Matrix n n F) (v₀ : n → F) ∈ L :=
      hLinv y hcy (v₀ : n → F) v₀.property
    obtain ⟨c, hc⟩ := hv₀_span ⟨Matrix.toLin' (y : Matrix n n F) (v₀ : n → F), hmem⟩
    have hc' : c • (v₀ : n → F) = Matrix.toLin' (y : Matrix n n F) (v₀ : n → F) := by
      simpa using congrArg Subtype.val hc
    have hinj : Function.Injective (Matrix.toLin' (y : Matrix n n F)) := by
      have hleft : Function.LeftInverse (Matrix.toLin' ((y⁻¹ : GL n F) : Matrix n n F))
          (Matrix.toLin' (y : Matrix n n F)) := by
        intro w
        rw [← Matrix.toLin'_mul_apply, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
          GeneralLinearGroup.coe_one, Matrix.toLin'_one]
        rfl
      exact hleft.injective
    have hc0 : c ≠ 0 := by
      intro hc0
      have hzero : Matrix.toLin' (y : Matrix n n F) (v₀ : n → F) = 0 := by
        rw [← hc', hc0, zero_smul]
      exact hv₀_vec (hinj (by rw [hzero, map_zero]))
    let u : Fˣ := Units.mk0 c⁻¹ (inv_ne_zero hc0)
    have hnorm : Matrix.toLin' ((y * GeneralLinearGroup.scalar n u : GL n F) : Matrix n n F)
        (v₀ : n → F) = (v₀ : n → F) := by
      rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar, Matrix.toLin'_mul_apply,
        toLin'_scalar_mulVec, map_smul, ← hc', smul_smul]
      rw [show (u : F) = c⁻¹ by rfl, inv_mul_cancel₀ hc0, one_smul]
    refine ExistsUnique.intro (y * GeneralLinearGroup.scalar n u) ⟨?_, hnorm⟩ ?_
    · rw [map_mul, hy, ProjGenLinGroup.mk_scalar, mul_one]
    · intro y' hy'
      obtain ⟨hy'mk, hy'v⟩ := hy'
      have hsame : ProjGenLinGroup.mk (y * GeneralLinearGroup.scalar n u)
          = ProjGenLinGroup.mk y' := by
        rw [map_mul, hy, ProjGenLinGroup.mk_scalar, mul_one, hy'mk]
      obtain ⟨u', hu'⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hsame
      have hcomputed : Matrix.toLin' (y' : Matrix n n F) (v₀ : n → F)
          = (u' : F) • (v₀ : n → F) := by
        rw [← hu', GeneralLinearGroup.coe_mul, Matrix.toLin'_mul_apply,
          GeneralLinearGroup.coe_scalar, toLin'_scalar_mulVec, map_smul, hnorm]
      have hu'1 : u' = 1 := by
        have hfix : (u' : F) • (v₀ : n → F) = (v₀ : n → F) := by
          rw [← hcomputed, hy'v]
        have hzero : ((u' : F) - 1) • (v₀ : n → F) = 0 := by
          rw [sub_smul, one_smul, hfix, sub_self]
        rcases smul_eq_zero.mp hzero with h | h
        · exact Units.ext (sub_eq_zero.mp h)
        · exact absurd h hv₀_vec
      rw [← hu', hu'1, map_one, mul_one]
  let f : E → GL n F := fun e => (hex e).choose
  have hf : ∀ e : E, ProjGenLinGroup.mk (f e) = (e : ProjGenLinGroup n F) ∧
      Matrix.toLin' (f e : Matrix n n F) (v₀ : n → F) = (v₀ : n → F) :=
    fun e => (hex e).choose_spec.1
  have hf_mul : ∀ a b : E, f (a * b) = f a * f b := by
    intro a b
    apply (hex (a * b)).unique (hf (a * b))
    refine ⟨?_, ?_⟩
    · rw [map_mul, (hf a).1, (hf b).1]
      rfl
    · rw [GeneralLinearGroup.coe_mul, Matrix.toLin'_mul_apply, (hf b).2, (hf a).2]
  exact ⟨MonoidHom.mk' f hf_mul, fun e => (hf e).1⟩

end CFSG.LieType.TwoRank
