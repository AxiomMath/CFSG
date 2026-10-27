module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.ABGDGroups.LinearStructure

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup Matrix CFSG CFSG.GorensteinWalter CFSG.ABGDGroups

section Residual

variable {X : Type*} [Group X]

theorem oPrimeResidual_normal_gen (p : ℕ) : (oPrimeResidual p X).Normal := by
  constructor
  intro n hn g
  unfold oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨k, ?_⟩
    rw [conj_pow, hk]
    group
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem mem_oPrimeResidual_of_pow {p k : ℕ} {x : X} (h : x ^ (p ^ k) = 1) :
    x ∈ oPrimeResidual p X :=
  Subgroup.subset_closure ⟨k, h⟩

end Residual

section PGLResidual

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem exists_involution_psl2 :
    ∃ y : PSL2 F, y ≠ 1 ∧ (Matrix.ProjectiveSpecialLinearGroup.toPGL y) ^ 2 = 1 := by
  let w₀ : SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  let u : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨QuotientGroup.mk' _ w₀, ?_, ?_⟩
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) (h u)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
    simp [w₀, u, Matrix.mul_apply, Fin.sum_univ_two] at h1
  · rw [← map_pow, ← map_pow]
    have : (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)) (w₀ ^ 2)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hw : ((w₀ ^ 2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
        rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [w₀, Matrix.mul_apply, Fin.sum_univ_two]
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hw]
      simp
    rw [this, map_one]

theorem oPrimeResidual_pgl2 (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    oPrimeResidual 2 (PGL2 F) = ⊤ := by
  classical
  have hF2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hFc : ringChar F ≠ 2 := by
    intro h
    apply hF2
    have : CharP F 2 := h ▸ ringChar.charP F
    exact_mod_cast CharP.cast_eq_zero F 2
  set W := oPrimeResidual 2 (PGL2 F) with hW
  have hWn : W.Normal := oPrimeResidual_normal_gen 2
  have hP : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ≤ W := by
    have hsimple : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    set N := W.comap (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) with hN
    have hNn : N.Normal := hWn.comap _
    rcases (haveI := hNn; hsimple.eq_bot_or_eq_top_of_normal N) with hbot | htop
    · exfalso
      obtain ⟨y, hy1, hy2⟩ := exists_involution_psl2 (F := F)
      have : y ∈ N := Subgroup.mem_comap.2 (mem_oPrimeResidual_of_pow (k := 1) (by simpa using hy2))
      rw [hbot] at this
      exact hy1 this
    · rintro _ ⟨y, rfl⟩
      have : y ∈ N := htop ▸ Subgroup.mem_top y
      exact this
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare hFc
  have hn0 : n ≠ 0 := fun h => hn (h ▸ IsSquare.zero)
  let G₀ : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -n, 0] (by
    simpa [Matrix.det_fin_two] using hn0)
  have hG₀det : (G₀ : Matrix (Fin 2) (Fin 2) F).det = n := by
    simp [G₀, Matrix.det_fin_two]
  have hs2 : (Matrix.ProjGenLinGroup.mk G₀) ^ 2 = 1 := by
    rw [← map_pow]
    have : G₀ ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-n) (neg_ne_zero.2 hn0)) := by
      apply Units.ext
      rw [pow_two, Units.val_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [G₀, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply]
    rw [this, Matrix.ProjGenLinGroup.mk_scalar]
  have hsW : Matrix.ProjGenLinGroup.mk G₀ ∈ W := mem_oPrimeResidual_of_pow (k := 1) (by simpa using hs2)
  have hsP : Matrix.ProjGenLinGroup.mk G₀ ∉
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.val_det_apply, hG₀det]
    exact hn
  have hsinv : (Matrix.ProjGenLinGroup.mk G₀)⁻¹ = Matrix.ProjGenLinGroup.mk G₀ := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hs2]
  rw [eq_top_iff]
  intro g _
  by_cases hg : g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  · exact hP hg
  · have hgs : g * Matrix.ProjGenLinGroup.mk G₀ ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      rw [mul_mem_range_toPGL_iff]
      exact ⟨fun h => absurd h hg, fun h => absurd h hsP⟩
    have : g = (g * Matrix.ProjGenLinGroup.mk G₀) * (Matrix.ProjGenLinGroup.mk G₀)⁻¹ := by group
    rw [this]
    exact W.mul_mem (hP hgs) (W.inv_mem hsW)

end PGLResidual

end CFSG.GH74.GLS.IVK
