module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Basic
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Open

private lemma exists_preimage_of_mulEquiv {C M : Type*} [Group C] [Group M] (e : C ≃* M)
    (h : ∃ a b : M, a ^ 3 * b ^ 3 ≠ b ^ 3 * a ^ 3) :
    ∃ a b : C, a ^ 3 * b ^ 3 ≠ b ^ 3 * a ^ 3 := by
  obtain ⟨a, b, hne⟩ := h
  refine ⟨e.symm a, e.symm b, fun hc => hne ?_⟩
  have := congrArg e hc
  simpa using this

private lemma exists_cube_not_comm_prod {M : Type*} [Group M] {σ τ : M}
    (hne : σ ^ 3 * τ ^ 3 ≠ τ ^ 3 * σ ^ 3) :
    ∃ a b : Multiplicative (ZMod 3) × M, a ^ 3 * b ^ 3 ≠ b ^ 3 * a ^ 3 := by
  refine ⟨(1, σ), (1, τ), fun h => hne ?_⟩
  simpa using congrArg Prod.snd h

namespace ThreeA5OrS5

theorem exists_cube_not_comm {C : Type*} [Group C] (h : ThreeA5OrS5 C) :
    ∃ a b : C, a ^ 3 * b ^ 3 ≠ b ^ 3 * a ^ 3 := by
  let σ : Equiv.Perm (Fin 5) := finRotate 5
  let τ : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3
  have hne : σ ^ 3 * τ ^ 3 ≠ τ ^ 3 * σ ^ 3 := by
    intro hc
    exact (by decide : ¬ (σ ^ 3 * τ ^ 3 = τ ^ 3 * σ ^ 3)) hc
  rcases h with h | h
  · obtain ⟨e⟩ := h
    let σA : ↥(alternatingGroup (Fin 5)) :=
      ⟨σ, by simpa [σ] using Equiv.Perm.finRotate_bit1_mem_alternatingGroup (n := 2)⟩
    let τA : ↥(alternatingGroup (Fin 5)) :=
      ⟨τ, by
        simp only [τ]
        exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
          ⟨0, 1, by decide, rfl⟩ ⟨2, 3, by decide, rfl⟩⟩
    have hneA : σA ^ 3 * τA ^ 3 ≠ τA ^ 3 * σA ^ 3 := by
      intro hc
      exact hne (by
        simpa [σ, τ, σA, τA, Subgroup.coe_pow, Subgroup.coe_mul] using
          congrArg Subtype.val hc)
    exact exists_preimage_of_mulEquiv e (exists_cube_not_comm_prod hneA)
  · obtain ⟨e⟩ := h
    exact exists_preimage_of_mulEquiv e (exists_cube_not_comm_prod hne)

end ThreeA5OrS5

namespace Cat3

private lemma cycMat_pow_three {K : Type} [Field K] :
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  rw [pow_three']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private lemma cycMat_det {K : Type} [Field K] :
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp

private lemma cycThree_form {K : Type} [Field K] {M : Matrix (Fin 3) (Fin 3) K}
    (h : M * !![0, 0, 1; 1, 0, 0; 0, 1, 0] = !![0, 0, 1; 1, 0, 0; 0, 1, 0] * M) :
    M = !![M 0 0, M 0 1, M 0 2; M 0 2, M 0 0, M 0 1; M 0 1, M 0 2, M 0 0] := by
  have h01 : M 0 1 = M 2 0 := by
    have e := congrFun (congrFun h 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using e
  have h02 : M 0 2 = M 2 1 := by
    have e := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using e
  have h00 : M 0 0 = M 2 2 := by
    have e := congrFun (congrFun h 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using e
  have h11 : M 1 1 = M 0 0 := by
    have e := congrFun (congrFun h 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using e
  have h12 : M 1 2 = M 0 1 := by
    have e := congrFun (congrFun h 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using e
  have h10 : M 1 0 = M 0 2 := by
    have e := congrFun (congrFun h 1) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using e
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h02, h00, h11, h12, h10]

private lemma commute_of_commute_cycThree {K : Type} [Field K]
    {M N : Matrix (Fin 3) (Fin 3) K}
    (hM : M * !![0, 0, 1; 1, 0, 0; 0, 1, 0] = !![0, 0, 1; 1, 0, 0; 0, 1, 0] * M)
    (hN : N * !![0, 0, 1; 1, 0, 0; 0, 1, 0] = !![0, 0, 1; 1, 0, 0; 0, 1, 0] * N) :
    M * N = N * M := by
  rw [cycThree_form hM, cycThree_form hN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private lemma conj_cube_eq_of_scalar {G : Type*} [Group G] {A C Z : G}
    (hZ : Commute A Z) (hconj : C⁻¹ * A * C = A * Z) (hZ3 : Z ^ 3 = 1) :
    A ^ 3 * C = C * A ^ 3 := by
  have h3 : C⁻¹ * A ^ 3 * C = A ^ 3 := by
    have hconj3 : (C⁻¹ * A * C) ^ 3 = A ^ 3 := by
      rw [hconj, hZ.mul_pow 3, hZ3, mul_one]
    calc C⁻¹ * A ^ 3 * C = (C⁻¹ * A * (C⁻¹)⁻¹) ^ 3 := by rw [conj_pow]; simp
      _ = (C⁻¹ * A * C) ^ 3 := by simp
      _ = A ^ 3 := hconj3
  have hC := congrArg (fun x => C * x) h3
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at hC
  exact hC

private lemma cycThree_cube_commute {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hcyc : CFSG.RankThree.PartTwo.Sec4.cycThree ∈ H) {l : H}
    (hl : QuotientGroup.mk l *
          (QuotientGroup.mk ⟨CFSG.RankThree.PartTwo.Sec4.cycThree, hcyc⟩ : StatedProj H) =
        QuotientGroup.mk ⟨CFSG.RankThree.PartTwo.Sec4.cycThree, hcyc⟩ *
          QuotientGroup.mk l) :
    (((l : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        !![0, 0, 1; 1, 0, 0; 0, 1, 0] =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] *
        (((l : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  let cycH : H := ⟨CFSG.RankThree.PartTwo.Sec4.cycThree, hcyc⟩
  have hl' : (QuotientGroup.mk (l * cycH) : StatedProj H) = QuotientGroup.mk (cycH * l) := by
    simpa [cycH] using hl
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff H (cycH * l) (l * cycH)).mp hl'.symm
  have hu' : ((l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        !![0, 0, 1; 1, 0, 0; 0, 1, 0] =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] * ((l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((u : K) • (1 : Matrix (Fin 3) (Fin 3) K)) := by
    simpa [cycH, Subgroup.coe_mul, Units.val_mul,
      CFSG.RankThree.PartTwo.Sec4.coe_cycThree] using hu
  have hdetu : ((u : K) • (1 : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
    have h := congrArg Matrix.det hu'
    simp only [Matrix.det_mul, hdet l l.2, cycMat_det, one_mul, mul_one] at h
    exact h.symm
  have hu3 : (u : K) ^ 3 = 1 := by
    have h := hdetu
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
    exact h
  have hgl : (l : GL (Fin 3) K) * CFSG.RankThree.PartTwo.Sec4.cycThree =
      CFSG.RankThree.PartTwo.Sec4.cycThree * (l : GL (Fin 3) K) *
        Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
    apply Units.ext
    simpa only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      CFSG.RankThree.PartTwo.Sec4.coe_cycThree, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal] using hu'
  have hAZcomm : Commute (l : GL (Fin 3) K) (Matrix.GeneralLinearGroup.scalar (Fin 3) u) :=
    (Matrix.GeneralLinearGroup.scalar_commute u (l : GL (Fin 3) K)).symm
  have hZ3 : (Matrix.GeneralLinearGroup.scalar (Fin 3) u) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
    simp only [smul_pow, hu3, one_pow, one_smul, Units.val_one]
  have hconj : CFSG.RankThree.PartTwo.Sec4.cycThree⁻¹ * (l : GL (Fin 3) K) *
        CFSG.RankThree.PartTwo.Sec4.cycThree =
      (l : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
    calc CFSG.RankThree.PartTwo.Sec4.cycThree⁻¹ * (l : GL (Fin 3) K) *
          CFSG.RankThree.PartTwo.Sec4.cycThree
        = CFSG.RankThree.PartTwo.Sec4.cycThree⁻¹ *
          ((l : GL (Fin 3) K) * CFSG.RankThree.PartTwo.Sec4.cycThree) := by rw [mul_assoc]
      _ = CFSG.RankThree.PartTwo.Sec4.cycThree⁻¹ *
          (CFSG.RankThree.PartTwo.Sec4.cycThree * (l : GL (Fin 3) K) *
            Matrix.GeneralLinearGroup.scalar (Fin 3) u) := by rw [hgl]
      _ = (l : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) u := by group
  have hmain : (l : GL (Fin 3) K) ^ 3 * CFSG.RankThree.PartTwo.Sec4.cycThree =
      CFSG.RankThree.PartTwo.Sec4.cycThree * (l : GL (Fin 3) K) ^ 3 :=
    conj_cube_eq_of_scalar hAZcomm hconj hZ3
  have hmat : (((l : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        !![0, 0, 1; 1, 0, 0; 0, 1, 0] =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] *
        (((l : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simpa only [Units.val_mul, CFSG.RankThree.PartTwo.Sec4.coe_cycThree] using
      congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K))) hmain
  exact hmat

namespace CentHyp

variable {L : Type*} [Group L]

theorem exists_cube_not_comm (h : CentHyp L) {x : L} (hx : orderOf x = 3) :
    ∃ a b : L, a * x = x * a ∧ b * x = x * b ∧ a ^ 3 * b ^ 3 ≠ b ^ 3 * a ^ 3 := by
  obtain ⟨a, b, hab⟩ := ThreeA5OrS5.exists_cube_not_comm (h x hx)
  refine ⟨(a : L), (b : L), ?_, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mp a.2
  · exact Subgroup.mem_centralizer_singleton_iff.mp b.2
  · intro hcon
    apply hab
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_mul] using hcon

end CentHyp

theorem false_of_cycThree_mem {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hcyc : CFSG.RankThree.PartTwo.Sec4.cycThree ∈ H) (hC : CentHyp (StatedProj H)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let cycH : H := ⟨CFSG.RankThree.PartTwo.Sec4.cycThree, hcyc⟩
  have hcyc3 : (cycH : GL (Fin 3) K) ^ 3 = 1 := by
    change (CFSG.RankThree.PartTwo.Sec4.cycThree : GL (Fin 3) K) ^ 3 = 1
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, CFSG.RankThree.PartTwo.Sec4.coe_cycThree,
      cycMat_pow_three, Units.val_one]
  have hcycNotScalar : (cycH : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := by
    rintro ⟨u, hu⟩
    have h := congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K)) 1 0) hu
    have hL : ((Matrix.GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
      rw [Matrix.GeneralLinearGroup.coe_scalar]; simp
    have hR : ((cycH : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 1 := by
      change (((CFSG.RankThree.PartTwo.Sec4.cycThree : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) 1 0 = 1
      rw [CFSG.RankThree.PartTwo.Sec4.coe_cycThree]; simp
    rw [hL, hR] at h
    exact zero_ne_one h
  have hx : orderOf (QuotientGroup.mk cycH : StatedProj H) = 3 :=
    orderOf_mk_eq_prime (p := 3) cycH (by rw [hcyc3]; exact Subgroup.one_mem _) hcycNotScalar
  obtain ⟨a, b, hax, hbx, hne⟩ := CentHyp.exists_cube_not_comm hC hx
  obtain ⟨l₁, hl₁⟩ := QuotientGroup.mk_surjective a
  obtain ⟨l₂, hl₂⟩ := QuotientGroup.mk_surjective b
  have hl₁' : (QuotientGroup.mk l₁ : StatedProj H) * QuotientGroup.mk cycH =
      QuotientGroup.mk cycH * QuotientGroup.mk l₁ := by rw [hl₁]; exact hax
  have hl₂' : (QuotientGroup.mk l₂ : StatedProj H) * QuotientGroup.mk cycH =
      QuotientGroup.mk cycH * QuotientGroup.mk l₂ := by rw [hl₂]; exact hbx
  have hmat : (((l₁ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((l₂ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((l₂ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((l₁ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    commute_of_commute_cycThree (cycThree_cube_commute hdet hcyc hl₁')
      (cycThree_cube_commute hdet hcyc hl₂')
  have hH : (l₁ ^ 3 : H) * (l₂ ^ 3 : H) = (l₂ ^ 3 : H) * (l₁ ^ 3 : H) := by
    apply Subtype.ext
    apply Units.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul] using hmat
  have hproj : a ^ 3 * b ^ 3 = b ^ 3 * a ^ 3 := by
    have := congrArg (fun x : H => (QuotientGroup.mk x : StatedProj H)) hH
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, hl₁, hl₂] using this
  exact hne hproj

theorem false_of_psl_three {K : Type} [Field K] [Finite K]
    (hC : CentHyp (StatedProj (StatedSL 3 K))) : False := by
  refine false_of_cycThree_mem (H := StatedSL 3 K) (fun h hh => ?_) ?_ hC
  · exact CFSG.Open.StatedAPI.det_of_mem_statedSL hh
  · rw [CFSG.Open.StatedAPI.mem_statedSL_iff, CFSG.RankThree.PartTwo.Sec4.coe_cycThree,
      Matrix.det_fin_three]
    simp

theorem false_of_psu_three {K : Type} [Field K] [Finite K] {q : ℕ} (hq : 1 ≤ q)
    (hC : CentHyp (StatedProj (StatedSU 3 q K))) : False := by
  refine false_of_cycThree_mem (H := StatedSU 3 q K) (fun h hh => ?_) ?_ hC
  · exact CFSG.Open.StatedAPI.det_of_mem_statedSU hh
  · apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [CFSG.RankThree.PartTwo.Sec4.coe_cycThree, Matrix.det_fin_three]
      simp
    · rw [CFSG.RankThree.PartTwo.Sec4.coe_cycThree]
      have hmap : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).map (· ^ q) =
          !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [zero_pow (by omega : q ≠ 0)]
      rw [hmap]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end Cat3

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan