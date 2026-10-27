module

public import CFSG.GH74.Filter.ClassicalOdd.Basic

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.Filter.ClassicalOdd Matrix

theorem exists_orderOf_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H : Subgroup (GL ι K)} (g : GL ι K) (hg : g ∈ H) {n : ℕ} (hn : g ^ n = 1)
    (hscal : ∀ (k : ℕ) (c : K), ((g ^ k : GL ι K) : Matrix ι ι K) = scalar ι c → n ∣ k) :
    ∃ x : StatedProj H, orderOf x = n := by
  refine ⟨(QuotientGroup.mk ⟨g, hg⟩ : StatedProj H), Nat.dvd_antisymm ?_ ?_⟩
  · refine orderOf_dvd_of_pow_eq_one ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h1 : ((⟨g, hg⟩ : H) ^ n : H) = 1 := Subtype.ext (by simpa using hn)
    rw [h1]
    exact one_mem _
  · have h := pow_orderOf_eq_one (QuotientGroup.mk ⟨g, hg⟩ : StatedProj H)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨c, hc⟩ := h
    refine hscal _ (c : K) ?_
    rw [← GeneralLinearGroup.coe_scalar, hc]
    rfl

section Diag

variable {K : Type} [Field K]

@[expose] def diag22 : GL (Fin 2) K × GL (Fin 2) K →* GL (Fin (2 + 2)) K :=
  MonoidHom.toHomUnits
    { toFun := fun p => diagBlock (p.1 : Matrix (Fin 2) (Fin 2) K) (p.2 : Matrix (Fin 2) (Fin 2) K)
      map_one' := by simp [diagBlock_one]
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul]
        exact (diagBlock_mul _ _ _ _).symm }

theorem coe_diag22 (X Y : GL (Fin 2) K) :
    (diag22 (X, Y) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
      diagBlock (X : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem det_diag22 (X Y : GL (Fin 2) K) :
    (diag22 (X, Y) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).det =
      (X : Matrix (Fin 2) (Fin 2) K).det * (Y : Matrix (Fin 2) (Fin 2) K).det := by
  rw [coe_diag22, det_diagBlock]

@[expose] def diagOneHom : Kˣ →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := fun e => diagonal ![1, (e : K)]
      map_one' := by
        rw [← diagonal_one]
        congr 1
        ext i
        fin_cases i <;> simp
      map_mul' := fun a b => by
        rw [diagonal_mul_diagonal]
        congr 1
        ext i
        fin_cases i <;> simp }

theorem coe_diagOneHom (e : Kˣ) :
    (diagOneHom e : Matrix (Fin 2) (Fin 2) K) = diagonal ![1, (e : K)] :=
  rfl

theorem diagOneHom_apply_zero_zero (e : Kˣ) :
    (diagOneHom e : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
  simp [coe_diagOneHom]

theorem det_diag22_det_inv (A : GL (Fin 2) K) :
    (diag22 (A, diagOneHom (Matrix.GeneralLinearGroup.det A)⁻¹) :
      Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).det = 1 := by
  rw [det_diag22, coe_diagOneHom, det_diagonal, Fin.prod_univ_two]
  simp [← Matrix.GeneralLinearGroup.val_det_apply]

theorem exists_orderOf_statedProj_diag {H : Subgroup (GL (Fin (2 + 2)) K)} (A : GL (Fin 2) K)
    (hmem : diag22 (A, diagOneHom (Matrix.GeneralLinearGroup.det A)⁻¹) ∈ H) :
    ∃ x : StatedProj H, orderOf x = orderOf A := by
  set d : Kˣ := Matrix.GeneralLinearGroup.det A with hd
  have hpow : ∀ k : ℕ, (diag22 (A, diagOneHom d⁻¹)) ^ k =
      diag22 (A ^ k, diagOneHom ((d⁻¹) ^ k)) := fun k => by
    rw [← map_pow, Prod.pow_mk, map_pow]
  refine exists_orderOf_statedProj _ hmem (n := orderOf A) ?_ ?_
  · have hdn : d ^ orderOf A = 1 := by rw [hd, ← map_pow, pow_orderOf_eq_one, map_one]
    rw [hpow, pow_orderOf_eq_one, inv_pow, hdn, inv_one, map_one]
    exact map_one _
  · intro k c h
    rw [hpow, coe_diag22] at h
    obtain ⟨hA, hB⟩ := eq_scalar_of_diagBlock_eq h
    have hc : c = 1 := by
      have := congrFun (congrFun hB 0) 0
      rw [diagOneHom_apply_zero_zero] at this
      simpa [scalar_apply, diagonal_apply] using this.symm
    rw [hc, map_one] at hA
    exact orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using hA))

end Diag

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
