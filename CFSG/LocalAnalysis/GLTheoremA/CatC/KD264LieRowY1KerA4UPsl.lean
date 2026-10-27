module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4UDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Psl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def piU (K : Type) [Field K] (p f : ℕ) :
    unitarySU p f K 4 →* StatedProj (unitarySU p f K 4) :=
  QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (unitarySU p f K 4))

theorem scalar_of_piU_eq_one {x : unitarySU p f K 4} (hx : piU K p f x = 1) :
    ∃ u : Kˣ, (x : GL (Fin 4) K) = Matrix.GeneralLinearGroup.scalar (Fin 4) u := by
  have hx' : (x : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K := by
    have h := (QuotientGroup.eq_one_iff x).mp hx
    exact (Subgroup.mem_subgroupOf).mp h
  obtain ⟨u, hu⟩ := hx'
  exact ⟨u, hu.symm⟩

theorem pow_four_of_scalar {p f : ℕ} (h : UnitaryFieldData p f K) {u : Kˣ}
    (hu : Matrix.GeneralLinearGroup.scalar (Fin 4) u ∈ unitarySU p f K 4) :
    (u : K) ^ 4 = 1 := by
  rw [mem_unitarySU_iff h] at hu
  have hdet := hu.1
  have hdet' : ((Matrix.GeneralLinearGroup.scalar (Fin 4) u : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = (u : K) ^ 4 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
    simp [Finset.prod_const]
  rw [← hdet', hdet]

theorem eq_one_of_scalar_pow_three {p f : ℕ} (h : UnitaryFieldData p f K) {x : unitarySU p f K 4}
    (hx : (x : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K) (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨u, hu⟩ := hx
  have hu4 : (u : K) ^ 4 = 1 := pow_four_of_scalar h (by rw [hu]; exact x.2)
  have h3' : (x : GL (Fin 4) K) ^ 3 = 1 := by
    have := congrArg Subtype.val h3
    simpa using this
  rw [← hu, ← map_pow] at h3'
  have hu3 : (u : K) ^ 3 = 1 := by
    have hs := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) h3'
    have h00 := congrFun (congrFun hs 0) 0
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
    rw [Units.val_pow_eq_pow_val] at h00
    simpa using h00
  have hu1 : u = 1 := by
    apply Units.ext
    have h4 : (u : K) ^ 4 = (u : K) := by
      rw [show (u : K) ^ 4 = (u : K) * (u : K) ^ 3 by ring, hu3, mul_one]
    simp only [Units.val_one]
    rw [← h4, hu4]
  apply Subtype.ext
  rw [← hu, hu1, map_one]
  rfl

theorem piU_injOn_F0U (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) :
    ∀ x ∈ F0U h hdiv, piU K p f x = 1 → x = 1 := by
  intro x hx hpi
  obtain ⟨u, hu⟩ := scalar_of_piU_eq_one hpi
  exact eq_one_of_scalar_pow_three h ⟨u, hu.symm⟩ (F0U_pow_three h hdiv hx)

theorem commute_of_scalar {w : GL (Fin 4) K} (hw : w ∈ StatedScalars (Fin 4) K)
    (z : GL (Fin 4) K) : z * w = w * z := by
  rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hw
  exact Subgroup.mem_center_iff.mp hw z

theorem comm_of_piU_comm (h : UnitaryFieldData p f K) {x g : unitarySU p f K 4}
    (hg : g ^ 3 = 1) (hc : piU K p f x * piU K p f g = piU K p f g * piU K p f x) :
    x * g = g * x := by
  have hq : piU K p f (g * x) = piU K p f (x * g) := by
    rw [map_mul, map_mul]
    exact hc.symm
  have hmem : (g * x)⁻¹ * (x * g) ∈ (StatedScalars (Fin 4) K).subgroupOf (unitarySU p f K 4) :=
    QuotientGroup.eq.mp hq
  have hsc : (((g * x)⁻¹ * (x * g) : unitarySU p f K 4) : GL (Fin 4) K) ∈
      StatedScalars (Fin 4) K := Subgroup.mem_subgroupOf.mp hmem
  have hw3 : ((g * x)⁻¹ * (x * g)) ^ 3 = 1 := by
    apply pow_three_of_conj_aux (x := x) (w := (g * x)⁻¹ * (x * g)) hg (by group)
    intro z
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact commute_of_scalar hsc z.1
  have hw1 := eq_one_of_scalar_pow_three h hsc hw3
  exact (inv_mul_eq_one.mp hw1).symm

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
