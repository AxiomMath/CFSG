module

public import CFSG.ClassicalGroups.UnitaryFlag.LineSU2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryInv
public import CFSG.Quasithin.Background.OddCentralKerSylowTI

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts
open scoped Pointwise

variable {p f m : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 m K}

@[expose] noncomputable def hermPerp (h : UnitaryFieldData p f K)
    (L : Submodule K (Fin 3 → K)) : Submodule K (Fin 3 → K) :=
  L.orthogonalBilin (stdHermForm h 3)

@[simp] theorem mem_hermPerp {L : Submodule K (Fin 3 → K)} {v : Fin 3 → K} :
    v ∈ hermPerp h L ↔ ∀ a ∈ L, stdHermForm h 3 a v = 0 :=
  Submodule.mem_orthogonalBilin

variable {L L' : Submodule K (Fin 3 → K)}

theorem le_hermPerp_self (hL : L ∈ isotropicLines h 3) : L ≤ hermPerp h L := by
  obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_isotropicLines hL
  intro v hv
  rw [hLa] at hv ⊢
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [mem_hermPerp]
  intro x hx
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hx
  simp [map_smul, ha, smul_eq_mul]

theorem finrank_hermPerp (hL : L ∈ isotropicLines h 3) :
    Module.finrank K (hermPerp h L) = 2 := by
  obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_isotropicLines hL
  have hker : hermPerp h L = LinearMap.ker (stdHermForm h 3 a) := by
    rw [hermPerp, hLa, Submodule.orthogonalBilin_span_singleton]
  have hne : stdHermForm h 3 a ≠ 0 := by
    intro hzero
    apply ha0
    refine stdHermForm_separatingLeft h 3 a fun x => ?_
    rw [hzero]
    rfl
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero
    (K := K) (V₁ := Fin 3 → K) (f := stdHermForm h 3 a) hne
  rw [Module.finrank_fin_fun] at hdim
  rw [hker]
  omega

theorem inf_hermPerp_eq_bot (hL : L ∈ isotropicLines h 3) (hL' : L' ∈ isotropicLines h 3)
    (hne : L' ≠ L) : L ⊓ hermPerp h L' = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvL, hvP⟩ := Submodule.mem_inf.mp hv
  by_contra hv0
  have hLv : L = K ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hL.1 hvL hv0
  have horth : ∀ x ∈ L, ∀ y ∈ L', stdHermForm h 3 x y = 0 := by
    intro x hx y hy
    have hyv : stdHermForm h 3 y v = 0 := (mem_hermPerp.mp hvP) y hy
    have hvy : stdHermForm h 3 v y = 0 :=
      ((stdHermForm_isSymm h 3).eq_iff (x := v) (y := y)).mpr hyv
    rw [hLv] at hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [map_smul, hvy, smul_eq_mul]
  have hne' : (⟨L, hL⟩ : isotropicLines h 3) ≠ ⟨L', hL'⟩ := by
    intro hEq
    exact hne (congrArg Subtype.val hEq).symm
  obtain ⟨-, -, -, h4, -⟩ := unitary_isotropic_pair_orbits h (n := 3) (by norm_num)
  exact h4 rfl ⟨L, hL⟩ ⟨L', hL'⟩ hne' horth

@[expose] noncomputable def subOne (g : unitarySU 2 m K 3) :
    (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
  Matrix.mulVecLin (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) - LinearMap.id

@[simp] theorem subOne_apply (h : UnitaryFieldData 2 m K) (g : unitarySU 2 m K 3)
    (v : Fin 3 → K) : subOne g v = g • v - v := by
  rw [subOne, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply,
    unitarySU_smul_def h g v, Matrix.mulVecLin_apply]

theorem range_subOne_of_mem_isotropicTransvectionGroup (hL : L ∈ isotropicLines h 3)
    {x : unitarySU 2 m K 3} (hx : x ∈ isotropicTransvectionGroup h 3 L) (hx1 : x ≠ 1) :
    LinearMap.range (subOne x) = L := by
  obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_isotropicLines hL
  have haa : stdHermForm h 3 a a = 0 := ha
  have haL : a ∈ L := hLa.symm ▸ Submodule.mem_span_singleton_self a
  have hrange := (unitary_point_subgroup h hL haL ha0).2.2.1
  obtain ⟨c, rfl⟩ : ∃ c, ptTransvectionHom h haa c = x := by
    rw [← hrange] at hx
    exact hx
  have hval : ∀ v, subOne (ptTransvectionHom h haa c) v =
      ((c.toAdd : K) * stdHermForm h 3 a v) • a := by
    intro v
    rw [subOne_apply h, unitarySU_smul_def h, mulVecLin_ptTransvectionHom,
      hermTransvection_apply]
    abel
  have hc0 : (c.toAdd : K) ≠ 0 := by
    rintro h0
    apply hx1
    have hc : c = 1 := by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext h0
    rw [hc, map_one]
  rw [hLa]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [hval v]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  · intro x hx
    obtain ⟨lam, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨y, hy⟩ := exists_stdHermForm_eq_one h ha0
    refine ⟨((c.toAdd : K)⁻¹ * lam) • y, ?_⟩
    rw [hval, map_smul, hy, smul_eq_mul, mul_one]
    congr 1
    field_simp

theorem ker_subOne_of_mem_isotropicTransvectionGroup (hL : L ∈ isotropicLines h 3)
    {x : unitarySU 2 m K 3} (hx : x ∈ isotropicTransvectionGroup h 3 L) (hx1 : x ≠ 1) :
    LinearMap.ker (subOne x) = hermPerp h L := by
  obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_isotropicLines hL
  have haa : stdHermForm h 3 a a = 0 := ha
  have haL : a ∈ L := hLa.symm ▸ Submodule.mem_span_singleton_self a
  have hrange := (unitary_point_subgroup h hL haL ha0).2.2.1
  obtain ⟨c, rfl⟩ : ∃ c, ptTransvectionHom h haa c = x := by
    rw [← hrange] at hx
    exact hx
  have hval : ∀ v, subOne (ptTransvectionHom h haa c) v =
      ((c.toAdd : K) * stdHermForm h 3 a v) • a := by
    intro v
    rw [subOne_apply h, unitarySU_smul_def h, mulVecLin_ptTransvectionHom,
      hermTransvection_apply]
    abel
  have hc0 : (c.toAdd : K) ≠ 0 := by
    rintro h0
    apply hx1
    have hc : c = 1 := by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext h0
    rw [hc, map_one]
  ext v
  rw [LinearMap.mem_ker, hermPerp, hLa, Submodule.orthogonalBilin_span_singleton,
    LinearMap.mem_ker]
  constructor
  · intro hv
    rw [hval] at hv
    have hcoef : (c.toAdd : K) * stdHermForm h 3 a v = 0 := by
      rcases smul_eq_zero.mp hv with h | h
      · exact h
      · exact absurd h ha0
    exact (mul_eq_zero.mp hcoef).resolve_left hc0
  · intro hv
    rw [hval, hv, mul_zero, zero_smul]

end CFSG.ClassicalGroups.UnitaryFlag

end
