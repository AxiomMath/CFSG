module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeNormal
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix
open scoped commutatorElement

variable {F : Type*} [Field F]

theorem conjUnit_conjUnit_inv {n : ℕ} (P : GL (Fin n) F) (g : SpecialLinearGroup (Fin n) F) :
    conjUnit P (conjUnit P⁻¹ g) = g := by
  apply Subtype.ext
  simp only [conjUnit_coe, Matrix.mul_assoc, inv_inv, Units.mul_inv, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem diagSL_mul_diagSL_comm (a b d a' b' d' : F) (h : a * b * d = 1) (h' : a' * b' * d' = 1) :
    diagSL a b d h * diagSL a' b' d' h' = diagSL a' b' d' h' * diagSL a b d h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem closure_centralizers_psl_of_heisenberg [Finite F]
    {E : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F)} {x y : SpecialLinearGroup (Fin 3) F}
    (hxE : toPSL x ∈ E) (hyE : toPSL y ∈ E)
    (hxZ : x ∉ Subgroup.center (SpecialLinearGroup (Fin 3) F))
    (hyZ : y ∉ Subgroup.center (SpecialLinearGroup (Fin 3) F)) {P : GL (Fin 3) F} {ω ξ : F}
    (hξ : ξ * (ξ * ω) * (ξ * ω ^ 2) = 1) (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (hy : conjUnit P⁻¹ y = diagSL ξ (ξ * ω) (ξ * ω ^ 2) hξ) (hx : conjUnit P⁻¹ x = shiftSL)
    (hcard : 4 < Nat.card F) :
    Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin 3) F |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
  set C := Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin 3) F |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} with hC
  set K : Subgroup (SpecialLinearGroup (Fin 3) F) := C.comap toPSL with hK
  have hy' : y = conjUnit P (diagSL ξ (ξ * ω) (ξ * ω ^ 2) hξ) := by
    rw [← hy, conjUnit_conjUnit_inv]
  have hx' : x = conjUnit P shiftSL := by rw [← hx, conjUnit_conjUnit_inv]
  have hdiag : ∀ (a b d : F) (h : a * b * d = 1), conjUnit P (diagSL a b d h) ∈ K := by
    intro a b d h
    refine Subgroup.subset_closure ⟨toPSL y, hyE, fun h1 =>
      hyZ (mem_center_iff_toPSL_eq_one.2 h1), ?_⟩
    have hc : conjUnit P (diagSL a b d h) * y = y * conjUnit P (diagSL a b d h) := by
      rw [hy', ← map_mul, ← map_mul, diagSL_mul_diagSL_comm]
    rw [← map_mul, ← map_mul, hc]
  have hcirc : ∀ (a b d : F) (h : a ^ 3 + b ^ 3 + d ^ 3 - 3 * a * b * d = 1),
      conjUnit P (circSL a b d h) ∈ K := by
    intro a b d h
    refine Subgroup.subset_closure ⟨toPSL x, hxE, fun h1 =>
      hxZ (mem_center_iff_toPSL_eq_one.2 h1), ?_⟩
    have hc : conjUnit P (circSL a b d h) * x = x * conjUnit P (circSL a b d h) := by
      rw [hx', ← map_mul, ← map_mul, circSL_mul_shiftSL]
    rw [← map_mul, ← map_mul, hc]
  have htop : K.comap (conjUnit P) = ⊤ :=
    eq_top_of_torus_circ (K := K.comap (conjUnit P)) (fun a b d h => hdiag a b d h)
      (fun a b d h => hcirc a b d h) hω hω1 hcard
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have h1 : conjUnit P⁻¹ g ∈ K.comap (conjUnit P) := htop ▸ Subgroup.mem_top _
    rwa [Subgroup.mem_comap, conjUnit_conjUnit_inv] at h1
  rw [eq_top_iff]
  intro k _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ k
  have : g ∈ K := hKtop ▸ Subgroup.mem_top g
  exact this

theorem closure_centralizers_psl_nonab_three [Finite F] (hcard : 4 < Nat.card F)
    (E : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hnc : ∃ x y : SpecialLinearGroup (Fin 3) F, toPSL x ∈ E ∧ toPSL y ∈ E ∧ x * y ≠ y * x) :
    Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin 3) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  obtain ⟨x, y, hxE, hyE, hxy⟩ := hnc
  have hyx : ⁅y, x⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
    rw [mem_center_iff_toPSL_eq_one, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hyE _ hxE)
  have hx3 : x ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
    rw [mem_center_iff_toPSL_eq_one, map_pow]; exact hexp _ hxE
  obtain ⟨P, ω, ξ, hξ, hω, hω1, hy, hx⟩ := exists_heisenberg_basis hyx hxy hx3
  have hxZ : x ∉ Subgroup.center (SpecialLinearGroup (Fin 3) F) := fun h =>
    hxy (Subgroup.mem_center_iff.1 h y).symm
  have hyZ : y ∉ Subgroup.center (SpecialLinearGroup (Fin 3) F) := fun h =>
    hxy (Subgroup.mem_center_iff.1 h x)
  exact closure_centralizers_psl_of_heisenberg hxE hyE hxZ hyZ hξ hω hω1 hy hx hcard

end CFSG.LieType.SeitzGeneration
