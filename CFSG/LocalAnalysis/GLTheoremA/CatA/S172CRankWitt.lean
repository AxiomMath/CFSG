module

public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.Timmesfeld.Orders.ClassicalAnisotropic
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open scoped commutatorElement

variable {F : Type*} [Field F] [Finite F] [CharP F 2] {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem exists_mem_orthogonalGroup_apply_eq_of_map_eq (hQ : (polarBilin Q).Nondegenerate) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Q y = Q x) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g x = y := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨g, hg, hgx⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq hQ
    (k := 1) ![x] ![y] (linearIndependent_unique_iff.2 (by simpa using hx))
    (linearIndependent_unique_iff.2 (by simpa using hy)) (fun i => by simpa using hxy)
    (fun i j => by
      simp only [Matrix.cons_val_fin_one, polar_self_eq_two_mul, h2, zero_mul])
  exact ⟨g, hg, by simpa using hgx 0⟩

theorem reflect_mul_reflect_mem_orthDerived (hQ : (polarBilin Q).Nondegenerate) {x y : V}
    (hx : Q x ≠ 0) (hy : Q y ≠ 0) : reflect Q x * reflect Q y ∈ orthDerived Q := by
  obtain ⟨c, hc⟩ := CFSG.Timmesfeld.ClassicalOrders.exists_sq_eq_of_charTwo (Q x / Q y)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at hc
    exact hc.elim hx hy
  have hQcy : Q (c • y) = Q x := by
    rw [map_smul_eq_sq, hc, div_mul_cancel₀ _ hy]
  have hcy0 : c • y ≠ 0 := by
    intro h
    apply hx
    rw [← hQcy, h, QuadraticMap.map_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (QuadraticMap.map_zero Q)
  obtain ⟨g, hg, hgx⟩ := exists_mem_orthogonalGroup_apply_eq_of_map_eq hQ hx0 hcy0 hQcy
  have h1 : g * reflect Q x * g⁻¹ = reflect Q y := by
    rw [reflect_conj hg, hgx, CFSG.Timmesfeld.ClassicalOrders.reflect_smul hc0]
  have h2 : reflect Q x * reflect Q y = ⁅reflect Q x, g⁆ := by
    rw [commutatorElement_def, reflect_inv, ← h1]
    simp only [mul_assoc]
  rw [h2]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q x) hg

end CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

end
