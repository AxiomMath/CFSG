module

public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

section SL2

variable {F : Type*} [Field F]

@[expose] def slW (F : Type*) [Field F] : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem sl2_w_mul_self : slW F * slW F = -1 := by
  have hneg : ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (-1) :=
    CFSG.Semidihedral.OddFieldSL2.minusIdentity_matrix F
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have h1 : ((slW F * slW F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
      ((slW F : Matrix (Fin 2) (Fin 2) F) * (slW F : Matrix (Fin 2) (Fin 2) F)) i j := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
  have h2 : (((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) i j =
      (Matrix.scalar (Fin 2) (-1 : F)) i j := by
    rw [hneg]
  change ((slW F * slW F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
    (((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) i j
  rw [h1, h2]
  fin_cases i <;> fin_cases j <;>
    simp [slW, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply]

end SL2

section Exact

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {K : Subgroup G} {z : G}

theorem exists_mul_self_eq_of_exact (hz : IsClassicalMember p f K z)
    (hex : classicalInvolutionOddCore K = ⊥) (hodd : Odd (Nat.card (GaloisField p f))) :
    ∃ a ∈ K, a * a = z := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hex
  have hzK : (⟨z, hz.mem⟩ : K) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨z, hz.mem⟩).mp
      (by rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two)
  refine ⟨((e.symm (slW (GaloisField p f)) : K) : G), (e.symm (slW (GaloisField p f))).2, ?_⟩
  have h : e.symm (slW (GaloisField p f)) * e.symm (slW (GaloisField p f)) = ⟨z, hz.mem⟩ := by
    rw [hzK, ← map_mul, sl2_w_mul_self]
  exact congrArg Subtype.val h

theorem eq_one_or_eq_of_central_of_exact (hz : IsClassicalMember p f K z)
    (hex : classicalInvolutionOddCore K = ⊥) (hodd : Odd (Nat.card (GaloisField p f))) {x : G}
    (hx : x ∈ K) (hc : ∀ k ∈ K, k * x = x * k) : x = 1 ∨ x = z := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hex
  have hzK : (⟨z, hz.mem⟩ : K) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨z, hz.mem⟩).mp
      (by rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two)
  have hcenter : (⟨x, hx⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc k k.2)
  rcases (mem_center_sl2_iff _).mp ((mem_center_iff_of_equiv_sl2 e _).mp hcenter) with h | h
  · left
    have : (⟨x, hx⟩ : K) = 1 := by
      rw [← e.symm_apply_apply (⟨x, hx⟩ : K), h, map_one]
    exact congrArg Subtype.val this
  · right
    have : (⟨x, hx⟩ : K) = ⟨z, hz.mem⟩ := by
      rw [hzK, ← e.symm_apply_apply (⟨x, hx⟩ : K), h]
    exact congrArg Subtype.val this

theorem exists_not_commute_of_mul_self_eq (hz : IsClassicalMember p f K z)
    (hex : classicalInvolutionOddCore K = ⊥) (hodd : Odd (Nat.card (GaloisField p f))) {a : G}
    (ha : a ∈ K) (haa : a * a = z) : ∃ k ∈ K, k * a ≠ a * k := by
  by_contra hcon
  push Not at hcon
  have hz2 : z * z = 1 := by
    have h2 := pow_orderOf_eq_one z
    rwa [hz.orderOf_eq_two, pow_two] at h2
  rcases eq_one_or_eq_of_central_of_exact hz hex hodd ha hcon with h | h
  · rw [h, one_mul] at haa
    have h1 : z = 1 := haa.symm
    have h2 : orderOf z = 1 := by rw [h1]; exact orderOf_one
    rw [hz.orderOf_eq_two] at h2
    omega
  · rw [h, hz2] at haa
    have h1 : z = 1 := haa.symm
    have h2 : orderOf z = 1 := by rw [h1]; exact orderOf_one
    rw [hz.orderOf_eq_two] at h2
    omega

end Exact

end CFSG.ClassicalInvolution.RouteD.TwinY
