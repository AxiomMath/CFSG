module

public import Mathlib.LinearAlgebra.Matrix.Unique
public import CFSG.FeitThompson.Local.RankTwoAutomorphismLinearQuotient
public import CFSG.FeitThompson.Representations.OddLinearGroupsDimTwoPrimeField
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Matrix Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p n : ℕ} {P : Type*} [Group P]

theorem isMulCommutative_generalLinearGroup_one (R : Type*) [CommRing R] :
    IsMulCommutative (GL (Fin 1) R) :=
  ⟨⟨fun a b => (Units.mapEquiv
    (Matrix.uniqueRingEquiv (m := Fin 1) (A := R)).toMulEquiv).injective (by simp [mul_comm])⟩⟩

theorem isPGroup_commutator_of_hom {A : Type*} [Group A] {K : Type*} [Group K] (g : A →* K)
    (hker : IsPGroup p g.ker) (himg : IsPGroup p (⁅g.range, g.range⁆ : Subgroup K)) :
    IsPGroup p (_root_.commutator A) :=
  (himg.comap_of_ker_isPGroup g hker).to_le
    (Subgroup.map_le_iff_le_comap.mp (map_commutator_eq A g).le)

theorem isPGroup_commutator_subgroup_GL_of_odd (hp : p.Prime) {d : ℕ} (hd : d = 1 ∨ d = 2)
    {G : Subgroup (GL (Fin d) (ZMod p))} (hG : Odd (Nat.card G)) :
    IsPGroup p (⁅G, G⁆ : Subgroup (GL (Fin d) (ZMod p))) := by
  rcases hd with rfl | rfl
  · have := isMulCommutative_generalLinearGroup_one (ZMod p)
    rw [Subgroup.commutator_self_eq_bot_iff.2 (inferInstance : IsMulCommutative G)]
    exact IsPGroup.of_bot
  · have := Fact.mk hp
    obtain ⟨Q, -, -, -, hcomm⟩ := exists_cyclic_normal_sylow_of_odd_prime_field hp hG
    rw [← Subgroup.map_subtype_commutator]
    exact (Q.isPGroup'.to_le hcomm).map _

theorem isPGroup_commutator_of_odd_aut_of_elementaryAbelianPRank_le_two [Finite P]
    (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P) (hrank : elementaryAbelianPRank p P ≤ 2)
    {A : Subgroup (MulAut P)} (hA : Odd (Nat.card A)) :
    IsPGroup p (_root_.commutator ↥A) := by
  rcases subsingleton_or_nontrivial P with hs | hnt
  · have : Subsingleton (MulAut P) := ⟨fun _ _ => MulEquiv.ext fun _ => Subsingleton.elim _ _⟩
    exact IsPGroup.of_subsingleton _ _
  obtain ⟨B, hBnorm, d, hBp, hd, f, hf⟩ :=
    exists_normal_isPGroup_injective_quotient_toGL_of_elementaryAbelianPRank_le_two hp hodd hP
      hrank A
  set g : ↥A →* GL (Fin d) (ZMod p) := f.comp (QuotientGroup.mk' B) with hg
  have hker : g.ker = B := by
    rw [hg, MonoidHom.ker_comp_of_injective _ _ hf, QuotientGroup.ker_mk']
  exact isPGroup_commutator_of_hom g (hker ▸ hBp)
    (isPGroup_commutator_subgroup_GL_of_odd hp hd (hA.of_dvd_nat (Subgroup.card_range_dvd g)))

theorem isPGroup_commutator_subgroup_of_odd_aut_of_elementaryAbelianPRank_le_two [Finite P]
    (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P) (hrank : elementaryAbelianPRank p P ≤ 2)
    {A : Subgroup (MulAut P)} (hA : Odd (Nat.card A)) :
    IsPGroup p (⁅A, A⁆ : Subgroup (MulAut P)) := by
  rw [← Subgroup.map_subtype_commutator]
  exact (isPGroup_commutator_of_odd_aut_of_elementaryAbelianPRank_le_two hp hodd hP hrank hA).map _

theorem isPGroup_closure_setOf_inv_mul_inv_mul_mul_of_odd_aut_of_elementaryAbelianPRank_le_two
    [Finite P] (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P)
    (hrank : elementaryAbelianPRank p P ≤ 2) {A : Subgroup (MulAut P)} (hA : Odd (Nat.card A)) :
    IsPGroup p (Subgroup.closure {g : MulAut P | ∃ a ∈ A, ∃ b ∈ A, a⁻¹ * b⁻¹ * a * b = g}) := by
  rw [closure_setOf_inv_mul_inv_mul_mul]
  exact isPGroup_commutator_subgroup_of_odd_aut_of_elementaryAbelianPRank_le_two hp hodd hP hrank hA

theorem exists_card_commutator_eq_pow_of_odd_aut_of_elementaryAbelianPRank_le_two
    (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card P = p ^ n)
    (hrank : elementaryAbelianPRank p P ≤ 2) {A : Subgroup (MulAut P)} (hA : Odd (Nat.card A)) :
    ∃ k : ℕ, Nat.card (⁅A, A⁆ : Subgroup (MulAut P)) = p ^ k := by
  have := Fact.mk hp
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  exact IsPGroup.iff_card.1
    (isPGroup_commutator_subgroup_of_odd_aut_of_elementaryAbelianPRank_le_two hp hodd
      (IsPGroup.of_card hcard) hrank hA)

end

end CFSG.FeitThompson
