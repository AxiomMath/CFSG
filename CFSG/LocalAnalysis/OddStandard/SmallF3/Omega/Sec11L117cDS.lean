module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo
public import CFSG.CharacterTheory.Semidihedral.ElementOrders

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem exists_cyclic_relIndex_two_pow_four {D : Subgroup G} {P₀ : Type*} [Group P₀]
    (e : ↥D ≃* P₀) (Y₀ : Subgroup P₀) (hc : IsCyclic Y₀) (hidx : Y₀.index = 2)
    (h4 : ∀ g : P₀, g ∉ Y₀ → g ^ 4 = 1) :
    ∃ Y : Subgroup G, Y ≤ D ∧ IsCyclic Y ∧ Y.relIndex D = 2 ∧
      ∀ u ∈ D, u ∉ Y → u ^ 4 = 1 := by
  have hcyc₁ : IsCyclic (Y₀.comap (e : ↥D →* P₀)) :=
    isCyclic_of_injective ((e : ↥D →* P₀).subgroupComap Y₀)
      ((e : ↥D →* P₀).subgroupComap_injective Y₀ e.injective)
  have hidx₁ : (Y₀.comap (e : ↥D →* P₀)).index = 2 := by
    rw [Subgroup.index_comap_of_surjective Y₀ e.surjective, hidx]
  refine ⟨(Y₀.comap (e : ↥D →* P₀)).map D.subtype,
    Subgroup.map_subtype_le (Y₀.comap (e : ↥D →* P₀)), ?_, ?_, ?_⟩
  · exact (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).isCyclic.mp hcyc₁
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
    exact hidx₁
  · intro u hu huY
    have he : e ⟨u, hu⟩ ∉ Y₀ := by
      intro hy
      apply huY
      exact Subgroup.mem_map_of_mem D.subtype
        ((Subgroup.mem_comap (f := (e : ↥D →* P₀))).mpr hy)
    have hpow : (⟨u, hu⟩ : ↥D) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, map_one, h4 (e ⟨u, hu⟩) he]
    simpa using congrArg Subtype.val hpow

private theorem dihedral_rotation_cyclic_index_two (m : ℕ) (hm : 1 ≤ m) :
    IsCyclic (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m))) ∧
      (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m))).index = 2 := by
  refine ⟨Subgroup.isCyclic_zpowers _, ?_⟩
  have hcard :=
    (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m))).card_mul_index
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at hcard
  have hpos : 0 < 2 ^ m := Nat.pow_pos (by norm_num)
  rw [show 2 * 2 ^ m = 2 ^ m * 2 from Nat.mul_comm 2 (2 ^ m)] at hcard
  exact Nat.mul_left_cancel hpos hcard

private theorem dihedral_outside_pow_four (m : ℕ) (hm : 1 ≤ m) :
    ∀ g : DihedralGroup (2 ^ m),
      g ∉ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) → g ^ 4 = 1 := by
  intro g hg
  cases g with
  | r i =>
    exact absurd (Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), by
      rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]⟩) hg
  | sr i =>
    have hsq : (DihedralGroup.sr i : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
      rw [sq, DihedralGroup.sr_mul_self]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, one_pow]

private theorem semidihedral_outside_pow_four (n : ℕ) (hn : 4 ≤ n) :
    ∀ g : CFSG.Open.SemidihedralGroup n,
      g ∉ CFSG.Semidihedral.rotationSubgroup n → g ^ 4 = 1 := by
  intro g hg
  have hn3 : 3 ≤ n := by omega
  set i := (CFSG.Semidihedral.coordinateEquiv n hn3 g).1
  set e := (CFSG.Semidihedral.coordinateEquiv n hn3 g).2
  have hcoord : CFSG.Semidihedral.element n hn3 i e = g :=
    CFSG.Semidihedral.element_coordinates n hn3 g
  have he : e ≠ 0 := by
    intro h
    apply hg
    rw [← hcoord, CFSG.Semidihedral.element_mem_rotationSubgroup_iff n hn3 i e]
    exact h
  have hval : e.val = 1 := by
    have hlt := ZMod.val_lt e
    have hne : e.val ≠ 0 := by
      intro h
      apply he
      rw [← ZMod.natCast_zmod_val e, h]
      exact Nat.cast_zero
    omega
  have hg2 : g ^ 2 = CFSG.Semidihedral.z n ^ i.val := by
    rw [← hcoord, CFSG.Semidihedral.element_eq, hval, pow_one,
      CFSG.Semidihedral.reflection_square_nat n hn3 i.val]
  calc g ^ 4 = (g ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    _ = (CFSG.Semidihedral.z n ^ i.val) ^ 2 := by rw [hg2]
    _ = CFSG.Semidihedral.z n ^ (i.val * 2) := by rw [← pow_mul]
    _ = (CFSG.Semidihedral.z n ^ 2) ^ i.val := by rw [Nat.mul_comm, pow_mul]
    _ = 1 := by rw [CFSG.Semidihedral.z_sq n hn3, one_pow]

theorem sec11c_isDihSd_cyclic4 {D : Subgroup G} (hD : IsDihSd D) :
    ∃ Y : Subgroup G, Y ≤ D ∧ IsCyclic Y ∧ Y.relIndex D = 2 ∧ ∀ u ∈ D, u ∉ Y → u ^ 4 = 1 := by
  rcases hD with ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact exists_cyclic_relIndex_two_pow_four e _
      (dihedral_rotation_cyclic_index_two m hm).1
      (dihedral_rotation_cyclic_index_two m hm).2
      (dihedral_outside_pow_four m hm)
  · exact exists_cyclic_relIndex_two_pow_four e _
      (CFSG.Semidihedral.rotationSubgroup_cyclic n)
      (CFSG.Semidihedral.rotationSubgroup_index n (by omega))
      (semidihedral_outside_pow_four n (by omega))

end CFSG.OddStandard.SmallF3.Omega
