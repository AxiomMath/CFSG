module

public import CFSG.GroupTheory.DihedralSubgroups
public import CFSG.CharacterTheory.Wreathed.NonabelianCentralizer

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def subgroupDihedralProjection {m : ℕ} (P : Subgroup (Wreath m)) :
    P →* DihedralGroup m := (dihedralProjection m).comp P.subtype

theorem subgroupDihedralProjection_ker_eq_center (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : ∃ u v : P, u * v ≠ v * u) :
    (subgroupDihedralProjection P).ker = Subgroup.center P := by
  have hcenter := nonabelian_subgroup_center m hm P hP
  ext p
  have hmem : p ∈ Subgroup.center P ↔
      p.val ∈ (Subgroup.center P).map P.subtype := by
    constructor
    · intro hp
      exact Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
    · intro hp
      obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.mp hp
      have hqp' : q = p := Subtype.ext hqp
      exact hqp' ▸ hq
  rw [hmem, hcenter]
  change (dihedralProjection m) p.val = 1 ↔
    p.val ∈ P ⊓ Subgroup.center (Wreath m)
  rw [← MonoidHom.mem_ker, dihedralProjection_ker_eq_center m hm]
  simp only [Subgroup.mem_inf, p.property, true_and]

@[expose] def subgroupCenterQuotientEquivDihedralRange (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : ∃ u v : P, u * v ≠ v * u) :
    P ⧸ Subgroup.center P ≃* (subgroupDihedralProjection P).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (subgroupDihedralProjection_ker_eq_center m hm P hP).symm).trans
    (QuotientGroup.quotientKerEquivRange (subgroupDihedralProjection P))

theorem subgroupDihedralProjection_range_not_isCyclic (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : ∃ u v : P, u * v ≠ v * u) :
    ¬ IsCyclic (subgroupDihedralProjection P).range := by
  intro hcyclic
  let : IsCyclic (subgroupDihedralProjection P).range := hcyclic
  have hker : (subgroupDihedralProjection P).rangeRestrict.ker ≤ Subgroup.center P := by
    rw [MonoidHom.ker_rangeRestrict, subgroupDihedralProjection_ker_eq_center m hm P hP]
  have hab := (subgroupDihedralProjection P).rangeRestrict
    |>.isMulCommutative_of_isCyclic_of_ker_le_center hker
  obtain ⟨u, v, huv⟩ := hP
  exact huv (isMulCommutative_iff.mp hab u v)

@[expose] def nonabelianSubgroupCenterEquiv (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : ∃ u v : P, u * v ≠ v * u)
    (hZ : Subgroup.center (Wreath m) ≤ P) :
    Subgroup.center P ≃* Subgroup.center (Wreath m) :=
  ((Subgroup.center P).equivMapOfInjective P.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [nonabelian_subgroup_center m hm P hP, inf_eq_right.mpr hZ]))

theorem nonabelian_subgroup_center_isCyclic (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : ∃ u v : P, u * v ≠ v * u)
    (hZ : Subgroup.center (Wreath m) ≤ P) : IsCyclic (Subgroup.center P) :=
  (nonabelianSubgroupCenterEquiv m hm P hP hZ).isCyclic.mpr (center_isCyclic m hm)

theorem nonabelian_subgroup_center_card (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : ∃ u v : P, u * v ≠ v * u)
    (hZ : Subgroup.center (Wreath m) ≤ P) : Nat.card (Subgroup.center P) = m := by
  rw [Nat.card_congr (nonabelianSubgroupCenterEquiv m hm P hP hZ).toEquiv,
    card_center m hm]

theorem nonabelian_subgroup_center_quotient_dihedral {n : ℕ} (hn : 1 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (hP : ∃ u v : P, u * v ≠ v * u) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      Nonempty (P ⧸ Subgroup.center P ≃* DihedralGroup (2 ^ k)) := by
  have hm : 1 < 2 ^ n := by
    calc
      1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  obtain ⟨k, hk, hkn, ⟨e⟩⟩ :=
    CFSG.GorensteinWalter.noncyclic_subgroup_dihedral_two_pow
      (subgroupDihedralProjection P).range
      (subgroupDihedralProjection_range_not_isCyclic (2 ^ n) hm P hP)
  exact ⟨k, hk, hkn,
    ⟨(subgroupCenterQuotientEquivDihedralRange (2 ^ n) hm P hP).trans e⟩⟩

theorem nonabelian_subgroup_center_quotient_dihedral_card {n : ℕ} (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (hP : ∃ u v : P, u * v ≠ v * u)
    (hZ : Subgroup.center (Wreath (2 ^ n)) ≤ P) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      Nonempty (P ⧸ Subgroup.center P ≃* DihedralGroup (2 ^ k)) ∧
      Nat.card P = (2 ^ n) * 2 ^ (k + 1) := by
  have hn' : 1 ≤ n := by omega
  have hm : 1 < 2 ^ n := by
    calc
      1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn'
  obtain ⟨k, hk, hkn, ⟨e⟩⟩ := nonabelian_subgroup_center_quotient_dihedral hn' P hP
  refine ⟨k, hk, hkn, ⟨e⟩, ?_⟩
  rw [(Subgroup.center P).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr e.toEquiv, DihedralGroup.nat_card,
    nonabelian_subgroup_center_card (2 ^ n) hm P hP hZ, pow_succ]
  simp only [mul_comm, mul_left_comm]

end CFSG.Wreathed
