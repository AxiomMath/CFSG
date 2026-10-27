module

public import CFSG.ClassicalInvolution.Q3.Q3MApp
public import CFSG.ClassicalInvolution.Q3.Tight

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification
open scoped MatrixGroups

theorem sl2_involution_sq :
    ∀ w : SL(2, ZMod 3), w ^ 2 = 1 → w ≠ 1 → ∃ y : SL(2, ZMod 3), y ^ 2 = w := by
  decide +kernel

section Member

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

omit [Finite Y] in
theorem IsClassicalMember3.commute_involution (h : IsClassicalMember3 L z) {l : Y} (hl : l ∈ L) :
    l * z = z * l := by
  have h1 : l ∈ Subgroup.centralizer ({z} : Set Y) := isSubnormal_le h.subnormal hl
  exact (Subgroup.mem_centralizer_iff.mp h1 z (Set.mem_singleton z)).symm

omit [Finite Y] in
theorem IsClassicalMember3.sq_eq_one (h : IsClassicalMember3 L z) : z ^ 2 = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.orderOf_eq_two] at this

theorem eq_one_of_two_pow_of_odd_ker {G : Type*} [Group G] [Finite G] (φ : G →* SL(2, ZMod 3))
    (hker : Odd (Nat.card φ.ker)) {w : G} (hw : φ w = 1) {j : ℕ} (hj : w ^ (2 ^ j) = 1) :
    w = 1 := by
  have hmem : w ∈ φ.ker := hw
  have h1 : orderOf (⟨w, hmem⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  have h2 : orderOf w ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
  have hcop : Nat.Coprime (2 ^ j) (Nat.card φ.ker) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hker)
  have h3 : orderOf w ∣ Nat.gcd (2 ^ j) (Nat.card φ.ker) := Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one, Nat.dvd_one] at h3
  exact orderOf_eq_one_iff.mp h3

theorem IsClassicalMember3.exists_sq_eq (h : IsClassicalMember3 L z) : ∃ u ∈ L, u ^ 2 = z := by
  obtain ⟨φ, hφs, hφodd⟩ := M.exists_hom_of_member h
  set z' : L := ⟨z, h.mem⟩ with hz'
  have hz'2 : z' ^ 2 = 1 := Subtype.ext (by simpa [hz'] using h.sq_eq_one)
  have hz'1 : z' ≠ 1 := fun h1 => h.ne_one (congrArg Subtype.val h1)
  have hz'ord : orderOf z' = 2 := orderOf_eq_prime hz'2 hz'1
  have hz'c : ∀ g : L, g * z' = z' * g := fun g =>
    Subtype.ext (h.commute_involution g.2)
  have hφz1 : φ z' ≠ 1 := by
    intro h1
    have hmem : z' ∈ φ.ker := h1
    have hd : orderOf (⟨z', hmem⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hz'ord] at hd
    exact absurd (hφodd.of_dvd_nat hd) (by decide)
  have hφz2 : φ z' ^ 2 = 1 := by rw [← map_pow, hz'2, map_one]
  obtain ⟨y, hy⟩ := sl2_involution_sq (φ z') hφz2 hφz1
  obtain ⟨u₀, hu₀⟩ := hφs y
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos u₀).ne'
  have hu2k : (u₀ ^ m) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm m, ← hkm]
    exact pow_orderOf_eq_one u₀
  have hφu : φ ((u₀ ^ m) ^ 2) = φ z' := by
    rw [map_pow, map_pow, hu₀, ← pow_mul, mul_comm, pow_mul, hy]
    obtain ⟨c, hc⟩ := hm
    rw [hc, pow_succ, pow_mul, hφz2, one_pow, one_mul]
  have hcomm : Commute ((u₀ ^ m) ^ 2) z'⁻¹ :=
    Commute.inv_right (a := (u₀ ^ m) ^ 2) (b := z') (hz'c _)
  have hw : φ ((u₀ ^ m) ^ 2 * z'⁻¹) = 1 := by rw [map_mul, map_inv, hφu, mul_inv_cancel]
  have hw2a : ((u₀ ^ m) ^ 2) ^ (2 ^ (k + 1)) = 1 := by
    have key : ∀ (a : L) (k : ℕ), (a ^ 2) ^ (2 ^ (k + 1)) = (a ^ (2 ^ k)) ^ 4 := by
      intro a k
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [key, hu2k, one_pow]
  have hw2b : z'⁻¹ ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ', pow_mul, inv_pow, hz'2, inv_one, one_pow]
  have hw2 : ((u₀ ^ m) ^ 2 * z'⁻¹) ^ (2 ^ (k + 1)) = 1 := by
    rw [hcomm.mul_pow, hw2a, hw2b, one_mul]
  have h1 := eq_one_of_two_pow_of_odd_ker φ hφodd hw hw2
  refine ⟨((u₀ ^ m : L) : Y), (u₀ ^ m).2, ?_⟩
  have h2 : (u₀ ^ m) ^ 2 = z' := mul_inv_eq_one.mp h1
  exact congrArg Subtype.val h2

theorem IsClassicalMember3.le_centralizer_of_isComponentOf_centralizer
    (hL : IsClassicalMember3 L z) {D : Subgroup Y}
    (hDz : D ≤ Subgroup.centralizer ({z} : Set Y))
    (hDC : IsComponentOf (D.subgroupOf (Subgroup.centralizer ({z} : Set Y))) ⊤) :
    L ≤ Subgroup.centralizer (D : Set Y) := by
  set C : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hC
  have hLC : L ≤ C := isSubnormal_le hL.subnormal
  have hLsub : IsSubnormal (L.subgroupOf C) ⊤ := by
    have h := isSubnormal_subgroupOf hL.subnormal C
    rwa [Subgroup.subgroupOf_self] at h
  have hsolv : Group.IsSolvable (L.subgroupOf C) :=
    have := hL.isSolvable
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLC).injective
  have hcomm := @Layer.commutes_with_solvable_subnormal C _ _ (L.subgroupOf C) hLsub hsolv
  have hle : D.subgroupOf C ≤ Layer.subgroup C := Layer.component_le hDC
  have hcent : Layer.subgroup C ≤ Subgroup.centralizer ((L.subgroupOf C : Subgroup C) : Set C) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have h1 : (⟨d, hDz hd⟩ : C) ∈ Subgroup.centralizer ((L.subgroupOf C : Subgroup C) : Set C) :=
    hcent (hle hd)
  have h2 := Subgroup.mem_centralizer_iff.mp h1 (⟨l, hLC hl⟩ : C) hl
  exact (congrArg Subtype.val h2).symm

end Member

end CFSG.ClassicalInvolution.Q3
