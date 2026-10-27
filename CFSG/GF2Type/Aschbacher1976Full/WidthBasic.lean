module

public import CFSG.GF2Type.Aschbacher1976Full.Defs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG CFSG.Blueprint Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Z4Data (z : G) (w : ℕ) (Z A : Subgroup G) : Prop where
  cyc : IsCyclic Z
  card_Z : Nat.card Z = 4
  mem_z : z ∈ Z
  ext_A : IsExtraspecialPGroup 2 A
  card_A : Nat.card A = 2 ^ (1 + 2 * w)
  comm : A ≤ centralizer (Z : Set G)
  sup_eq : Z ⊔ A = Fz z
  inf_eq : Z ⊓ A = zpowers z

theorem exists_Z4Data {z : G} {w : ℕ} (h : IsZ4Star z w) :
    ∃ Z A : Subgroup G, Z4Data z w Z A := by
  obtain ⟨Z, A, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨Z, A, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

theorem mem_zpowers_involution {K : Type*} [Group K] {b y : K} (hb : orderOf b = 2)
    (hy : y ∈ zpowers b) : y = 1 ∨ y = b := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hk : b ^ k = b ^ (k % (orderOf b : ℤ)) := (zpow_mod_orderOf b k).symm
  rw [hb] at hk
  push_cast at hk
  rw [hk]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp

theorem comm_of_isCyclic {K : Type*} [Group K] (Z : Subgroup K) [IsCyclic Z] {u v : K}
    (hu : u ∈ Z) (hv : v ∈ Z) : u * v = v * u := by
  letI : CommGroup Z := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨u, hu⟩ : Z) ⟨v, hv⟩)

section Basic

variable {z : G} {w : ℕ} {Z A : Subgroup G}

theorem z_sq (hz : orderOf z = 2) : z ^ 2 = 1 := by
  rw [← hz]
  exact pow_orderOf_eq_one z

theorem comm_Z (hD : Z4Data z w Z A) {u v : G} (hu : u ∈ Z) (hv : v ∈ Z) :
    u * v = v * u := by
  haveI := hD.cyc
  exact comm_of_isCyclic Z hu hv

theorem involution_eq (hD : Z4Data z w Z A) (hz : orderOf z = 2) {s : G} (hs : s ∈ Z)
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) : s = z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hD.cyc
  let a : Z := ⟨s, hs⟩
  let b : Z := ⟨z, hD.mem_z⟩
  have hb : orderOf b = 2 := by
    show orderOf (⟨z, hD.mem_z⟩ : Z) = 2
    rw [Subgroup.orderOf_mk, hz]
  have ha2 : a ^ 2 = 1 := Subtype.ext (by simpa [a] using hs2)
  have ha1 : a ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have ha : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have heq : zpowers a = zpowers b := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, ha, hb]
  have hab : a ∈ zpowers b := heq ▸ mem_zpowers a
  rcases mem_zpowers_involution hb hab with h | h
  · exact absurd h ha1
  · exact congrArg Subtype.val h

theorem sq_mem_frattini_two {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) (x : P) :
    x ^ 2 ∈ frattini P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hP.isNilpotent
  unfold frattini Order.radical
  rw [Subgroup.mem_iInf]
  intro M
  rw [Subgroup.mem_iInf]
  intro hM
  exact Subgroup.sq_mem_of_index_two ((IsPGroup.isCoatom_iff_index_eq_prime hP).mp hM) x

theorem mem_zpowers_of_central (hD : Z4Data z w Z A) (hz : orderOf z = 2) {a : G} (ha : a ∈ A)
    (hac : ∀ b ∈ A, a * b = b * a) : a ∈ zpowers z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzA : z ∈ A := (hD.inf_eq ▸ mem_zpowers z : z ∈ Z ⊓ A).2
  let zA : A := ⟨z, hzA⟩
  have hzord : orderOf zA = 2 := by
    show orderOf (⟨z, hzA⟩ : A) = 2
    rw [Subgroup.orderOf_mk, hz]
  have hle : zpowers zA ≤ center A := by
    rw [zpowers_le, Subgroup.mem_center_iff]
    intro b
    have hbz : (b : G) * z = z * (b : G) :=
      ((mem_centralizer_iff.mp (hD.comm b.2)) z hD.mem_z).symm
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hbz
  have heq : zpowers zA = center A := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, hzord, hD.ext_A.2.2.2]
  have hmem : (⟨a, ha⟩ : A) ∈ zpowers zA := by
    rw [heq, Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hac b.1 b.2).symm
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hk' : z ^ k = a := congrArg Subtype.val hk
  exact hk' ▸ zpow_mem_zpowers z k

theorem sq_mem_zpowers_A (hD : Z4Data z w Z A) (hz : orderOf z = 2) {a : G} (ha : a ∈ A) :
    a ^ 2 ∈ zpowers z := by
  have hfr : (⟨a, ha⟩ : A) ^ 2 ∈ frattini A := sq_mem_frattini_two hD.ext_A.1 _
  rw [hD.ext_A.2.2.1] at hfr
  have h2A : a ^ 2 ∈ A := A.pow_mem ha 2
  apply mem_zpowers_of_central hD hz h2A
  intro b hb
  have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hfr ⟨b, hb⟩)
  simp only [Subgroup.coe_mul, Subgroup.coe_pow] at h2
  exact h2.symm

theorem comm_mem_zpowers_A (hD : Z4Data z w Z A) (hz : orderOf z = 2) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) : ⁅a, b⁆ ∈ zpowers z := by
  have hcen : (⁅(⟨a, ha⟩ : A), (⟨b, hb⟩ : A)⁆ : A) ∈ center A := by
    rw [← hD.ext_A.2.1]
    exact commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hAmem : ⁅a, b⁆ ∈ A := by
    simp only [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
  apply mem_zpowers_of_central hD hz hAmem
  intro c hc
  have := Subgroup.mem_center_iff.mp hcen ⟨c, hc⟩
  have h2 := congrArg Subtype.val this
  simp only [Subgroup.coe_mul] at h2
  exact h2.symm

theorem commute_ZA (hD : Z4Data z w Z A) {c a : G} (hc : c ∈ Z) (ha : a ∈ A) :
    Commute c a :=
  (mem_centralizer_iff.mp (hD.comm ha)) c hc

theorem comm_mul_left {c a y : G} (hca : Commute c a) (hcy : Commute c y) :
    ⁅c * a, y⁆ = ⁅a, y⁆ := by
  have hW : Commute c (a * y * a⁻¹) := ((hca.mul_right hcy).mul_right hca.inv_right)
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc c * a * y * (a⁻¹ * c⁻¹) * y⁻¹ = c * (a * y * a⁻¹) * c⁻¹ * y⁻¹ := by
        simp only [mul_assoc]
    _ = (a * y * a⁻¹) * c * c⁻¹ * y⁻¹ := by rw [hW.eq]
    _ = a * y * a⁻¹ * y⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]

theorem comm_mul_right {c a x : G} (hca : Commute c a) (hcx : Commute c x) :
    ⁅x, c * a⁆ = ⁅x, a⁆ := by
  have hW : Commute c (x * a * x⁻¹ * a⁻¹) :=
    (((hcx.mul_right hca).mul_right hcx.inv_right).mul_right hca.inv_right)
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * (c * a) * x⁻¹ * (a⁻¹ * c⁻¹) = c * (x * a * x⁻¹ * a⁻¹) * c⁻¹ := by
        rw [← mul_assoc x c a, ← hcx.eq]; simp only [mul_assoc]
    _ = x * a * x⁻¹ * a⁻¹ := by rw [hW.eq]; simp only [mul_assoc, mul_inv_cancel, mul_one]

end Basic

end CFSG.GF2Type.Aschbacher1976Full.Width
