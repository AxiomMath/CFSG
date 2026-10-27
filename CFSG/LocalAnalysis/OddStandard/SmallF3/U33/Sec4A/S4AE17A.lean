module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem e17_two_gen {K Y : Subgroup G} (φ : ↥K →* Multiplicative (ZMod 4 × ZMod 4))
    (hφ : Function.Surjective φ) (hker : φ.ker = Y.subgroupOf K) :
    ∃ a ∈ K, ∃ b ∈ K, ∀ q ∈ K, ∃ i j : ℕ, ∃ y ∈ Y, q = a ^ i * b ^ j * y := by
  obtain ⟨a₀, ha₀⟩ := hφ (Multiplicative.ofAdd ((1, 0) : ZMod 4 × ZMod 4))
  obtain ⟨b₀, hb₀⟩ := hφ (Multiplicative.ofAdd ((0, 1) : ZMod 4 × ZMod 4))
  refine ⟨(a₀ : G), a₀.2, (b₀ : G), b₀.2, ?_⟩
  intro q hq
  let z : ↥K := ⟨q, hq⟩
  let m : ZMod 4 := (φ z).toAdd.1
  let n : ZMod 4 := (φ z).toAdd.2
  have hv : φ z = Multiplicative.ofAdd (m, n) := rfl
  let i : ℕ := m.val
  let j : ℕ := n.val
  have hi : (i : ZMod 4) = m := ZMod.natCast_zmod_val m
  have hj : (j : ZMod 4) = n := ZMod.natCast_zmod_val n
  have hgen : φ (a₀ ^ i * b₀ ^ j) = Multiplicative.ofAdd (m, n) := by
    rw [map_mul, map_pow, map_pow, ha₀, hb₀]
    rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add]
    congr 1
    ext <;> simp [hi, hj, nsmul_eq_mul]
  have hu : (a₀ ^ i * b₀ ^ j)⁻¹ * z ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgen, hv, inv_mul_cancel]
  rw [hker] at hu
  refine ⟨i, j, ↑((a₀ ^ i * b₀ ^ j)⁻¹ * z), Subgroup.mem_subgroupOf.mp hu, ?_⟩
  have hz : (z : G) = q := rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hz]
  group

private lemma e17_comm_mem {K Y : Subgroup G}
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    {x x' : G} (hx : x ∈ K) (hx' : x' ∈ K) : ⁅x, x'⁆ ∈ Y :=
  hKY x hx x' hx'

private lemma e17_comm_Y_left {K Y : Subgroup G}
    (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y) {y k : G} (hy : y ∈ Y) (hk : k ∈ K) :
    ⁅y, k⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (hYc y hy k hk)

private lemma e17_comm_Y_right {K Y : Subgroup G}
    (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y) {y k : G} (hy : y ∈ Y) (hk : k ∈ K) :
    ⁅k, y⁆ = 1 := by
  rw [← commutatorElement_inv y k, e17_comm_Y_left hYc hy hk, inv_one]

private lemma e17_comm_mul_left {K Y : Subgroup G}
    (hYK : Y ≤ K) (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    {x x' z : G} (hx : x ∈ K) (hx' : x' ∈ K) (hz : z ∈ K) :
    ⁅x * x', z⁆ = ⁅x, z⁆ * ⁅x', z⁆ := by
  have hmemY : ⁅x', z⁆ ∈ Y := e17_comm_mem hKY hx' hz
  have hmemK : ⁅x', z⁆ ∈ K := hYK hmemY
  have hcx : x * ⁅x', z⁆ * x⁻¹ = ⁅x', z⁆ := by
    rw [← hYc ⁅x', z⁆ hmemY x hx]
    group
  calc ⁅x * x', z⁆ = x * ⁅x', z⁆ * x⁻¹ * ⁅x, z⁆ :=
        commutatorElement_mul_left_eq_conj_mul x x' z
    _ = ⁅x', z⁆ * ⁅x, z⁆ := by rw [hcx]
    _ = ⁅x, z⁆ * ⁅x', z⁆ :=
        (hYc ⁅x, z⁆ (e17_comm_mem hKY hx hz) ⁅x', z⁆ hmemK).symm

private lemma e17_comm_mul_right {K Y : Subgroup G}
    (hYK : Y ≤ K) (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    {x z z' : G} (hx : x ∈ K) (hz : z ∈ K) (hz' : z' ∈ K) :
    ⁅x, z * z'⁆ = ⁅x, z⁆ * ⁅x, z'⁆ := by
  have hmemY : ⁅x, z'⁆ ∈ Y := e17_comm_mem hKY hx hz'
  have hcz : z * ⁅x, z'⁆ * z⁻¹ = ⁅x, z'⁆ := by
    rw [← hYc ⁅x, z'⁆ hmemY z hz]
    group
  calc ⁅x, z * z'⁆ = ⁅x, z⁆ * z * ⁅x, z'⁆ * z⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj x z z'
    _ = ⁅x, z⁆ * (z * ⁅x, z'⁆ * z⁻¹) := by group
    _ = ⁅x, z⁆ * ⁅x, z'⁆ := by rw [hcz]

private lemma e17_comm_pow_left {K Y : Subgroup G}
    (hYK : Y ≤ K) (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    {x z : G} (hx : x ∈ K) (hz : z ∈ K) (n : ℕ) :
    ⁅x ^ n, z⁆ = ⁅x, z⁆ ^ n := by
  have h : Commute x ⁅x, z⁆ := (hYc ⁅x, z⁆ (e17_comm_mem hKY hx hz) x hx).symm
  exact (h.commutatorElement_pow_left n).symm

private lemma e17_comm_pow_right {K Y : Subgroup G}
    (hYK : Y ≤ K) (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    {x z : G} (hx : x ∈ K) (hz : z ∈ K) (n : ℕ) :
    ⁅x, z ^ n⁆ = ⁅x, z⁆ ^ n := by
  have h : Commute z ⁅x, z⁆ := (hYc ⁅x, z⁆ (e17_comm_mem hKY hx hz) z hz).symm
  exact (h.commutatorElement_pow_right n).symm

private lemma e17_comm_form_left {K Y : Subgroup G}
    (hYK : Y ≤ K) (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) {i j : ℕ} {y : G} (hy : y ∈ Y)
    {z : G} (hz : z ∈ K) :
    ⁅a ^ i * b ^ j * y, z⁆ = ⁅a, z⁆ ^ i * ⁅b, z⁆ ^ j := by
  have hai : a ^ i ∈ K := K.pow_mem ha i
  have hbj : b ^ j ∈ K := K.pow_mem hb j
  have hyK : y ∈ K := hYK hy
  have hab : a ^ i * b ^ j ∈ K := K.mul_mem hai hbj
  calc ⁅a ^ i * b ^ j * y, z⁆ = ⁅a ^ i * b ^ j, z⁆ * ⁅y, z⁆ :=
        e17_comm_mul_left hYK hYc hKY hab hyK hz
    _ = (⁅a ^ i, z⁆ * ⁅b ^ j, z⁆) * ⁅y, z⁆ := by
        rw [e17_comm_mul_left hYK hYc hKY hai hbj hz]
    _ = ⁅a, z⁆ ^ i * ⁅b, z⁆ ^ j := by
        rw [e17_comm_pow_left hYK hYc hKY ha hz i,
          e17_comm_pow_left hYK hYc hKY hb hz j,
          e17_comm_Y_left hYc hy hz]
        group

private lemma e17_comm_a_of_form {K Y : Subgroup G}
    (hYK : Y ≤ K) (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) {i' j' : ℕ} {y' : G} (hy' : y' ∈ Y) :
    ⁅a, a ^ i' * b ^ j' * y'⁆ = ⁅a, b⁆ ^ j' := by
  have hai : a ^ i' ∈ K := K.pow_mem ha i'
  have hbj : b ^ j' ∈ K := K.pow_mem hb j'
  have hyK : y' ∈ K := hYK hy'
  have hab : a ^ i' * b ^ j' ∈ K := K.mul_mem hai hbj
  calc ⁅a, a ^ i' * b ^ j' * y'⁆ = ⁅a, a ^ i' * b ^ j'⁆ * ⁅a, y'⁆ :=
        e17_comm_mul_right hYK hYc hKY ha hab hyK
    _ = (⁅a, a ^ i'⁆ * ⁅a, b ^ j'⁆) * ⁅a, y'⁆ := by
        rw [e17_comm_mul_right hYK hYc hKY ha hai hbj]
    _ = ⁅a, b⁆ ^ j' := by
        rw [((Commute.refl a).pow_right i').commutator_eq,
          e17_comm_pow_right hYK hYc hKY ha hb j',
          e17_comm_Y_right hYc hy' ha]
        group

private lemma e17_comm_b_of_form {K Y : Subgroup G}
    (hYK : Y ≤ K) (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) {i' j' : ℕ} {y' : G} (hy' : y' ∈ Y) :
    ⁅b, a ^ i' * b ^ j' * y'⁆ = ⁅b, a⁆ ^ i' := by
  have hai : a ^ i' ∈ K := K.pow_mem ha i'
  have hbj : b ^ j' ∈ K := K.pow_mem hb j'
  have hyK : y' ∈ K := hYK hy'
  have hab : a ^ i' * b ^ j' ∈ K := K.mul_mem hai hbj
  calc ⁅b, a ^ i' * b ^ j' * y'⁆ = ⁅b, a ^ i' * b ^ j'⁆ * ⁅b, y'⁆ :=
        e17_comm_mul_right hYK hYc hKY hb hab hyK
    _ = (⁅b, a ^ i'⁆ * ⁅b, b ^ j'⁆) * ⁅b, y'⁆ := by
        rw [e17_comm_mul_right hYK hYc hKY hb hai hbj]
    _ = ⁅b, a⁆ ^ i' := by
        rw [e17_comm_pow_right hYK hYc hKY hb ha i',
          ((Commute.refl b).pow_right j').commutator_eq,
          e17_comm_Y_right hYc hy' hb]
        group

private lemma e17_comm_mem_zpowers {K Y : Subgroup G} {a b : G}
    (ha : a ∈ K) (hb : b ∈ K)
    (hYK : Y ≤ K) (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    (hgen : ∀ q ∈ K, ∃ i j : ℕ, ∃ y ∈ Y, q = a ^ i * b ^ j * y)
    {x x' : G} (hx : x ∈ K) (hx' : x' ∈ K) :
    ⁅x, x'⁆ ∈ Subgroup.zpowers ⁅a, b⁆ := by
  obtain ⟨i, j, y, hy, rfl⟩ := hgen x hx
  obtain ⟨i', j', y', hy', rfl⟩ := hgen x' hx'
  rw [e17_comm_form_left hYK hYc hKY ha hb hy hx',
    e17_comm_a_of_form hYK hYc hKY ha hb hy',
    e17_comm_b_of_form hYK hYc hKY ha hb hy']
  refine (Subgroup.zpowers ⁅a, b⁆).mul_mem ?_ ?_
  · exact (Subgroup.zpowers ⁅a, b⁆).pow_mem
      (Subgroup.npow_mem_zpowers ⁅a, b⁆ j') i
  · have hba : ⁅b, a⁆ ∈ Subgroup.zpowers ⁅a, b⁆ := by
      rw [← commutatorElement_inv a b]
      exact (Subgroup.zpowers ⁅a, b⁆).inv_mem (Subgroup.mem_zpowers ⁅a, b⁆)
    have hbai : (⁅b, a⁆ ^ i') ∈ Subgroup.zpowers ⁅a, b⁆ :=
      (Subgroup.zpowers ⁅a, b⁆).pow_mem hba i'
    exact (Subgroup.zpowers ⁅a, b⁆).pow_mem hbai j

private lemma e17_mem_zpowers_sq_eq_one {c d : G} (hc : c * c = 1)
    (hd : d ∈ Subgroup.zpowers c) : d = 1 ∨ d = c := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
  have horder : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
  rcases (Nat.dvd_prime Nat.prime_two).mp horder with h1 | h2
  · left
    rw [← hk, orderOf_eq_one_iff.mp h1]
    simp
  · rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
    · left
      have h2z : (orderOf c : ℤ) = 2 := by rw [h2]; simp
      rw [← hk, ← zpow_mod_orderOf c k, h2z, hk0]
      simp
    · right
      have h2z : (orderOf c : ℤ) = 2 := by rw [h2]; simp
      rw [← hk, ← zpow_mod_orderOf c k, h2z, hk1]
      simp

theorem e17_abelian {K Y : Subgroup G} {a b ρ : G} (ha : a ∈ K) (hb : b ∈ K)
    (hgen : ∀ q ∈ K, ∃ i j : ℕ, ∃ y ∈ Y, q = a ^ i * b ^ j * y)
    (hYK : Y ≤ K) (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hKY : ∀ x ∈ K, ∀ x' ∈ K, x * x' * x⁻¹ * x'⁻¹ ∈ Y)
    (hρ : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K) (hfix : ∀ k ∈ K, ρ * k = k * ρ → k = 1) :
    ∀ x ∈ K, ∀ x' ∈ K, x * x' = x' * x := by
  set c : G := ⁅a, b⁆ with hc
  have hcY : c ∈ Y := by rw [hc]; exact e17_comm_mem hKY ha hb
  have hcK : c ∈ K := hYK hcY
  have hcc : c * c = 1 := hY2 c hcY
  have hc_eq_one : c = 1 := by
    by_contra hne
    have hρa : ρ * a * ρ⁻¹ ∈ K := hρ a ha
    have hρb : ρ * b * ρ⁻¹ ∈ K := hρ b hb
    have hconj : ρ * c * ρ⁻¹ = ⁅ρ * a * ρ⁻¹, ρ * b * ρ⁻¹⁆ := by
      rw [hc]
      exact conjugate_commutatorElement (g₁ := a) (g₂ := b) (g₃ := ρ)
    have hmem : ρ * c * ρ⁻¹ ∈ Subgroup.zpowers c := by
      rw [hconj]
      exact e17_comm_mem_zpowers ha hb hYK hYc hKY hgen hρa hρb
    rcases e17_mem_zpowers_sq_eq_one hcc hmem with h1 | h1
    · refine hne ?_
      calc c = ρ⁻¹ * (ρ * c * ρ⁻¹) * ρ := by group
        _ = ρ⁻¹ * 1 * ρ := by rw [h1]
        _ = 1 := by group
    · have hcomm : ρ * c = c * ρ := by
        calc ρ * c = (ρ * c * ρ⁻¹) * ρ := by group
          _ = c * ρ := by rw [h1]
      exact hne (hfix c hcK hcomm)
  intro x hx x' hx'
  have h : ⁅x, x'⁆ ∈ Subgroup.zpowers c :=
    e17_comm_mem_zpowers ha hb hYK hYc hKY hgen hx hx'
  rcases e17_mem_zpowers_sq_eq_one hcc h with h1 | h1
  · exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · rw [hc_eq_one] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
