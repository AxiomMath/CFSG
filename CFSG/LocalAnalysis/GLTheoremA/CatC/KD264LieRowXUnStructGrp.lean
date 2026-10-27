module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def IsGoodIn (Z Q : Subgroup G) : Prop :=
  (∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z) ∧ ∀ x ∈ Q, x ^ 3 ∈ Z

structure ScalarLike (Z : Subgroup G) : Prop where
  central : Z ≤ Subgroup.center G
  cube : ∀ z ∈ Z, z ^ 3 = 1
  card_le : Nat.card Z ≤ 3

theorem commutator_mul_right_of_central {x y z : G} (hz : ⁅x, z⁆ ∈ Subgroup.center G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hc : y * ⁅x, z⁆ = ⁅x, z⁆ * y := Subgroup.mem_center_iff.1 hz y
  calc ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ = ⁅x, y⁆ * (y * ⁅x, z⁆) * y⁻¹ := by group
    _ = ⁅x, y⁆ * (⁅x, z⁆ * y) * y⁻¹ := by rw [hc]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by group

theorem commutator_mul_left_of_central {x y z : G} (hy : ⁅y, z⁆ ∈ Subgroup.center G)
    (hx : ⁅x, z⁆ ∈ Subgroup.center G) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hc : x * ⁅y, z⁆ = ⁅y, z⁆ * x := Subgroup.mem_center_iff.1 hy x
  have hc' : ⁅y, z⁆ * ⁅x, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := Subgroup.mem_center_iff.1 hx _
  calc x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ = (x * ⁅y, z⁆) * x⁻¹ * ⁅x, z⁆ := by group
    _ = (⁅y, z⁆ * x) * x⁻¹ * ⁅x, z⁆ := by rw [hc]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by group
    _ = ⁅x, z⁆ * ⁅y, z⁆ := hc'

theorem pow_comm_of_central {x y d : G} (hd : ∀ g, g * d = d * g) (h : y * x = d * (x * y))
    (k : ℕ) : y ^ k * x = d ^ k * (x * y ^ k) := by
  have hdk : ∀ (k : ℕ) (g : G), g * d ^ k = d ^ k * g := fun k g => by
    have hc : Commute d g := (hd g).symm
    exact (hc.pow_left k).eq.symm
  induction k with
  | zero => simp
  | succ k ih =>
    calc y ^ (k + 1) * x = y * (y ^ k * x) := by rw [pow_succ', mul_assoc]
      _ = y * (d ^ k * (x * y ^ k)) := by rw [ih]
      _ = d ^ k * (y * x) * y ^ k := by
        rw [← mul_assoc y, hdk k y]; simp only [mul_assoc]
      _ = d ^ k * (d * (x * y)) * y ^ k := by rw [h]
      _ = d ^ (k + 1) * (x * y ^ (k + 1)) := by
        rw [pow_succ d k, pow_succ' y k]
        simp only [mul_assoc]

theorem mul_pow_eq_of_central {x y d : G} (hd : ∀ g, g * d = d * g) (h : y * x = d * (x * y))
    (n : ℕ) : (x * y) ^ n = d ^ (n.choose 2) * (x ^ n * y ^ n) := by
  have hdk : ∀ (k : ℕ) (g : G), g * d ^ k = d ^ k * g := fun k g => by
    have hc : Commute d g := (hd g).symm
    exact (hc.pow_left k).eq.symm
  induction n with
  | zero => simp
  | succ n ih =>
    have hyn := pow_comm_of_central hd h n
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = d ^ (n.choose 2) * (x ^ n * y ^ n) * (x * y) := by rw [ih]
      _ = d ^ (n.choose 2) * (x ^ n * (y ^ n * x) * y) := by simp only [mul_assoc]
      _ = d ^ (n.choose 2) * (x ^ n * (d ^ n * (x * y ^ n)) * y) := by rw [hyn]
      _ = d ^ (n.choose 2) * d ^ n * (x ^ n * x * (y ^ n * y)) := by
        rw [← mul_assoc (x ^ n), hdk n (x ^ n)]
        simp only [mul_assoc]
      _ = d ^ ((n + 1).choose 2) * (x ^ (n + 1) * y ^ (n + 1)) := by
        have hc : (n + 1).choose 2 = n.choose 2 + n := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
        rw [hc, pow_add d (n.choose 2) n, pow_succ x n, pow_succ y n]

theorem mul_pow_three_of_central {x y : G} (hc : ⁅x, y⁆ ∈ Subgroup.center G)
    (hc3 : ⁅x, y⁆ ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hcen : ∀ g : G, g * ⁅x, y⁆⁻¹ = ⁅x, y⁆⁻¹ * g := fun g =>
    Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hc) g
  have h : y * x = ⁅x, y⁆⁻¹ * (x * y) := by rw [commutatorElement_def]; group
  have h3 : (⁅x, y⁆⁻¹) ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
  rw [mul_pow_eq_of_central hcen h 3]
  have : (3 : ℕ).choose 2 = 3 := by decide
  rw [this, h3, one_mul]

section Good

variable {Z Q : Subgroup G}

theorem IsGoodIn.comm_central (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) {x y : G} (hx : x ∈ Q)
    (hy : y ∈ Q) : ⁅x, y⁆ ∈ Subgroup.center G :=
  hZ.central (hQ.1 x hx y hy)

theorem IsGoodIn.mul_pow_three (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) {x y : G} (hx : x ∈ Q)
    (hy : y ∈ Q) : (x * y) ^ 3 = x ^ 3 * y ^ 3 :=
  mul_pow_three_of_central (hQ.comm_central hZ hx hy) (hZ.cube _ (hQ.1 x hx y hy))

theorem IsGoodIn.pow_nine (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) {x : G} (hx : x ∈ Q) :
    x ^ 9 = 1 := by
  have := hZ.cube _ (hQ.2 x hx)
  rwa [← pow_mul] at this

theorem isPGroup_three_of_pow_nine (H : Subgroup G) (h : ∀ x ∈ H, x ^ 9 = 1) : IsPGroup 3 H :=
  fun x => ⟨2, Subtype.ext (by simpa using h x x.2)⟩

@[expose] def commHomRight (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) {g : G} (hg : g ∈ Q) :
    Q →* Z where
  toFun x := ⟨⁅g, (x : G)⁆, hQ.1 g hg x x.2⟩
  map_one' := Subtype.ext (commutatorElement_one_right g)
  map_mul' x y := Subtype.ext (commutator_mul_right_of_central (hQ.comm_central hZ hg y.2))

@[expose] def commHomLeft (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) {h : G} (hh : h ∈ Q) :
    Q →* Z where
  toFun x := ⟨⁅(x : G), h⁆, hQ.1 x x.2 h hh⟩
  map_one' := Subtype.ext (commutatorElement_one_left h)
  map_mul' x y := Subtype.ext (commutator_mul_left_of_central (hQ.comm_central hZ y.2 hh)
    (hQ.comm_central hZ x.2 hh))

@[expose] def cubeHom (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) : Q →* Z where
  toFun x := ⟨x ^ 3, hQ.2 x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (hQ.mul_pow_three hZ x.2 y.2)

theorem card_le_three_mul_card_ker [Finite G] (hZ : ScalarLike Z) (φ : Q →* Z) :
    Nat.card Q ≤ 3 * Nat.card φ.ker := by
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ≤ 3 :=
    (Subgroup.card_le_card_group φ.range).trans hZ.card_le
  have : Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 3 :=
    Nat.mul_le_mul_left _ h2
  omega

theorem exists_centralizer_of_good [Finite G] (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) {g : G}
    (hg : g ∈ Q) :
    ∃ C : Subgroup G, C ≤ Q ∧ (∀ x ∈ C, g * x = x * g) ∧ Nat.card Q ≤ 3 * Nat.card C := by
  refine ⟨(commHomRight hZ hQ hg).ker.map Q.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : ⁅g, (x : G)⁆ = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      simpa [commHomRight] using this
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact card_le_three_mul_card_ker hZ _

theorem exists_cube_kernel_of_good [Finite G] (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) :
    ∃ T : Subgroup G, T ≤ Q ∧ (∀ x ∈ T, x ^ 3 = 1) ∧ (∀ x ∈ Q, x ^ 3 = 1 → x ∈ T) ∧
      Nat.card Q ≤ 3 * Nat.card T := by
  refine ⟨(cubeHom hZ hQ).ker.map Q.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    simpa [cubeHom] using this
  · intro x hx h3
    exact ⟨⟨x, hx⟩, MonoidHom.mem_ker.2 (Subtype.ext (by simpa [cubeHom] using h3)), rfl⟩
  · rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact card_le_three_mul_card_ker hZ _

theorem eq_or_eq_inv_of_card_le [Finite G] (hZ : ScalarLike Z) {a b : G} (ha : a ∈ Z)
    (hb : b ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b ∨ a = b⁻¹ := by
  have hb3 : b ^ 3 = 1 := hZ.cube b hb
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hcard : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers b ≤ Z := (Subgroup.zpowers_le).2 hb
  have heq : Subgroup.zpowers b = Z := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard]
    exact hZ.card_le
  have haz : a ∈ Subgroup.zpowers b := heq ▸ ha
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 haz
  have hk' : b ^ (k % 3) = a := by
    have := zpow_mod_orderOf b k
    rw [hord] at this
    rw [← hk, ← this]
    rfl
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · rw [h, zpow_zero] at hk'
    exact absurd hk'.symm ha1
  · left
    rw [h, zpow_one] at hk'
    exact hk'.symm
  · right
    rw [h] at hk'
    rw [← hk', zpow_two]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hb3)

theorem exists_pow_three_eq_one_noncomm [Finite G] (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q)
    (hnc : ¬ ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    ∃ g ∈ Q, ∃ h ∈ Q, g ^ 3 = 1 ∧ g * h ≠ h * g := by
  push Not at hnc
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  by_cases hx3 : x ^ 3 = 1
  · exact ⟨x, hx, y, hy, hx3, hxy⟩
  by_cases hy3 : y ^ 3 = 1
  · exact ⟨y, hy, x, hx, hy3, fun h => hxy h.symm⟩
  have ha : x ^ 3 ∈ Z := hQ.2 x hx
  have hb : y ^ 3 ∈ Z := hQ.2 y hy
  have hbc : ∀ g : G, g * y ^ 3 = y ^ 3 * g := fun g => Subgroup.mem_center_iff.1 (hZ.central hb) g
  have hb3 : (y ^ 3) ^ 3 = 1 := hZ.cube _ hb
  rcases eq_or_eq_inv_of_card_le hZ ha hb hx3 hy3 with h | h
  ·
    refine ⟨x * y ^ 2, mul_mem hx (pow_mem hy 2), x, hx, ?_, ?_⟩
    · rw [hQ.mul_pow_three hZ hx (pow_mem hy 2), h, ← pow_mul, mul_comm 2 3, pow_mul]
      calc (y ^ 3) * (y ^ 3) ^ 2 = (y ^ 3) ^ 3 := by rw [pow_succ' (y ^ 3) 2]
        _ = 1 := hb3
    · intro hc
      have h1 : y ^ 2 * x = x * y ^ 2 := by
        have : x * (y ^ 2 * x) = x * (x * y ^ 2) := by
          simpa only [mul_assoc] using hc
        exact mul_left_cancel this
      have h2 : y ^ 4 * x = x * y ^ 4 := by
        calc y ^ 4 * x = y ^ 2 * (y ^ 2 * x) := by rw [← mul_assoc, ← pow_add]
          _ = y ^ 2 * (x * y ^ 2) := by rw [h1]
          _ = (y ^ 2 * x) * y ^ 2 := by rw [mul_assoc]
          _ = (x * y ^ 2) * y ^ 2 := by rw [h1]
          _ = x * y ^ 4 := by rw [mul_assoc, ← pow_add]
      apply hxy
      have h3 : y ^ 4 = y * y ^ 3 := by rw [← pow_succ']
      have h4 : (y * x) * y ^ 3 = (x * y) * y ^ 3 := by
        calc (y * x) * y ^ 3 = y * (x * y ^ 3) := by rw [mul_assoc]
          _ = y * (y ^ 3 * x) := by rw [hbc x]
          _ = y ^ 4 * x := by rw [h3, mul_assoc]
          _ = x * y ^ 4 := h2
          _ = (x * y) * y ^ 3 := by rw [h3, mul_assoc]
      exact (mul_right_cancel h4).symm
  ·
    refine ⟨x * y, mul_mem hx hy, x, hx, ?_, ?_⟩
    · rw [hQ.mul_pow_three hZ hx hy, h, inv_mul_cancel]
    · intro hc
      have : x * (y * x) = x * (x * y) := by simpa only [mul_assoc] using hc
      exact hxy (mul_left_cancel this).symm

end Good

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

end
