module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeAdic
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeSylow

public section

namespace CFSG.Semidihedral.UnitaryDValue

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

structure Exceptional where
  u₀ : G
  u₁ : G
  s₀ : ℤ
  hk : (Nat.card D.A).factorization 3 = 1
  hh : 3 ≤ (D.q + 1).factorization 3
  hu₀ : D.PW 3 = Subgroup.zpowers u₀
  hu₀o : orderOf u₀ = 3 ^ (D.q + 1).factorization 3
  hu₁ : D.PA 3 = Subgroup.zpowers u₁
  hu₁o : orderOf u₁ = 3
  hs₀ : ¬ (3 : ℤ) ∣ s₀
  ht₀ : D.t * u₀ * D.t⁻¹ = u₀ ^ (1 + 3 ^ ((D.q + 1).factorization 3 - 1) * s₀) * u₁
  ht₁ : D.t * u₁ * D.t⁻¹ = u₀ ^ (-(3 ^ ((D.q + 1).factorization 3 - 1) * s₀)) * u₁

theorem exists_exceptional (hext : D.CharacterExtend) (htriv : D.CharacterTrivial)
    (hk : (Nat.card D.A).factorization 3 = 1) (hh : 3 ≤ (D.q + 1).factorization 3) :
    Nonempty D.Exceptional := by
  have h3A : 3 ∣ Nat.card D.A :=
    (Nat.prime_three.dvd_iff_one_le_factorization D.card_A_pos.ne').mpr (by omega)
  rcases D.three_adic hext htriv h3A with h | ⟨-, -, u₀, u₁, s₀, h1, h2, h3, h4, h5, h6, h7⟩
  · omega
  · exact ⟨⟨u₀, u₁, s₀, hk, hh, h1, h2, h3, h4, h5, h6, h7⟩⟩

theorem t_pow_conj_mod {u : G} (hu : u ∈ D.C) (j r : ℕ) :
    D.t ^ (3 * j + r) * u * (D.t ^ (3 * j + r))⁻¹ = D.t ^ r * u * (D.t ^ r)⁻¹ := by
  rw [pow_add, conj_mul_eq, pow_mul]
  exact D.C_conj (D.C.pow_mem D.t_cube_mem_C j)
    (D.conj_mem_C (pow_mem D.t_mem_normalizer_T r) hu)

theorem tThree_conj_C {u : G} (hu : u ∈ D.C) : D.tThree * u * D.tThree⁻¹ = D.t * u * D.t⁻¹ := by
  have he := D.threeExponent_mod
  have h1 : D.tThree = D.t ^ (3 * (D.threeExponent / 3) + 1) := by
    show D.t ^ D.threeExponent = _
    congr 1
    omega
  rw [h1, D.t_pow_conj_mod hu, pow_one]

theorem tThree_pow_conj_C {u : G} (hu : u ∈ D.C) (n : ℕ) :
    D.tThree ^ n * u * (D.tThree ^ n)⁻¹ = D.t ^ n * u * (D.t ^ n)⁻¹ := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', conj_mul_eq, conj_mul_eq, ih hu,
      D.tThree_conj_C (D.conj_mem_C (pow_mem D.t_mem_normalizer_T n) hu)]

@[expose] def QT : Subgroup G where
  carrier := {g | ∃ u ∈ D.primaryPart 3, ∃ i : ℤ, g = u * D.tThree ^ i}
  one_mem' := ⟨1, (D.primaryPart 3).one_mem, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, i, rfl⟩ ⟨v, hv, j, rfl⟩
    refine ⟨u * (D.tThree ^ i * v * (D.tThree ^ i)⁻¹), (D.primaryPart 3).mul_mem hu
      (D.conj_mem_primaryPart (zpow_mem D.tThree_mem_normalizer_T i) hv), i + j, ?_⟩
    rw [zpow_add]
    group
  inv_mem' := by
    rintro _ ⟨u, hu, i, rfl⟩
    refine ⟨D.tThree ^ (-i) * u⁻¹ * (D.tThree ^ (-i))⁻¹,
      D.conj_mem_primaryPart (zpow_mem D.tThree_mem_normalizer_T (-i))
        ((D.primaryPart 3).inv_mem hu), -i, ?_⟩
    group

theorem mem_QT {g : G} : g ∈ D.QT ↔ ∃ u ∈ D.primaryPart 3, ∃ i : ℤ, g = u * D.tThree ^ i :=
  Iff.rfl

theorem P_le_QT : D.primaryPart 3 ≤ D.QT := fun u hu => ⟨u, hu, 0, by simp⟩

theorem tThree_mem_QT : D.tThree ∈ D.QT := ⟨1, (D.primaryPart 3).one_mem, 1, by simp⟩

theorem QT_le_normalizer_T : D.QT ≤ Subgroup.normalizer (D.T : Set G) := by
  rintro _ ⟨u, hu, i, rfl⟩
  exact mul_mem (D.C_le_normalizer_T (D.primaryPart_le_C 3 hu))
    (zpow_mem D.tThree_mem_normalizer_T i)

theorem QT_le_CT : D.QT ≤ D.CT := by
  rintro _ ⟨u, hu, i, rfl⟩
  refine ⟨u, D.primaryPart_le_C 3 hu, D.threeExponent * i, ?_⟩
  rw [zpow_mul, zpow_natCast]
  rfl

theorem cube_mem_P_of_mem_QT {g : G} (hg : g ∈ D.QT) : g ^ 3 ∈ D.primaryPart 3 := by
  obtain ⟨u, hu, i, rfl⟩ := hg
  have e : (u * D.tThree ^ i) ^ 3 = u * (D.tThree ^ i * u * (D.tThree ^ i)⁻¹) *
      (D.tThree ^ (2 * i) * u * (D.tThree ^ (2 * i))⁻¹) * (D.tThree ^ 3) ^ i := by
    rw [pow_three, ← zpow_natCast, ← zpow_mul]
    push_cast
    rw [show (2 : ℤ) * i = i + i by ring, show (3 : ℤ) * i = i + i + i by ring, zpow_add,
      zpow_add, zpow_add]
    group
  rw [e]
  have hP := D.primaryPart 3
  refine (D.primaryPart 3).mul_mem ((D.primaryPart 3).mul_mem ((D.primaryPart 3).mul_mem hu
    (D.conj_mem_primaryPart (zpow_mem D.tThree_mem_normalizer_T i) hu))
    (D.conj_mem_primaryPart (zpow_mem D.tThree_mem_normalizer_T _) hu))
    ((D.primaryPart 3).zpow_mem D.tThree_cube_mem_P3 i)

theorem three_element_of_mem_QT {g : G} (hg : g ∈ D.QT) : ∃ k : ℕ, orderOf g = 3 ^ k := by
  obtain ⟨c, hc⟩ := (D.cube_mem_P_of_mem_QT hg).2
  have h1 : g ^ (3 ^ (c + 1)) = 1 := by
    rw [pow_succ', pow_mul, ← hc, pow_orderOf_eq_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨k, hk⟩

theorem isPGroup_QT : IsPGroup 3 D.QT := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨k, hk⟩ := D.three_element_of_mem_QT hg
  exact ⟨k, (Subgroup.orderOf_coe _).symm.trans hk⟩

theorem card_QT (h3 : 3 ∣ D.q + 1) : Nat.card D.QT = 3 ^ (Nat.card G).factorization 3 := by
  obtain ⟨a, ha⟩ := D.isPGroup_QT.exists_card_eq
  rw [ha]
  congr 1
  have hG : (Nat.card G).factorization 3 = (Nat.card D.A).factorization 3 +
      (D.q + 1).factorization 3 + 1 := by
    rw [D.factorization_card_G Nat.prime_three (by norm_num) h3, D.three_factorization_Q h3]
  have h1 : 3 ^ a ∣ Nat.card G := ha ▸ Subgroup.card_subgroup_dvd_card _
  have h1' : a ≤ (Nat.card G).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h1
  have h2 : Nat.card (D.primaryPart 3) ∣ Nat.card D.QT := Subgroup.card_dvd_of_le D.P_le_QT
  rw [D.card_primaryPart_odd (by norm_num), ha] at h2
  have h2' := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have hne : (Nat.card D.A).factorization 3 + (D.q + 1).factorization 3 ≠ a := by
    intro heq
    apply D.tThree_not_mem_P3
    have hcard : Nat.card D.QT ≤ Nat.card (D.primaryPart 3) := by
      rw [ha, D.card_primaryPart_odd (by norm_num), heq]
    rw [Subgroup.eq_of_le_of_card_ge D.P_le_QT hcard]
    exact D.tThree_mem_QT
  omega

noncomputable def sylowQT (h3 : 3 ∣ D.q + 1) : Sylow 3 G := Sylow.ofCard D.QT (D.card_QT h3)

theorem coe_sylowQT (h3 : 3 ∣ D.q + 1) : ((D.sylowQT h3 : Sylow 3 G) : Subgroup G) = D.QT :=
  Sylow.coe_ofCard _ _

theorem exists_of_mem_QT_not_mem_P {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) :
    ∃ u ∈ D.primaryPart 3, ∃ i : ℤ, ¬ (3 : ℤ) ∣ i ∧ v = u * D.tThree ^ i := by
  obtain ⟨u, hu, i, rfl⟩ := hv
  refine ⟨u, hu, i, fun h3 => hvP ((D.primaryPart 3).mul_mem hu (D.tThree_zpow_mem_P3 h3)), rfl⟩

namespace Exceptional

variable {D} (E : D.Exceptional)

abbrev h (_E : D.Exceptional) : ℕ := (D.q + 1).factorization 3

abbrev l (E : D.Exceptional) : ℤ := 3 ^ (E.h - 1)

abbrev Z : Subgroup G := Subgroup.zpowers (E.u₀ ^ 3)

theorem h_def : E.h = (D.q + 1).factorization 3 := rfl

include E in
theorem three_dvd_q : 3 ∣ D.q + 1 := by
  have := E.hh
  exact (Nat.prime_three.dvd_iff_one_le_factorization (by omega)).mpr (by omega)

theorem three_le_h : 3 ≤ E.h := E.hh

theorem u₀_mem_PW : E.u₀ ∈ D.PW 3 := E.hu₀ ▸ Subgroup.mem_zpowers E.u₀

theorem u₁_mem_PA : E.u₁ ∈ D.PA 3 := E.hu₁ ▸ Subgroup.mem_zpowers E.u₁

theorem u₀_mem_W : E.u₀ ∈ D.W := D.PW_le_W E.u₀_mem_PW

theorem u₁_mem_A : E.u₁ ∈ D.A := D.PA_le_A E.u₁_mem_PA

theorem u₀_mem_C : E.u₀ ∈ D.C := D.W_le E.u₀_mem_W

theorem u₁_mem_C : E.u₁ ∈ D.C := D.A_le_C E.u₁_mem_A

theorem u₀_mem_P : E.u₀ ∈ D.primaryPart 3 := D.PW_le E.u₀_mem_PW

theorem u₁_mem_P : E.u₁ ∈ D.primaryPart 3 := D.PA_le E.u₁_mem_PA

theorem comm : Commute E.u₀ E.u₁ := D.C_comm _ E.u₀_mem_C _ E.u₁_mem_C

theorem disj : ∀ i j : ℤ, E.u₀ ^ i = E.u₁ ^ j → E.u₀ ^ i = 1 := by
  intro i j hij
  have h1 : E.u₀ ^ i ∈ D.PW 3 ⊓ D.PA 3 :=
    ⟨(D.PW 3).zpow_mem E.u₀_mem_PW i, hij ▸ (D.PA 3).zpow_mem E.u₁_mem_PA j⟩
  rw [D.disjoint_PW_PA.eq_bot] at h1
  exact h1

theorem coord (i j i' j' : ℤ) :
    E.u₀ ^ i * E.u₁ ^ j = E.u₀ ^ i' * E.u₁ ^ j' ↔ (3 : ℤ) ^ E.h ∣ i - i' ∧ (3 : ℤ) ∣ j - j' := by
  rw [zpow_mul_zpow_eq_iff E.comm E.disj, E.hu₀o, E.hu₁o]
  push_cast
  rfl

theorem coord_one (i j : ℤ) :
    E.u₀ ^ i * E.u₁ ^ j = 1 ↔ (3 : ℤ) ^ E.h ∣ i ∧ (3 : ℤ) ∣ j := by
  rw [zpow_mul_zpow_eq_one_iff_of_disjoint E.disj, E.hu₀o, E.hu₁o]
  push_cast
  rfl

theorem exists_coord {u : G} (hu : u ∈ D.primaryPart 3) : ∃ i j : ℤ, u = E.u₀ ^ i * E.u₁ ^ j := by
  obtain ⟨w, hw, a, ha, rfl⟩ := D.exists_mul_eq (by norm_num) hu
  rw [E.hu₀] at hw
  rw [E.hu₁] at ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ⟨i, j, rfl⟩

theorem coord_mem_P (i j : ℤ) : E.u₀ ^ i * E.u₁ ^ j ∈ D.primaryPart 3 :=
  (D.primaryPart 3).mul_mem ((D.primaryPart 3).zpow_mem E.u₀_mem_P i)
    ((D.primaryPart 3).zpow_mem E.u₁_mem_P j)

theorem ht₀' : D.t * E.u₀ * D.t⁻¹ = E.u₀ ^ (1 + E.l * E.s₀) * E.u₁ ^ (1 : ℤ) := by
  rw [zpow_one]
  exact E.ht₀

theorem ht₁' : D.t * E.u₁ * D.t⁻¹ = E.u₀ ^ (-(E.l * E.s₀)) * E.u₁ ^ (1 : ℤ) := by
  rw [zpow_one]
  exact E.ht₁

theorem t_conj (a b : ℤ) : D.t * (E.u₀ ^ a * E.u₁ ^ b) * D.t⁻¹ =
    E.u₀ ^ ((1 + E.l * E.s₀) * a + (-(E.l * E.s₀)) * b) * E.u₁ ^ (1 * a + 1 * b) :=
  conj_zpow_mul_zpow E.comm E.ht₀' E.ht₁' a b

theorem l_mul_l : (3 : ℤ) ^ E.h ∣ E.l * E.l := by
  rw [← pow_add]
  exact pow_dvd_pow 3 (by have := E.three_le_h; omega)

theorem three_mul_l : (3 : ℤ) * E.l = 3 ^ E.h := by
  rw [← pow_succ']
  congr 1
  have := E.three_le_h
  omega

theorem three_dvd_l : (3 : ℤ) ∣ E.l := dvd_pow_self 3 (by have := E.three_le_h; omega)

theorem t_fix_iff (a b : ℤ) :
    D.t * (E.u₀ ^ a * E.u₁ ^ b) * D.t⁻¹ = E.u₀ ^ a * E.u₁ ^ b ↔ (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b := by
  rw [E.t_conj, E.coord]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : (3 : ℤ) ∣ a := by
      have : 1 * a + 1 * b - b = a := by ring
      rw [this] at h2
      exact h2
    refine ⟨ha, ?_⟩
    have e : (1 + E.l * E.s₀) * a + -(E.l * E.s₀) * b - a = E.l * (E.s₀ * (a - b)) := by ring
    rw [e, ← E.three_mul_l, mul_comm (3 : ℤ)] at h1
    have h3 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp h1
    rcases Int.prime_three.dvd_or_dvd h3 with h4 | h4
    · exact absurd h4 E.hs₀
    · have := dvd_sub ha h4
      rwa [show a - (a - b) = b by ring] at this
  · rintro ⟨ha, hb⟩
    refine ⟨?_, ?_⟩
    · have e : (1 + E.l * E.s₀) * a + -(E.l * E.s₀) * b - a = E.l * (E.s₀ * (a - b)) := by ring
      rw [e, ← E.three_mul_l, mul_comm (3 : ℤ)]
      exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right (dvd_sub ha hb) _)
    · rw [show 1 * a + 1 * b - b = a by ring]
      exact ha

theorem u₀_cube_mem_Z : E.u₀ ^ 3 ∈ E.Z := Subgroup.mem_zpowers _

theorem Z_le_P : E.Z ≤ D.primaryPart 3 := by
  rw [Subgroup.zpowers_le]
  exact (D.primaryPart 3).pow_mem E.u₀_mem_P 3

theorem Z_le_W : E.Z ≤ D.W := by
  rw [Subgroup.zpowers_le]
  exact D.W.pow_mem E.u₀_mem_W 3

theorem Z_le_C : E.Z ≤ D.C := fun _ hz => D.primaryPart_le_C 3 (E.Z_le_P hz)

theorem mem_Z_iff_coord (a b : ℤ) :
    E.u₀ ^ a * E.u₁ ^ b ∈ E.Z ↔ (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b := by
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp hz
    have e : (E.u₀ ^ 3) ^ c = E.u₀ ^ (3 * c) * E.u₁ ^ (0 : ℤ) := by
      rw [zpow_zero, mul_one, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num,
        zpow_natCast]
    rw [e, E.coord] at hc
    refine ⟨?_, ?_⟩
    · have h1 := three_dvd_of_pow_dvd (by have := E.three_le_h; omega) hc.1
      have h2 := dvd_sub (dvd_mul_right (3 : ℤ) c) h1
      rwa [show 3 * c - (3 * c - a) = a by ring] at h2
    · have := hc.2
      rwa [show (0 : ℤ) - b = -b by ring, dvd_neg] at this
  · rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩
    have hb : E.u₁ ^ ((3 : ℤ) * b') = 1 := by
      rw [zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← E.hu₁o,
        pow_orderOf_eq_one, one_zpow]
    refine Subgroup.mem_zpowers_iff.mpr ⟨a', ?_⟩
    rw [hb, mul_one, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]

theorem mem_Z_iff {u : G} (hu : u ∈ D.primaryPart 3) : u ∈ E.Z ↔ D.t * u * D.t⁻¹ = u := by
  obtain ⟨a, b, rfl⟩ := E.exists_coord hu
  rw [E.mem_Z_iff_coord, E.t_fix_iff]

theorem t_conj_Z {z : G} (hz : z ∈ E.Z) : D.t * z * D.t⁻¹ = z :=
  (E.mem_Z_iff (E.Z_le_P hz)).mp hz

theorem t_comm_Z {z : G} (hz : z ∈ E.Z) : D.t * z = z * D.t :=
  comm_of_conj_eq (E.t_conj_Z hz)

theorem cube_mem_Z {u : G} (hu : u ∈ D.primaryPart 3) : u ^ 3 ∈ E.Z := by
  obtain ⟨a, b, rfl⟩ := E.exists_coord hu
  rw [E.comm.zpow_zpow a b |>.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    E.mem_Z_iff_coord]
  push_cast
  exact ⟨dvd_mul_left 3 a, dvd_mul_left 3 b⟩

theorem mem_Z_of_t_pow_fix {u : G} (hu : u ∈ D.primaryPart 3) {m : ℕ} (hm : ¬ 3 ∣ m)
    (hfix : D.t ^ m * u * (D.t ^ m)⁻¹ = u) : u ∈ E.Z := by
  have huC : u ∈ D.C := D.primaryPart_le_C 3 hu
  rw [E.mem_Z_iff hu]
  obtain ⟨j, hj⟩ : ∃ j, m = 3 * j + 1 ∨ m = 3 * j + 2 := ⟨m / 3, by omega⟩
  rcases hj with rfl | rfl
  · rw [D.t_pow_conj_mod huC, pow_one] at hfix
    exact hfix
  · rw [D.t_pow_conj_mod huC] at hfix
    have h3 : D.t ^ 3 * u * (D.t ^ 3)⁻¹ = u := D.C_conj D.t_cube_mem_C huC
    calc D.t * u * D.t⁻¹ = D.t * (D.t ^ 2 * u * (D.t ^ 2)⁻¹) * D.t⁻¹ := by rw [hfix]
      _ = D.t ^ 3 * u * (D.t ^ 3)⁻¹ := by
          rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, conj_mul_eq]
      _ = u := h3

theorem tThree_conj_Z {z : G} (hz : z ∈ E.Z) : D.tThree * z * D.tThree⁻¹ = z := by
  rw [D.tThree_conj_C (E.Z_le_C hz), E.t_conj_Z hz]

theorem tThree_zpow_comm_Z {z : G} (hz : z ∈ E.Z) (i : ℤ) :
    D.tThree ^ i * z = z * D.tThree ^ i :=
  (Commute.zpow_left (comm_of_conj_eq (E.tThree_conj_Z hz) : Commute D.tThree z) i).eq

theorem Z_comm_QT {z : G} (hz : z ∈ E.Z) {g : G} (hg : g ∈ D.QT) : g * z = z * g := by
  obtain ⟨u, hu, i, rfl⟩ := hg
  have huz : u * z = z * u :=
    D.C_comm u (D.primaryPart_le_C 3 hu) z (E.Z_le_C hz)
  rw [mul_assoc, E.tThree_zpow_comm_Z hz, ← mul_assoc, huz, mul_assoc]

theorem mem_Z_of_tThree_zpow_fix {p : G} (hp : p ∈ D.primaryPart 3) {i : ℤ} (hi : ¬ (3 : ℤ) ∣ i)
    (hfix : D.tThree ^ i * p * (D.tThree ^ i)⁻¹ = p) : p ∈ E.Z := by
  have hpC : p ∈ D.C := D.primaryPart_le_C 3 hp
  have hn : ¬ 3 ∣ i.natAbs := fun h => hi (Int.natCast_dvd.mpr h)
  have hfix' : D.tThree ^ i.natAbs * p * (D.tThree ^ i.natAbs)⁻¹ = p := by
    rcases Int.natAbs_eq i with h | h
    · rw [h, zpow_natCast] at hfix
      exact hfix
    · rw [h, zpow_neg, zpow_natCast, inv_inv] at hfix
      calc D.tThree ^ i.natAbs * p * (D.tThree ^ i.natAbs)⁻¹
          = D.tThree ^ i.natAbs * ((D.tThree ^ i.natAbs)⁻¹ * p * D.tThree ^ i.natAbs) *
              (D.tThree ^ i.natAbs)⁻¹ := by rw [hfix]
        _ = p := by group
  rw [D.tThree_pow_conj_C hpC] at hfix'
  exact E.mem_Z_of_t_pow_fix hp hn hfix'

theorem conj_fix_iff {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) {p : G}
    (hp : p ∈ D.primaryPart 3) : v * p * v⁻¹ = p ↔ p ∈ E.Z := by
  obtain ⟨u, hu, i, hi, rfl⟩ := D.exists_of_mem_QT_not_mem_P hv hvP
  have hτp : D.tThree ^ i * p * (D.tThree ^ i)⁻¹ ∈ D.C :=
    D.conj_mem_C (zpow_mem D.tThree_mem_normalizer_T i) (D.primaryPart_le_C 3 hp)
  have e : u * D.tThree ^ i * p * (u * D.tThree ^ i)⁻¹ = D.tThree ^ i * p * (D.tThree ^ i)⁻¹ := by
    rw [conj_mul_eq]
    exact D.C_conj (D.primaryPart_le_C 3 hu) hτp
  rw [e]
  constructor
  · exact E.mem_Z_of_tThree_zpow_fix hp hi
  · intro hz
    exact conj_eq_of_comm (E.tThree_zpow_comm_Z hz i)

theorem cube_mem_Z_of_mem_QT {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) :
    v ^ 3 ∈ E.Z :=
  (E.conj_fix_iff hv hvP (D.cube_mem_P_of_mem_QT hv)).mp
    (conj_eq_of_comm ((Commute.self_pow v 3).eq))

theorem card_QT_eq : Nat.card D.QT = 3 ^ (E.h + 2) := by
  rw [D.card_QT E.three_dvd_q, D.factorization_card_G Nat.prime_three (by norm_num)
    E.three_dvd_q, D.three_factorization_Q E.three_dvd_q, E.hk, E.h_def]
  congr 1
  omega

theorem card_P_eq : Nat.card (D.primaryPart 3) = 3 ^ (E.h + 1) := by
  rw [D.card_primaryPart_odd (by norm_num), E.hk, E.h_def]
  congr 1
  omega

theorem orderOf_u₀_cube : orderOf (E.u₀ ^ 3) = 3 ^ (E.h - 1) := by
  have hh := E.three_le_h
  rw [E.h_def] at hh ⊢
  rw [orderOf_pow' _ (by norm_num), E.hu₀o, Nat.gcd_eq_right (dvd_pow_self 3 (by omega)),
    show (3 : ℕ) ^ (D.q + 1).factorization 3 = 3 * 3 ^ ((D.q + 1).factorization 3 - 1) by
      rw [← pow_succ']; congr 1; omega, Nat.mul_div_cancel_left _ (by norm_num)]

theorem card_Z : Nat.card E.Z = 3 ^ (E.h - 1) := by
  rw [Nat.card_zpowers, E.orderOf_u₀_cube]

end Exceptional

end DValueData

end CFSG.Semidihedral.UnitaryDValue
