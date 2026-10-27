module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Semidihedral.ParameterFive

section Coordinates

variable {X : Type*} [Group X] {n k : X}

theorem pow_mul_pow_mul (hnk : Commute n k) (i j i' j' : ℕ) :
    n ^ i * k ^ j * (n ^ i' * k ^ j') = n ^ (i + i') * k ^ (j + j') := by
  have h : k ^ j * n ^ i' = n ^ i' * k ^ j := ((hnk.pow_pow i' j).eq).symm
  rw [pow_add, pow_add, mul_assoc, ← mul_assoc (k ^ j), h, mul_assoc, ← mul_assoc]

theorem pow_mul_pow_pow (hnk : Commute n k) (i j x : ℕ) :
    (n ^ i * k ^ j) ^ x = n ^ (i * x) * k ^ (j * x) := by
  rw [(hnk.pow_pow i j).mul_pow, pow_mul, pow_mul]

theorem conj_pow_mul_pow (hnk : Commute n k) (g : X) {a b c e : ℕ}
    (hgn : g * n * g⁻¹ = n ^ a * k ^ b) (hgk : g * k * g⁻¹ = n ^ c * k ^ e) (x y : ℕ) :
    g * (n ^ x * k ^ y) * g⁻¹ = n ^ (a * x + c * y) * k ^ (b * x + e * y) := by
  have h1 : g * (n ^ x * k ^ y) * g⁻¹ = (g * n * g⁻¹) ^ x * (g * k * g⁻¹) ^ y := by
    simp only [← MulAut.conj_apply, map_mul, map_pow]
  rw [h1, hgn, hgk, pow_mul_pow_pow hnk, pow_mul_pow_pow hnk, pow_mul_pow_mul hnk]

theorem coord_eq (hn : n ^ 3 = 1) (hk : k ^ 3 = 1) (hnk : Commute n k)
    (hind : ∀ i j : ℕ, n ^ i * k ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) {i j i' j' : ℕ}
    (h : n ^ i * k ^ j = n ^ i' * k ^ j') : (i : ZMod 3) = i' ∧ (j : ZMod 3) = j' := by
  have h1 : n ^ (i + 2 * i') * k ^ (j + 2 * j') = 1 := by
    have e1 : n ^ (i + 2 * i') * k ^ (j + 2 * j') = n ^ i * k ^ j * (n ^ (2 * i') * k ^ (2 * j')) :=
      (pow_mul_pow_mul hnk _ _ _ _).symm
    have e2 : n ^ i' * k ^ j' * (n ^ (2 * i') * k ^ (2 * j')) = 1 := by
      rw [pow_mul_pow_mul hnk, show i' + 2 * i' = 3 * i' by ring,
        show j' + 2 * j' = 3 * j' by ring, pow_mul, pow_mul, hn, hk, one_pow, one_pow, one_mul]
    rw [e1, h, e2]
  obtain ⟨hi, hj⟩ := hind _ _ h1
  have hi' := (ZMod.natCast_eq_zero_iff _ 3).mpr hi
  have hj' := (ZMod.natCast_eq_zero_iff _ 3).mpr hj
  push_cast at hi' hj'
  have h3 : (3 : ZMod 3) = 0 := by decide
  constructor
  · linear_combination hi' - (i' : ZMod 3) * h3
  · linear_combination hj' - (j' : ZMod 3) * h3

end Coordinates

theorem zmod_three_action : ∀ a b c e f : ZMod 3, b ≠ 0 →
    a * a + c * (f * b) = 1 → b * a + e * (f * b) = 0 →
    a * c + c * (f * e) = 0 → b * c + e * (f * e) = f →
    a * (a * a + c * b) + c * (b * a + e * b) = 1 →
    a = 1 ∧ c = 0 := by
  decide

theorem threeAction_coords {X : Type*} [Group X] {n k η d : X}
    (hn : n ^ 3 = 1) (hk : k ^ 3 = 1) (hnk : Commute n k)
    (hind : ∀ i j : ℕ, n ^ i * k ^ j = 1 → 3 ∣ i ∧ 3 ∣ j)
    {a b c e f : ℕ}
    (hηn : η * n * η⁻¹ = n ^ a * k ^ b) (hηk : η * k * η⁻¹ = n ^ c * k ^ e)
    (hdn : d * n * d⁻¹ = n) (hdk : d * k * d⁻¹ = k ^ f)
    (h3 : η ^ 3 * n * (η ^ 3)⁻¹ = n)
    (hrn : (η * d * η) * n * (η * d * η)⁻¹ = d * n * d⁻¹)
    (hrk : (η * d * η) * k * (η * d * η)⁻¹ = d * k * d⁻¹)
    (hb : ¬ 3 ∣ b) : (a : ZMod 3) = 1 ∧ (c : ZMod 3) = 0 := by
  have hη := conj_pow_mul_pow hnk η hηn hηk
  have hdn' : d * n * d⁻¹ = n ^ 1 * k ^ (f * 0) := by rw [hdn]; simp
  have hdk' : d * k * d⁻¹ = n ^ 0 * k ^ (f * 1) := by rw [hdk]; simp
  have hd : ∀ x y : ℕ, d * (n ^ x * k ^ y) * d⁻¹ = n ^ x * k ^ (f * y) := by
    intro x y
    rw [conj_pow_mul_pow hnk d hdn' hdk' x y]
    ring_nf
  have hn1 : n = n ^ 1 * k ^ 0 := by simp
  have hk1 : k = n ^ 0 * k ^ 1 := by simp
  have e1 : n ^ (a * a + c * (f * b)) * k ^ (b * a + e * (f * b)) = n ^ 1 * k ^ 0 := by
    rw [← hη, ← hd, ← hηn, ← hn1]
    calc η * (d * (η * n * η⁻¹) * d⁻¹) * η⁻¹ = (η * d * η) * n * (η * d * η)⁻¹ := by group
      _ = n := by rw [hrn, hdn]
  have e2 : n ^ (a * c + c * (f * e)) * k ^ (b * c + e * (f * e)) = n ^ 0 * k ^ f := by
    rw [← hη, ← hd, ← hηk]
    calc η * (d * (η * k * η⁻¹) * d⁻¹) * η⁻¹ = (η * d * η) * k * (η * d * η)⁻¹ := by group
      _ = n ^ 0 * k ^ f := by rw [hrk, hdk]; simp
  have e3 : n ^ (a * (a * a + c * b) + c * (b * a + e * b)) *
      k ^ (b * (a * a + c * b) + e * (b * a + e * b)) = n ^ 1 * k ^ 0 := by
    have hη2 : η * (η * n * η⁻¹) * η⁻¹ = n ^ (a * a + c * b) * k ^ (b * a + e * b) := by
      rw [hηn, hη]
    rw [← hη, ← hη2, ← hn1]
    rw [pow_three'] at h3
    calc η * (η * (η * n * η⁻¹) * η⁻¹) * η⁻¹ = η * η * η * n * (η * η * η)⁻¹ := by group
      _ = n := h3
  obtain ⟨e1a, e1b⟩ := coord_eq hn hk hnk hind e1
  obtain ⟨e2a, e2b⟩ := coord_eq hn hk hnk hind e2
  obtain ⟨e3a, -⟩ := coord_eq hn hk hnk hind e3
  push_cast at e1a e1b e2a e2b e3a
  have hb' : (b : ZMod 3) ≠ 0 := fun h => hb ((ZMod.natCast_eq_zero_iff b 3).mp h)
  exact zmod_three_action _ _ _ _ _ hb' e1a e1b e2a e2b e3a

theorem pow_eq_pow_of_natCast_eq {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) {i j : ℕ}
    (h : (i : ZMod 3) = j) : x ^ i = x ^ j := by
  have hij : i % 3 = j % 3 := (ZMod.natCast_eq_natCast_iff' i j 3).mp h
  rw [← Nat.mod_add_div i 3, ← Nat.mod_add_div j 3]
  simp only [pow_add, pow_mul, hx, one_pow, mul_one, hij]

theorem conj_mul_inv_mem_zpowers {X : Type*} [Group X] {n k η d : X}
    (hn : n ^ 3 = 1) (hk : k ^ 3 = 1) (hnk : Commute n k)
    (hind : ∀ i j : ℕ, n ^ i * k ^ j = 1 → 3 ∣ i ∧ 3 ∣ j)
    {a b c e f : ℕ}
    (hηn : η * n * η⁻¹ = n ^ a * k ^ b) (hηk : η * k * η⁻¹ = n ^ c * k ^ e)
    (hdn : d * n * d⁻¹ = n) (hdk : d * k * d⁻¹ = k ^ f)
    (h3 : η ^ 3 * n * (η ^ 3)⁻¹ = n)
    (hrn : (η * d * η) * n * (η * d * η)⁻¹ = d * n * d⁻¹)
    (hrk : (η * d * η) * k * (η * d * η)⁻¹ = d * k * d⁻¹)
    (hb : ¬ 3 ∣ b) (i j : ℕ) :
    η * (n ^ i * k ^ j) * η⁻¹ * (n ^ i * k ^ j)⁻¹ ∈ Subgroup.zpowers k := by
  obtain ⟨ha, hc⟩ := threeAction_coords hn hk hnk hind hηn hηk hdn hdk h3 hrn hrk hb
  rw [conj_pow_mul_pow hnk η hηn hηk i j]
  have hni : n ^ (a * i + c * j) = n ^ i := by
    apply pow_eq_pow_of_natCast_eq hn
    push_cast
    rw [ha, hc]
    ring
  rw [hni]
  have hcomm : Commute (n ^ i) (k ^ (b * i + e * j) * (k ^ j)⁻¹) :=
    ((hnk.pow_right _).mul_right (hnk.pow_right _).inv_right).pow_left i
  have heq : n ^ i * k ^ (b * i + e * j) * (n ^ i * k ^ j)⁻¹ =
      k ^ (b * i + e * j) * (k ^ j)⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_assoc (n ^ i), hcomm.eq, mul_assoc, mul_inv_cancel,
      mul_one]
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _)
    (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _))

theorem klein_centralizer_thirtysix {G : Type*} [Group G] [Finite G] (V W₀ : Subgroup G)
    (hV : IsKleinFour V) (hD : Nat.card (Subgroup.centralizer (V : Set G)) = 36)
    (hW₀D : W₀ ≤ Subgroup.centralizer (V : Set G)) (hW₀ : Nat.card W₀ = 9) :
    V ⊔ W₀ = Subgroup.centralizer (V : Set G) ∧
      (∀ x ∈ Subgroup.centralizer (V : Set G), ∀ y ∈ Subgroup.centralizer (V : Set G),
        x * y = y * x) ∧
      ∀ x ∈ Subgroup.centralizer (V : Set G), x ^ 3 = 1 → x ∈ W₀ := by
  set D := Subgroup.centralizer (V : Set G) with hDdef
  have hV4 : Nat.card V = 4 := hV.card_four
  have hVcomm : ∀ a b : V, a * b = b * a := mul_comm_of_exponent_two hV.exponent_two
  have hVD : V ≤ D := fun x hx y hy => by
    have h := hVcomm ⟨y, hy⟩ ⟨x, hx⟩
    exact congrArg Subtype.val h
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW₀comm : ∀ a b : W₀, a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := W₀)
      (by rw [hW₀]; norm_num)).is_comm.comm a b
  have hsup : V ⊔ W₀ = D := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hVD hW₀D)
    rw [hD]
    have h4 : 4 ∣ Nat.card (V ⊔ W₀ : Subgroup G) := hV4 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h9 : 9 ∣ Nat.card (V ⊔ W₀ : Subgroup G) := hW₀ ▸ Subgroup.card_dvd_of_le le_sup_right
    have h36 : 36 ∣ Nat.card (V ⊔ W₀ : Subgroup G) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 9) h4 h9
    exact Nat.le_of_dvd Nat.card_pos h36
  have hVW : V ≤ Subgroup.centralizer (W₀ : Set G) := Subgroup.le_centralizer_iff.mpr hW₀D
  have hDW : D ≤ Subgroup.centralizer (W₀ : Set G) := by
    rw [← hsup]
    refine sup_le hVW fun x hx y hy => ?_
    exact congrArg Subtype.val (hW₀comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hDD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    rw [← hsup] at hy
    have hyc : y ∈ Subgroup.centralizer ({x} : Set G) := by
      have hle : V ⊔ W₀ ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (fun v hv => ?_) (fun w hw => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hx v hv
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact hDW hx w hw
      exact hle hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    exact hyc.symm
  have hDcomm : ∀ a b : D, a * b = b * a := fun a b => Subtype.ext (hDD a a.2 b b.2)
  refine ⟨hsup, hDD, ?_⟩
  have hW₀n : (W₀.subgroupOf D).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hDcomm g x, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  have hW₀card : Nat.card (W₀.subgroupOf D) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₀D).toEquiv, hW₀]
  intro x hx hx3
  let x' : D := ⟨x, hx⟩
  have hQ : Nat.card (D ⧸ W₀.subgroupOf D) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (W₀.subgroupOf D)
    rw [hD, hW₀card] at h
    omega
  have hq4 : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 4 = 1 := by
    rw [← hQ]
    exact pow_card_eq_one'
  have hq3 : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, QuotientGroup.mk_one]
  have hq1 : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) = 1 := by
    have : (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) =
        (QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 4 *
          ((QuotientGroup.mk x' : D ⧸ W₀.subgroupOf D) ^ 3)⁻¹ := by group
    rw [this, hq4, hq3, inv_one, mul_one]
  rw [QuotientGroup.eq_one_iff] at hq1
  exact hq1

end CFSG.Semidihedral.ParameterFive
