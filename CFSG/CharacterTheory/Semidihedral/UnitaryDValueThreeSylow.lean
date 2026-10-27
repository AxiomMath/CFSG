module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueBrauer
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueLine
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Semidihedral.UnitaryDValue

section General

variable {G : Type*} [Group G]

theorem mem_zpowers_pow_of_pow_eq_one {r : ℕ} (hr : 0 < r) {w₀ x : G} {h : ℕ} (hh : 1 ≤ h)
    (hw₀ : orderOf w₀ = r ^ h) (hx : x ∈ Subgroup.zpowers w₀) (hxr : x ^ (r ^ (h - 1)) = 1) :
    x ∈ Subgroup.zpowers (w₀ ^ r) := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hdvd : (orderOf w₀ : ℤ) ∣ n * (r ^ (h - 1) : ℕ) := by
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    rw [zpow_mul, zpow_natCast]
    exact hxr
  rw [hw₀] at hdvd
  have hsplit : ((r ^ h : ℕ) : ℤ) = r * (r ^ (h - 1) : ℕ) := by
    rw [← Nat.cast_mul, ← pow_succ', Nat.sub_add_cancel hh]
  rw [hsplit] at hdvd
  obtain ⟨c, hc⟩ := (mul_dvd_mul_iff_right (by positivity)).mp hdvd
  refine Subgroup.mem_zpowers_iff.mpr ⟨c, ?_⟩
  rw [hc, zpow_mul, zpow_natCast]

theorem pow_conj_eq_mul_pow {g s d : G} (h1 : g * s * g⁻¹ = s * d) (h2 : g * d * g⁻¹ = d)
    (j : ℕ) : g ^ j * s * (g ^ j)⁻¹ = s * d ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : g * (s * d ^ j) * g⁻¹ = g * s * g⁻¹ * (g * d * g⁻¹) ^ j := by
      rw [conj_pow]
      group
    rw [pow_succ', conj_mul_eq, ih, e, h1, h2, mul_assoc, ← pow_succ']

theorem pow_eq_one_of_conj_eq_mul {g s d : G} (h1 : g * s * g⁻¹ = s * d)
    (h2 : g * d * g⁻¹ = d) {m : ℕ} (hm : g ^ m * s * (g ^ m)⁻¹ = s) : d ^ m = 1 := by
  have h := pow_conj_eq_mul_pow h1 h2 m
  rw [hm] at h
  simpa using h.symm

theorem eq_one_of_pow_eq_one_of_not_dvd {p : ℕ} {d : G} {k m : ℕ} (hd : orderOf d = p ^ k)
    (hdm : d ^ m = 1) (hm : ¬ p ∣ m) : d = 1 := by
  have h1 : p ^ k ∣ m := hd ▸ orderOf_dvd_of_pow_eq_one hdm
  rcases k with _ | k
  · rw [pow_zero] at hd
    exact orderOf_eq_one_iff.mp hd
  · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans h1) hm

theorem pow_conj_eq_of_conj_eq {g s : G} (h : g * s * g⁻¹ = s) (j : ℕ) :
    g ^ j * s * (g ^ j)⁻¹ = s :=
  conj_eq_of_comm ((Commute.pow_left (comm_of_conj_eq h : Commute g s) j).eq)

theorem even_orderOf_of_conj_eq_inv {g z : G} (h : g * z * g⁻¹ = z⁻¹) (hz : z ^ 2 ≠ 1) :
    Even (orderOf g) := by
  by_contra hodd
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hodd
  have hg : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have h2 : g ^ 2 * z * (g ^ 2)⁻¹ = z := by
    rw [pow_two, conj_mul_eq, h, conj_inv_eq, h, inv_inv]
  have h3 := pow_conj_eq_of_conj_eq h2 (k + 1)
  rw [← hg, h] at h3
  apply hz
  rw [pow_two]
  nth_rw 1 [← h3]
  exact inv_mul_cancel z

theorem exists_pow_orderOf_eq_two [Finite G] {g : G} (hg : Even (orderOf g)) :
    orderOf (g ^ (orderOf g / 2)) = 2 :=
  orderOf_pow_orderOf_div (orderOf_pos g).ne' (even_iff_two_dvd.mp hg)

theorem relIndex_eq_two_of_act' {P : Subgroup G} {u₀ τ : G} (hu₀P : u₀ ∈ P) (hu₀ : u₀⁻¹ ≠ u₀)
    (hact : ∀ g ∈ Subgroup.normalizer (P : Set G),
      (∀ u ∈ P, g * u * g⁻¹ = u) ∨ (∀ u ∈ P, g * u * g⁻¹ = u⁻¹))
    (hτN : τ ∈ Subgroup.normalizer (P : Set G)) (hτ : ∀ u ∈ P, τ * u * τ⁻¹ = u⁻¹) :
    (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2 := by
  have hcent : ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) ↔ ∀ u ∈ P, g * u * g⁻¹ = u := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    exact ⟨fun h u hu => conj_eq_of_comm (h u hu).symm,
      fun h u hu => (comm_of_conj_eq (h u hu)).symm⟩
  have hnot : ∀ g : G, (∀ u ∈ P, g * u * g⁻¹ = u⁻¹) → g ∉ Subgroup.centralizer (P : Set G) := by
    intro g hg hgC
    apply hu₀
    rw [← hg u₀ hu₀P, (hcent g).mp hgC u₀ hu₀P]
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨τ, hτN⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases hact b b.2 with h | h
  · refine Or.inr ⟨(hcent b).mpr h, hnot _ fun u hu => ?_⟩
    rw [conj_mul_eq, hτ u hu, h _ (P.inv_mem hu)]
  · refine Or.inl ⟨(hcent _).mpr fun u hu => ?_, hnot _ h⟩
    rw [conj_mul_eq, hτ u hu, h _ (P.inv_mem hu), inv_inv]

theorem zpow_pow_comm' (a : G) (j : ℤ) (k : ℕ) : (a ^ j) ^ k = (a ^ k) ^ j := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm j, zpow_mul, zpow_natCast]

end General

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem toThree_t : D.toThree.t = D.tThree := rfl

theorem tThree_x : D.tThree * D.x * D.tThree⁻¹ = D.z := D.toThree.t_x

theorem tThree_z : D.tThree * D.z * D.tThree⁻¹ = D.x * D.z := D.toThree.t_z

theorem tThree_cube_mem_C : D.tThree ^ 3 ∈ D.C := D.toThree.t_cube_mem_C

theorem tThree_not_mem_C : D.tThree ∉ D.C := fun h =>
  D.z_ne ((D.tThree_x).symm.trans (D.mem_C_iff_conj.mp h).1)

theorem tThree_mem_normalizer_T : D.tThree ∈ Subgroup.normalizer (D.T : Set G) :=
  D.toThree.t_mem_normalizer_T

theorem tThree_conj_eq_of_le_W {P : Subgroup G} (hPW : P ≤ D.W)
    (htP : ∀ u ∈ P, D.t * u * D.t⁻¹ ∈ P) {u : G} (hu : u ∈ P) :
    D.tThree * u * D.tThree⁻¹ = u :=
  D.t_pow_conj_eq_of_le_W hPW htP _ hu

theorem P3_le_W (h3A : ¬ 3 ∣ Nat.card D.A) : D.primaryPart 3 ≤ D.W :=
  D.primaryPart_le_W_of_not_dvd (by norm_num) h3A

theorem tThree_comm_P3 (h3A : ¬ 3 ∣ Nat.card D.A) {u : G} (hu : u ∈ D.primaryPart 3) :
    D.tThree * u = u * D.tThree :=
  comm_of_conj_eq (D.tThree_conj_eq_of_le_W (D.P3_le_W h3A)
    (fun _ hv => D.t_conj_primaryPart hv) hu)

theorem tThree_zpow_comm_P3 (h3A : ¬ 3 ∣ Nat.card D.A) {u : G} (hu : u ∈ D.primaryPart 3)
    (i : ℤ) : D.tThree ^ i * u = u * D.tThree ^ i :=
  ((Commute.zpow_left (D.tThree_comm_P3 h3A hu) i)).eq

@[expose] def S3 (h3A : ¬ 3 ∣ Nat.card D.A) : Subgroup G where
  carrier := {g | ∃ u ∈ D.primaryPart 3, ∃ i : ℤ, g = u * D.tThree ^ i}
  one_mem' := ⟨1, (D.primaryPart 3).one_mem, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, i, rfl⟩ ⟨v, hv, j, rfl⟩
    refine ⟨u * v, (D.primaryPart 3).mul_mem hu hv, i + j, ?_⟩
    rw [zpow_add, mul_assoc, ← mul_assoc (D.tThree ^ i), D.tThree_zpow_comm_P3 h3A hv i]
    group
  inv_mem' := by
    rintro _ ⟨u, hu, i, rfl⟩
    refine ⟨u⁻¹, (D.primaryPart 3).inv_mem hu, -i, ?_⟩
    rw [mul_inv_rev, zpow_neg]
    have := D.tThree_zpow_comm_P3 h3A ((D.primaryPart 3).inv_mem hu) (-i)
    rw [zpow_neg] at this
    exact this

theorem mem_S3 (h3A : ¬ 3 ∣ Nat.card D.A) {g : G} :
    g ∈ D.S3 h3A ↔ ∃ u ∈ D.primaryPart 3, ∃ i : ℤ, g = u * D.tThree ^ i := Iff.rfl

theorem P3_le_S3 (h3A : ¬ 3 ∣ Nat.card D.A) : D.primaryPart 3 ≤ D.S3 h3A :=
  fun u hu => ⟨u, hu, 0, by simp⟩

theorem tThree_mem_S3 (h3A : ¬ 3 ∣ Nat.card D.A) : D.tThree ∈ D.S3 h3A :=
  ⟨1, (D.primaryPart 3).one_mem, 1, by simp⟩

theorem S3_comm (h3A : ¬ 3 ∣ Nat.card D.A) :
    ∀ a ∈ D.S3 h3A, ∀ b ∈ D.S3 h3A, a * b = b * a := by
  rintro _ ⟨u, hu, i, rfl⟩ _ ⟨v, hv, j, rfl⟩
  have huv : u * v = v * u := D.C_comm u (D.primaryPart_le_C 3 hu) v (D.primaryPart_le_C 3 hv)
  calc u * D.tThree ^ i * (v * D.tThree ^ j) = u * v * (D.tThree ^ i * D.tThree ^ j) := by
        rw [mul_assoc, ← mul_assoc (D.tThree ^ i), D.tThree_zpow_comm_P3 h3A hv i]
        group
    _ = v * u * (D.tThree ^ j * D.tThree ^ i) := by rw [huv, ← zpow_add, ← zpow_add, add_comm]
    _ = v * D.tThree ^ j * (u * D.tThree ^ i) := by
        rw [show v * D.tThree ^ j * (u * D.tThree ^ i) = v * (D.tThree ^ j * u) * D.tThree ^ i by
          group, D.tThree_zpow_comm_P3 h3A hu j]
        group

theorem isPGroup_S3 (h3A : ¬ 3 ∣ Nat.card D.A) : IsPGroup 3 (D.S3 h3A) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨_, u, hu, i, rfl⟩
  obtain ⟨-, a, ha⟩ := id hu
  obtain ⟨b, hb⟩ := D.tThree_order
  have hcomm : Commute u (D.tThree ^ i) := (D.tThree_zpow_comm_P3 h3A hu i).symm
  have hdvd : orderOf (u * D.tThree ^ i) ∣ 3 ^ max a b := by
    refine hcomm.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd ?_ ?_)
    · rw [ha]
      exact Nat.pow_dvd_pow 3 (le_max_left a b)
    · refine (orderOf_dvd_of_pow_eq_one (n := orderOf D.tThree) ?_).trans ?_
      · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
          one_zpow]
      · rw [hb]
        exact Nat.pow_dvd_pow 3 (le_max_right a b)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact ⟨k, (Subgroup.orderOf_coe _).symm.trans hk⟩

theorem tThree_not_mem_P3 : D.tThree ∉ D.primaryPart 3 :=
  fun h => D.tThree_not_mem_C (D.primaryPart_le_C 3 h)

theorem factorization_three_card_G (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) :
    (Nat.card G).factorization 3 = (D.q + 1).factorization 3 + 1 := by
  rw [D.factorization_card_G Nat.prime_three (by norm_num) h3,
    Nat.factorization_eq_zero_of_not_dvd h3A, D.three_factorization_Q h3, zero_add]

theorem card_P3 (h3A : ¬ 3 ∣ Nat.card D.A) :
    Nat.card (D.primaryPart 3) = 3 ^ (D.q + 1).factorization 3 := by
  rw [D.card_primaryPart_odd (by norm_num), Nat.factorization_eq_zero_of_not_dvd h3A, zero_add]

theorem card_S3 (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) :
    Nat.card (D.S3 h3A) = 3 ^ (Nat.card G).factorization 3 := by
  rw [D.factorization_three_card_G h3A h3]
  obtain ⟨a, ha⟩ := (D.isPGroup_S3 h3A).exists_card_eq
  rw [ha]
  congr 1
  have h1 : 3 ^ a ∣ Nat.card G := ha ▸ Subgroup.card_subgroup_dvd_card _
  have h1' : a ≤ (Nat.card G).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h1
  rw [D.factorization_three_card_G h3A h3] at h1'
  have h2 : Nat.card (D.primaryPart 3) ∣ Nat.card (D.S3 h3A) :=
    Subgroup.card_dvd_of_le (D.P3_le_S3 h3A)
  rw [D.card_P3 h3A, ha] at h2
  have h2' : (D.q + 1).factorization 3 ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have hne : (D.q + 1).factorization 3 ≠ a := by
    intro heq
    apply D.tThree_not_mem_P3
    have hle : D.primaryPart 3 ≤ D.S3 h3A := D.P3_le_S3 h3A
    have hcard : Nat.card (D.S3 h3A) ≤ Nat.card (D.primaryPart 3) := by
      rw [ha, D.card_P3 h3A, heq]
    have := Subgroup.eq_of_le_of_card_ge hle hcard
    rw [this]
    exact D.tThree_mem_S3 h3A
  omega

noncomputable def sylowS3 (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) : Sylow 3 G :=
  Sylow.ofCard (D.S3 h3A) (D.card_S3 h3A h3)

theorem coe_sylowS3 (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) :
    ((D.sylowS3 h3A h3 : Sylow 3 G) : Subgroup G) = D.S3 h3A := Sylow.coe_ofCard _ _

theorem card_N_factorization_three (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) :
    (Nat.card D.N).factorization 3 = (D.q + 1).factorization 3 := by
  rw [D.factorization_card_N Nat.prime_three (by norm_num) h3,
    Nat.factorization_eq_zero_of_not_dvd h3A, zero_add]

theorem exists_conj_mem_P3 (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) {w : G}
    (hw : ∃ k : ℕ, orderOf w = 3 ^ k) {i : G} (hi : orderOf i = 2) (hiw : i * w = w * i) :
    ∃ g : G, g * w * g⁻¹ ∈ D.primaryPart 3 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (D.involution_conj i hi)
  have hcw : c * w * c⁻¹ ∈ D.N := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * w * c⁻¹ * (c * i * c⁻¹) = c * (w * i) * c⁻¹ := by group
      _ = c * (i * w) * c⁻¹ := by rw [hiw]
      _ = c * i * c⁻¹ * (c * w * c⁻¹) := by group
  have hP₀N : D.primaryPart 3 ≤ D.N := fun u hu => D.C_le_N (D.primaryPart_le_C 3 hu)
  have hcard : Nat.card ((D.primaryPart 3).subgroupOf D.N) =
      3 ^ (Nat.card D.N).factorization 3 := by
    rw [card_subgroupOf_of_le' hP₀N, D.card_P3 h3A, D.card_N_factorization_three h3A h3]
  let Q₀ : Sylow 3 D.N := Sylow.ofCard _ hcard
  obtain ⟨k, hk⟩ := hw
  have hp : IsPGroup 3 (Subgroup.zpowers (⟨c * w * c⁻¹, hcw⟩ : D.N)) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_conj_eq, hk]
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq D.N R Q₀
  have hmem : (⟨c * w * c⁻¹, hcw⟩ : D.N) ∈ (R : Subgroup D.N) := hR (Subgroup.mem_zpowers _)
  have h2 : n * ⟨c * w * c⁻¹, hcw⟩ * n⁻¹ ∈ (Q₀ : Subgroup D.N) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact ⟨_, hmem, rfl⟩
  rw [Sylow.coe_ofCard] at h2
  refine ⟨n * c, ?_⟩
  have h3' : ((n * ⟨c * w * c⁻¹, hcw⟩ * n⁻¹ : D.N) : G) ∈ D.primaryPart 3 := h2
  convert h3' using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  group

theorem two_le_factorization_three (h9 : 9 ∣ D.q + 1) : 2 ≤ (D.q + 1).factorization 3 :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mp
    (by norm_num; exact h9)

theorem exists_generator_P3 (h3A : ¬ 3 ∣ Nat.card D.A) :
    ∃ u₀ : G, D.primaryPart 3 = Subgroup.zpowers u₀ ∧
      orderOf u₀ = 3 ^ (D.q + 1).factorization 3 := by
  obtain ⟨u₀, hu₀⟩ := D.exists_eq_zpowers_of_le_W (D.P3_le_W h3A)
  exact ⟨u₀, hu₀, by rw [← Nat.card_zpowers, ← hu₀, D.card_P3 h3A]⟩

theorem tThree_cube_mem_P3 : D.tThree ^ 3 ∈ D.primaryPart 3 := by
  refine ⟨D.tThree_cube_mem_C, ?_⟩
  obtain ⟨b, hb⟩ := D.tThree_order
  have hdvd : orderOf (D.tThree ^ 3) ∣ 3 ^ b := hb ▸ orderOf_pow_dvd 3
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact ⟨k, hk⟩

theorem tThree_zpow_mem_P3 {i : ℤ} (hi : (3 : ℤ) ∣ i) : D.tThree ^ i ∈ D.primaryPart 3 := by
  obtain ⟨k, rfl⟩ := hi
  rw [zpow_mul, zpow_ofNat]
  exact (D.primaryPart 3).zpow_mem D.tThree_cube_mem_P3 k

theorem three_element_of_mem_S3 (h3A : ¬ 3 ∣ Nat.card D.A) {s : G} (hs : s ∈ D.S3 h3A) :
    ∃ k : ℕ, orderOf s = 3 ^ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (D.isPGroup_S3 h3A)) ⟨s, hs⟩
  exact ⟨k, (Subgroup.orderOf_coe (⟨s, hs⟩ : D.S3 h3A)).trans hk⟩

theorem mem_P3_of_mem_C (h3A : ¬ 3 ∣ Nat.card D.A) {s : G} (hs : s ∈ D.S3 h3A)
    (hsC : s ∈ D.C) : s ∈ D.primaryPart 3 :=
  ⟨hsC, D.three_element_of_mem_S3 h3A hs⟩

theorem cube_mem_P3 (h3A : ¬ 3 ∣ Nat.card D.A) {s : G} (hs : s ∈ D.S3 h3A) :
    s ^ 3 ∈ D.primaryPart 3 := by
  obtain ⟨u, hu, i, rfl⟩ := hs
  have hc : Commute u (D.tThree ^ i) := (D.tThree_zpow_comm_P3 h3A hu i).symm
  rw [hc.mul_pow]
  refine (D.primaryPart 3).mul_mem ((D.primaryPart 3).pow_mem hu 3) ?_
  rw [← zpow_natCast, ← zpow_mul]
  exact D.tThree_zpow_mem_P3 ⟨i, by push_cast; ring⟩

theorem trichotomy (h3A : ¬ 3 ∣ Nat.card D.A) {s s' : G} (hs : s ∈ D.S3 h3A)
    (hs' : s' ∈ D.S3 h3A) (hsP : s ∉ D.primaryPart 3) :
    s' ∈ D.primaryPart 3 ∨ s' * s⁻¹ ∈ D.primaryPart 3 ∨ s' * s ∈ D.primaryPart 3 := by
  obtain ⟨u, hu, i, rfl⟩ := hs
  obtain ⟨u', hu', i', rfl⟩ := hs'
  have hi : ¬ (3 : ℤ) ∣ i := fun h =>
    hsP ((D.primaryPart 3).mul_mem hu (D.tThree_zpow_mem_P3 h))
  have key : (3 : ℤ) ∣ i' ∨ (3 : ℤ) ∣ i' - i ∨ (3 : ℤ) ∣ i' + i := by
    have h1 : i % 3 = 1 ∨ i % 3 = 2 := by omega
    have h2 : i' % 3 = 0 ∨ i' % 3 = 1 ∨ i' % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> omega
  have hui := (D.primaryPart 3).inv_mem hu
  rcases key with h | h | h
  · exact Or.inl ((D.primaryPart 3).mul_mem hu' (D.tThree_zpow_mem_P3 h))
  · refine Or.inr (Or.inl ?_)
    have e : u' * D.tThree ^ i' * (u * D.tThree ^ i)⁻¹ =
        u' * u⁻¹ * D.tThree ^ (i' - i) := by
      calc u' * D.tThree ^ i' * (u * D.tThree ^ i)⁻¹ = u' * (D.tThree ^ (i' - i) * u⁻¹) := by
            rw [zpow_sub]; group
        _ = u' * u⁻¹ * D.tThree ^ (i' - i) := by
            rw [D.tThree_zpow_comm_P3 h3A hui, mul_assoc]
    rw [e]
    exact (D.primaryPart 3).mul_mem ((D.primaryPart 3).mul_mem hu' hui) (D.tThree_zpow_mem_P3 h)
  · refine Or.inr (Or.inr ?_)
    have e : u' * D.tThree ^ i' * (u * D.tThree ^ i) = u' * u * D.tThree ^ (i' + i) := by
      calc u' * D.tThree ^ i' * (u * D.tThree ^ i) = u' * (D.tThree ^ i' * u) * D.tThree ^ i := by
            group
        _ = u' * u * D.tThree ^ (i' + i) := by
            rw [D.tThree_zpow_comm_P3 h3A hu, zpow_add]; group
    rw [e]
    exact (D.primaryPart 3).mul_mem ((D.primaryPart 3).mul_mem hu' hu) (D.tThree_zpow_mem_P3 h)

theorem pow_ordCompl_mem_S3 (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) {n : G}
    (hn : n ∈ Subgroup.normalizer (D.S3 h3A : Set G)) :
    n ^ (orderOf n / 3 ^ (orderOf n).factorization 3) ∈ D.S3 h3A := by
  set m := orderOf n / 3 ^ (orderOf n).factorization 3 with hm
  have hord : orderOf (n ^ m) = 3 ^ (orderOf n).factorization 3 :=
    orderOf_pow_orderOf_div (orderOf_pos n).ne' (Nat.ordProj_dvd (orderOf n) 3)
  have hP : IsPGroup 3 (Subgroup.zpowers (n ^ m)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hord])
  have key := hP.inf_normalizer_sylow (D.sylowS3 h3A h3)
  have hmem : n ^ m ∈ Subgroup.zpowers (n ^ m) ⊓
      Subgroup.normalizer (D.sylowS3 h3A h3 : Set G) :=
    ⟨Subgroup.mem_zpowers _, pow_mem hn m⟩
  rw [key] at hmem
  exact hmem.2

theorem not_three_dvd_ordCompl (n : G) : ¬ 3 ∣ orderOf n / 3 ^ (orderOf n).factorization 3 :=
  Nat.not_dvd_ordCompl Nat.prime_three (orderOf_pos n).ne'

theorem C_le_normalizer_T : D.C ≤ Subgroup.normalizer (D.T : Set G) := by
  intro c hc
  obtain ⟨h1, h2⟩ := D.mem_C_iff_conj.mp hc
  exact D.mem_normalizer_T_of (by rw [h1]; exact D.x_mem_T) (by rw [h2]; exact D.z_mem_T)

@[expose] def CT : Subgroup G where
  carrier := {g | ∃ c ∈ D.C, ∃ i : ℤ, g = c * D.t ^ i}
  one_mem' := ⟨1, D.C.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨c₁, hc₁, i, rfl⟩ ⟨c₂, hc₂, j, rfl⟩
    refine ⟨c₁ * (D.t ^ i * c₂ * (D.t ^ i)⁻¹),
      D.C.mul_mem hc₁ (D.conj_mem_C (zpow_mem D.t_mem_normalizer_T i) hc₂), i + j, ?_⟩
    rw [zpow_add]
    group
  inv_mem' := by
    rintro _ ⟨c, hc, i, rfl⟩
    refine ⟨D.t ^ (-i) * c⁻¹ * (D.t ^ (-i))⁻¹,
      D.conj_mem_C (zpow_mem D.t_mem_normalizer_T (-i)) (D.C.inv_mem hc), -i, ?_⟩
    group

theorem C_le_CT : D.C ≤ D.CT := fun c hc => ⟨c, hc, 0, by simp⟩

theorem CT_le_normalizer_T : D.CT ≤ Subgroup.normalizer (D.T : Set G) := by
  rintro _ ⟨c, hc, i, rfl⟩
  exact mul_mem (D.C_le_normalizer_T hc) (zpow_mem D.t_mem_normalizer_T i)

theorem S3_le_CT (h3A : ¬ 3 ∣ Nat.card D.A) : D.S3 h3A ≤ D.CT := by
  rintro _ ⟨u, hu, i, rfl⟩
  refine ⟨u, D.primaryPart_le_C 3 hu, D.threeExponent * i, ?_⟩
  rw [zpow_mul, zpow_natCast]
  rfl

theorem y_conj_CT {g : G} (hg : g ∈ D.CT) : D.y * g * D.y⁻¹ ∈ D.CT := by
  obtain ⟨c, hc, i, rfl⟩ := hg
  have e : D.y * (c * D.t ^ i) * D.y⁻¹ = (D.y * c * D.y⁻¹) * (D.y * D.t * D.y⁻¹) ^ i := by
    rw [conj_zpow]
    group
  rw [e]
  refine mul_mem (D.C_le_CT (D.conj_mem_C D.y_mem_normalizer_T hc)) (zpow_mem ?_ i)
  have e2 : D.y * D.t * D.y⁻¹ = (D.y * D.t * D.y⁻¹ * D.t) * D.t ^ (-1 : ℤ) := by group
  rw [e2]
  exact ⟨_, D.y_t_y_inv_t_mem_C, -1, rfl⟩

theorem t_comm_P3 (h3A : ¬ 3 ∣ Nat.card D.A) {u : G} (hu : u ∈ D.primaryPart 3) :
    D.t * u = u * D.t :=
  comm_of_conj_eq (D.t_conj_eq_of_le_W (D.P3_le_W h3A) (fun _ hv => D.t_conj_primaryPart hv) hu)

theorem CT_conj_P3 (h3A : ¬ 3 ∣ Nat.card D.A) {g u : G} (hg : g ∈ D.CT)
    (hu : u ∈ D.primaryPart 3) : g * u * g⁻¹ = u := by
  obtain ⟨c, hc, i, rfl⟩ := hg
  have hti : D.t ^ i * u = u * D.t ^ i :=
    (Commute.zpow_left (D.t_comm_P3 h3A hu : Commute D.t u) i).eq
  rw [conj_mul_eq, conj_eq_of_comm hti, D.C_conj hc (D.primaryPart_le_C 3 hu)]

theorem CT_conj_tThree {g : G} (hg : g ∈ D.CT) : g * D.tThree * g⁻¹ * D.tThree⁻¹ ∈ D.C := by
  obtain ⟨c, hc, i, rfl⟩ := hg
  have hti : D.t ^ i * D.tThree = D.tThree * D.t ^ i :=
    (((Commute.refl D.t).zpow_left i).pow_right D.threeExponent).eq
  rw [conj_mul_eq, conj_eq_of_comm hti]
  have e : c * D.tThree * c⁻¹ * D.tThree⁻¹ = c * (D.tThree * c⁻¹ * D.tThree⁻¹) := by group
  rw [e]
  exact D.C.mul_mem hc (D.conj_mem_C D.tThree_mem_normalizer_T (D.C.inv_mem hc))

theorem conj_pow_mul_pow_mem_C {g a : G} (ha : a ∈ Subgroup.normalizer (D.T : Set G))
    (h : g * a * g⁻¹ * a ∈ D.C) (n : ℕ) : g * a ^ n * g⁻¹ * a ^ n ∈ D.C := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : g * a ^ (n + 1) * g⁻¹ * a ^ (n + 1) =
        (g * a ^ n * g⁻¹ * a ^ n) * ((a ^ n)⁻¹ * (g * a * g⁻¹ * a) * ((a ^ n)⁻¹)⁻¹) := by
      group
    rw [e]
    exact D.C.mul_mem ih (D.conj_mem_C (inv_mem (pow_mem ha n)) h)

theorem y_tThree_mem_C : D.y * D.tThree * D.y⁻¹ * D.tThree ∈ D.C :=
  D.conj_pow_mul_pow_mem_C D.t_mem_normalizer_T D.y_t_y_inv_t_mem_C _

theorem exists_inverting (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) :
    ∃ σ ∈ Subgroup.normalizer (D.S3 h3A : Set G),
      (∀ u ∈ D.primaryPart 3, σ * u * σ⁻¹ = u⁻¹) ∧ σ * D.tThree * σ⁻¹ * D.tThree ∈ D.C := by
  have hle := D.S3_le_CT h3A
  let P : Sylow 3 D.CT := (D.sylowS3 h3A h3).subtype (by rw [D.coe_sylowS3]; exact hle)
  have hP : (P : Subgroup D.CT) = (D.S3 h3A).subgroupOf D.CT := by
    rw [Sylow.coe_subtype, D.coe_sylowS3]
  obtain ⟨c, hc, hcy⟩ :=
    exists_mul_mem_normalizer_of_sylow hle P hP (fun k hk => D.y_conj_CT hk)
  refine ⟨c * D.y, hcy, ?_, ?_⟩
  · intro u hu
    rw [conj_mul_eq, D.y_W u (D.P3_le_W h3A hu)]
    exact D.CT_conj_P3 h3A hc ((D.primaryPart 3).inv_mem hu)
  · rw [conj_mul_eq]
    have hd : D.y * D.tThree * D.y⁻¹ * D.tThree ∈ D.C := D.y_tThree_mem_C
    have e : c * (D.y * D.tThree * D.y⁻¹) * c⁻¹ * D.tThree =
        (c * (D.y * D.tThree * D.y⁻¹ * D.tThree) * c⁻¹) *
          (D.tThree⁻¹ * (c * D.tThree * c⁻¹ * D.tThree⁻¹)⁻¹ * D.tThree⁻¹⁻¹) := by
      group
    rw [e]
    exact D.C.mul_mem (D.conj_mem_C (D.CT_le_normalizer_T hc) hd)
      (D.conj_mem_C (inv_mem D.tThree_mem_normalizer_T) (D.C.inv_mem (D.CT_conj_tThree hc)))

theorem conj_mem_S3 (h3A : ¬ 3 ∣ Nat.card D.A) {n : G}
    (hn : n ∈ Subgroup.normalizer (D.S3 h3A : Set G)) {s : G} (hs : s ∈ D.S3 h3A) :
    n * s * n⁻¹ ∈ D.S3 h3A :=
  (Subgroup.mem_normalizer_iff.mp hn s).mp hs

theorem pow_ordCompl_conj (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) {n : G}
    (hn : n ∈ Subgroup.normalizer (D.S3 h3A : Set G)) {s : G} (hs : s ∈ D.S3 h3A) :
    n ^ (orderOf n / 3 ^ (orderOf n).factorization 3) * s *
      (n ^ (orderOf n / 3 ^ (orderOf n).factorization 3))⁻¹ = s :=
  conj_eq_of_comm (D.S3_comm h3A _ (D.pow_ordCompl_mem_S3 h3A h3 hn) s hs)

theorem inverts_S3 (h3A : ¬ 3 ∣ Nat.card D.A) (h3 : 3 ∣ D.q + 1) {σ : G}
    (hσS : σ ∈ Subgroup.normalizer (D.S3 h3A : Set G))
    (hσP : ∀ u ∈ D.primaryPart 3, σ * u * σ⁻¹ = u⁻¹)
    (hστ : σ * D.tThree * σ⁻¹ * D.tThree ∈ D.C) :
    ∀ s ∈ D.S3 h3A, σ * s * σ⁻¹ = s⁻¹ := by
  have hτS := D.tThree_mem_S3 h3A
  have hp : σ * D.tThree * σ⁻¹ * D.tThree ∈ D.primaryPart 3 :=
    D.mem_P3_of_mem_C h3A ((D.S3 h3A).mul_mem (D.conj_mem_S3 h3A hσS hτS) hτS) hστ
  have hστ' : σ * D.tThree * σ⁻¹ = (σ * D.tThree * σ⁻¹ * D.tThree) * D.tThree⁻¹ := by group
  intro s hs
  have ha : σ * s * σ⁻¹ * s ∈ D.primaryPart 3 := by
    obtain ⟨u, hu, j, rfl⟩ := hs
    set p := σ * D.tThree * σ⁻¹ * D.tThree with hpdef
    have hpτ0 : Commute p D.tThree := (D.tThree_comm_P3 h3A hp).symm
    have hpτ : Commute p D.tThree⁻¹ := hpτ0.inv_right
    have e1 : σ * (u * D.tThree ^ j) * σ⁻¹ = (σ * u * σ⁻¹) * (σ * D.tThree * σ⁻¹) ^ j := by
      rw [conj_zpow]
      group
    have e : σ * (u * D.tThree ^ j) * σ⁻¹ * (u * D.tThree ^ j) = u⁻¹ * p ^ j * u := by
      calc σ * (u * D.tThree ^ j) * σ⁻¹ * (u * D.tThree ^ j) =
            u⁻¹ * (p * D.tThree⁻¹) ^ j * (u * D.tThree ^ j) := by rw [e1, hσP u hu, hστ']
        _ = u⁻¹ * p ^ j * (D.tThree ^ (-j) * u) * D.tThree ^ j := by
            rw [hpτ.mul_zpow, inv_zpow']
            group
        _ = u⁻¹ * p ^ j * u := by
            rw [D.tThree_zpow_comm_P3 h3A hu (-j)]
            group
    rw [e]
    exact (D.primaryPart 3).mul_mem
      ((D.primaryPart 3).mul_mem ((D.primaryPart 3).inv_mem hu) ((D.primaryPart 3).zpow_mem hp j))
      hu
  have haS : σ * s * σ⁻¹ * s ∈ D.S3 h3A := D.P3_le_S3 h3A ha
  obtain ⟨a, hadef⟩ : ∃ a, a = σ * s * σ⁻¹ * s := ⟨_, rfl⟩
  rw [← hadef] at ha haS
  have hσa : σ * a * σ⁻¹ = a⁻¹ := hσP a ha
  have hσs : σ * s * σ⁻¹ = a * s⁻¹ := by rw [hadef]; group
  have hcomm : Commute a s := D.S3_comm h3A a haS s hs
  have h1 : σ ^ 2 * s * (σ ^ 2)⁻¹ = s * (a⁻¹ * a⁻¹) := by
    have e : σ * (a * s⁻¹) * σ⁻¹ = (σ * a * σ⁻¹) * (σ * s * σ⁻¹)⁻¹ := by group
    rw [pow_two, conj_mul_eq, hσs, e, hσa, hσs, mul_inv_rev, inv_inv, ← mul_assoc,
      hcomm.inv_left.eq, mul_assoc]
  have hP2 : a⁻¹ * a⁻¹ ∈ D.primaryPart 3 :=
    (D.primaryPart 3).mul_mem ((D.primaryPart 3).inv_mem ha) ((D.primaryPart 3).inv_mem ha)
  have h2 : σ ^ 2 * (a⁻¹ * a⁻¹) * (σ ^ 2)⁻¹ = a⁻¹ * a⁻¹ := by
    rw [pow_two, conj_mul_eq, hσP _ hP2, hσP _ ((D.primaryPart 3).inv_mem hP2), inv_inv]
  have hm : (σ ^ 2) ^ (orderOf σ / 3 ^ (orderOf σ).factorization 3) * s *
      ((σ ^ 2) ^ (orderOf σ / 3 ^ (orderOf σ).factorization 3))⁻¹ = s := by
    rw [← pow_mul, mul_comm 2, pow_mul]
    exact pow_conj_eq_of_conj_eq (D.pow_ordCompl_conj h3A h3 hσS hs) 2
  have hd := pow_eq_one_of_conj_eq_mul h1 h2 hm
  obtain ⟨k, hk⟩ := hP2.2
  have hd1 := eq_one_of_pow_eq_one_of_not_dvd hk hd (not_three_dvd_ordCompl σ)
  have ha2 : a ^ 2 = 1 := by
    have h3' : (a⁻¹ * a⁻¹)⁻¹ = 1 := by rw [hd1, inv_one]
    rw [mul_inv_rev, inv_inv] at h3'
    rw [pow_two]
    exact h3'
  obtain ⟨k', hk'⟩ := ha.2
  have ha1 := eq_one_of_pow_eq_one_of_not_dvd hk' ha2 (by norm_num)
  rw [hadef] at ha1
  exact eq_inv_of_mul_eq_one_left ha1

theorem not_comm_involution (h3A : ¬ 3 ∣ Nat.card D.A) (h9 : 9 ∣ D.q + 1) {u₀ : G}
    (hu₀ : D.primaryPart 3 = Subgroup.zpowers u₀)
    (hu₀o : orderOf u₀ = 3 ^ (D.q + 1).factorization 3)
    {w : G} (hw : w ∈ D.S3 h3A) (hw3 : w ^ 3 = 1) (hwP : w ∉ D.primaryPart 3)
    {i : G} (hi : orderOf i = 2) (hiw : i * w = w * i) : False := by
  have h3 : 3 ∣ D.q + 1 := (by norm_num : (3 : ℕ) ∣ 9).trans h9
  have hh := D.two_le_factorization_three h9
  obtain ⟨g, hg⟩ := D.exists_conj_mem_P3 h3A h3 (D.three_element_of_mem_S3 h3A hw) hi hiw
  have hSc : ∀ v ∈ D.S3 h3A,
      v ∈ Subgroup.centralizer ((D.sylowS3 h3A h3 : Sylow 3 G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact D.S3_comm h3A s hs v hv
  obtain ⟨n, hn, hnw⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer (D.sylowS3 h3A h3) w
    g⁻¹ (hSc w hw) (by rw [inv_inv]; exact hSc _ (D.P3_le_S3 h3A hg))
  rw [inv_inv] at hnw
  have hn' : n ∈ Subgroup.normalizer (D.S3 h3A : Set G) := hn
  have hk3 : (g * w * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hw3, mul_one, mul_inv_cancel]
  obtain ⟨j, hj⟩ := mem_zpowers_of_pow_eq_one (by omega) hu₀o (hu₀ ▸ hg) hk3
  have hvS : n * u₀ ^ j * n⁻¹ ∈ D.S3 h3A :=
    D.conj_mem_S3 h3A hn' (D.P3_le_S3 h3A (hu₀ ▸ Subgroup.zpow_mem_zpowers u₀ j))
  have hwpow : w = ((n * u₀ ^ j * n⁻¹) ^ 3) ^ (3 ^ ((D.q + 1).factorization 3 - 2)) := by
    have e1 : w = n * (g * w * g⁻¹) * n⁻¹ := by rw [hnw]; group
    rw [e1, hj, ← zpow_pow_comm', ← conj_pow, ← pow_mul, ← pow_succ']
    congr 2
    omega
  exact hwP (hwpow ▸ (D.primaryPart 3).pow_mem (D.cube_mem_P3 h3A hvS) _)

theorem normalizer_S3_act_Z (h3A : ¬ 3 ∣ Nat.card D.A) (h9 : 9 ∣ D.q + 1) {u₀ : G}
    (hu₀ : D.primaryPart 3 = Subgroup.zpowers u₀)
    (hu₀o : orderOf u₀ = 3 ^ (D.q + 1).factorization 3) {n : G}
    (hn : n ∈ Subgroup.normalizer (D.S3 h3A : Set G)) :
    (∀ z ∈ Subgroup.zpowers (u₀ ^ 3), n * z * n⁻¹ = z) ∨
      (∀ z ∈ Subgroup.zpowers (u₀ ^ 3), n * z * n⁻¹ = z⁻¹) := by
  have hh := D.two_le_factorization_three h9
  have hu₀P : u₀ ∈ D.primaryPart 3 := hu₀ ▸ Subgroup.mem_zpowers u₀
  have hZP : Subgroup.zpowers (u₀ ^ 3) ≤ D.primaryPart 3 := by
    rw [Subgroup.zpowers_le]
    exact (D.primaryPart 3).pow_mem hu₀P 3
  have hu₀3W : u₀ ^ 3 ∈ D.W := D.P3_le_W h3A ((D.primaryPart 3).pow_mem hu₀P 3)
  have hu₀3 : u₀ ^ 3 ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hu₀o] at h2
    have h4 := Nat.le_of_dvd (by norm_num) h2
    have h5 : 3 ^ 2 ≤ 3 ^ (D.q + 1).factorization 3 := Nat.pow_le_pow_right (by norm_num) hh
    omega
  apply D.normalizer_conj_of_le_W hu₀3W hu₀3
  · intro u hu
    rw [conj_eq_of_comm (D.t_comm_P3 h3A (hZP hu))]
    exact hu
  · apply mem_normalizer_of_conj_mem_of_finite
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hvS : n * u₀ ^ j * n⁻¹ ∈ D.S3 h3A :=
      D.conj_mem_S3 h3A hn (D.P3_le_S3 h3A ((D.primaryPart 3).zpow_mem hu₀P j))
    have e : n * (u₀ ^ 3) ^ j * n⁻¹ = (n * u₀ ^ j * n⁻¹) ^ 3 := by
      rw [conj_pow, zpow_pow_comm']
    rw [e]
    have hmemP : (n * u₀ ^ j * n⁻¹) ^ 3 ∈ Subgroup.zpowers u₀ := hu₀ ▸ D.cube_mem_P3 h3A hvS
    refine mem_zpowers_pow_of_pow_eq_one (by norm_num) (by omega) hu₀o hmemP ?_
    rw [← pow_mul, conj_pow, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ _),
      zpow_pow_comm', ← hu₀o, pow_orderOf_eq_one, one_zpow, mul_one, mul_inv_cancel]

theorem conj_eq_of_conj_Z (h3A : ¬ 3 ∣ Nat.card D.A) (h9 : 9 ∣ D.q + 1) {u₀ : G}
    (hu₀ : D.primaryPart 3 = Subgroup.zpowers u₀)
    (hu₀o : orderOf u₀ = 3 ^ (D.q + 1).factorization 3) {σ : G}
    (hσinv : ∀ s ∈ D.S3 h3A, σ * s * σ⁻¹ = s⁻¹) {n : G}
    (hn : n ∈ Subgroup.normalizer (D.S3 h3A : Set G))
    (hnZ : ∀ z ∈ Subgroup.zpowers (u₀ ^ 3), n * z * n⁻¹ = z) :
    ∀ s ∈ D.S3 h3A, n * s * n⁻¹ = s := by
  have h3 : 3 ∣ D.q + 1 := (by norm_num : (3 : ℕ) ∣ 9).trans h9
  have hh := D.two_le_factorization_three h9
  have hu₀P : u₀ ∈ D.primaryPart 3 := hu₀ ▸ Subgroup.mem_zpowers u₀
  have hS := D.S3_comm h3A
  have hm3 := not_three_dvd_ordCompl n
  have key : ∀ s ∈ D.S3 h3A, ∀ d ∈ D.S3 h3A, n * s * n⁻¹ = s * d → n * d * n⁻¹ = d →
      d = 1 := by
    intro s hs d hd h1 h2
    obtain ⟨k, hk⟩ := D.three_element_of_mem_S3 h3A hd
    exact eq_one_of_pow_eq_one_of_not_dvd hk
      (pow_eq_one_of_conj_eq_mul h1 h2 (D.pow_ordCompl_conj h3A h3 hn hs)) hm3
  have hZ : ∀ x ∈ D.primaryPart 3, x ^ 3 = 1 → x ∈ Subgroup.zpowers (u₀ ^ 3) := by
    intro x hx hx3
    refine mem_zpowers_pow_of_pow_eq_one (by norm_num) (by omega) hu₀o (hu₀ ▸ hx) ?_
    obtain ⟨c, hc⟩ : 3 ∣ 3 ^ ((D.q + 1).factorization 3 - 1) := dvd_pow_self 3 (by omega)
    rw [hc, pow_mul, hx3, one_pow]
  have hZS : ∀ z ∈ Subgroup.zpowers (u₀ ^ 3), z ∈ D.S3 h3A := by
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact D.P3_le_S3 h3A ((D.primaryPart 3).zpow_mem ((D.primaryPart 3).pow_mem hu₀P 3) j)
  have ha : ∀ w ∈ D.S3 h3A, w ^ 3 = 1 → n * w * n⁻¹ = w := by
    intro w hw hw3
    by_cases hwP : w ∈ D.primaryPart 3
    · exact hnZ w (hZ w hwP hw3)
    have hw'S : n * w * n⁻¹ ∈ D.S3 h3A := D.conj_mem_S3 h3A hn hw
    have hw'3 : (n * w * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hw3, mul_one, mul_inv_cancel]
    have hcomm : Commute w (n * w * n⁻¹) := hS w hw _ hw'S
    rcases D.trichotomy h3A hw hw'S hwP with h1 | h1 | h1
    · exfalso
      have hfix := hnZ _ (hZ _ h1 hw'3)
      exact hwP ((eq_of_conj_eq hfix.symm) ▸ h1)
    · have hd : w⁻¹ * (n * w * n⁻¹) ∈ D.primaryPart 3 := by
        rw [hcomm.inv_left.eq]
        exact h1
      have hd3 : (w⁻¹ * (n * w * n⁻¹)) ^ 3 = 1 := by
        rw [hcomm.inv_left.mul_pow, inv_pow, hw3, hw'3, inv_one, one_mul]
      have hd1 := key w hw _ ((D.S3 h3A).mul_mem ((D.S3 h3A).inv_mem hw) hw'S)
        (by group) (hnZ _ (hZ _ hd hd3))
      exact (inv_mul_eq_one.mp hd1).symm
    · exfalso
      have hk3 : (n * w * n⁻¹ * w) ^ 3 = 1 := by
        rw [hcomm.symm.mul_pow, hw'3, hw3, one_mul]
      have hkfix := hnZ _ (hZ _ h1 hk3)
      have hkS : n * w * n⁻¹ * w ∈ D.S3 h3A := (D.S3 h3A).mul_mem hw'S hw
      set k := n * w * n⁻¹ * w with hkdef
      have hwk : Commute w k := hS w hw k hkS
      have hw₁S : w * k ∈ D.S3 h3A := (D.S3 h3A).mul_mem hw hkS
      have hw₁P : w * k ∉ D.primaryPart 3 := fun h => hwP (by
        have e : w = w * k * k⁻¹ := by group
        rw [e]
        exact (D.primaryPart 3).mul_mem h ((D.primaryPart 3).inv_mem h1))
      have hw₁3 : (w * k) ^ 3 = 1 := by rw [hwk.mul_pow, hw3, hk3, one_mul]
      have hgw : σ * n * w * (σ * n)⁻¹ = w * k⁻¹ := by
        rw [conj_mul_eq, hσinv _ hw'S, hkdef]
        group
      have hgk : σ * n * k * (σ * n)⁻¹ = k⁻¹ := by
        rw [conj_mul_eq, hkfix, hσinv _ hkS]
      have hkk : k⁻¹ * k⁻¹ = k := by
        have e3 : k * (k * k) = 1 := by rw [← pow_three]; exact hk3
        calc k⁻¹ * k⁻¹ = k⁻¹ * k⁻¹ * (k * (k * k)) := by rw [e3, mul_one]
          _ = k := by group
      have hgw₁ : σ * n * (w * k) * (σ * n)⁻¹ = w * k := by
        have e : σ * n * (w * k) * (σ * n)⁻¹ =
            (σ * n * w * (σ * n)⁻¹) * (σ * n * k * (σ * n)⁻¹) := by group
        rw [e, hgw, hgk, mul_assoc, hkk]
      have hgz : σ * n * u₀ ^ 3 * (σ * n)⁻¹ = (u₀ ^ 3)⁻¹ := by
        rw [conj_mul_eq, hnZ _ (Subgroup.mem_zpowers _),
          hσinv _ (hZS _ (Subgroup.mem_zpowers _))]
      have hz2 : (u₀ ^ 3) ^ 2 ≠ 1 := by
        intro h2
        rw [← pow_mul] at h2
        have h4 := orderOf_dvd_of_pow_eq_one h2
        rw [hu₀o] at h4
        have h5 := Nat.le_of_dvd (by norm_num) h4
        have h6 : 3 ^ 2 ≤ 3 ^ (D.q + 1).factorization 3 := Nat.pow_le_pow_right (by norm_num) hh
        omega
      have heven := even_orderOf_of_conj_eq_inv hgz hz2
      have hinv := exists_pow_orderOf_eq_two heven
      exact D.not_comm_involution h3A h9 hu₀ hu₀o hw₁S hw₁3 hw₁P hinv
        (comm_of_conj_eq (pow_conj_eq_of_conj_eq hgw₁ _))
  have hcube : ∀ s ∈ D.S3 h3A, n * s ^ 3 * n⁻¹ = s ^ 3 → n * s * n⁻¹ = s := by
    intro s hs hs3
    have hns : n * s * n⁻¹ ∈ D.S3 h3A := D.conj_mem_S3 h3A hn hs
    have hcomm : Commute s (n * s * n⁻¹) := hS s hs _ hns
    have hdS : s⁻¹ * (n * s * n⁻¹) ∈ D.S3 h3A := (D.S3 h3A).mul_mem ((D.S3 h3A).inv_mem hs) hns
    have hd3 : (s⁻¹ * (n * s * n⁻¹)) ^ 3 = 1 := by
      rw [hcomm.inv_left.mul_pow, conj_pow, hs3, inv_pow, inv_mul_cancel]
    have hd1 := key s hs _ hdS (by group) (ha _ hdS hd3)
    exact (inv_mul_eq_one.mp hd1).symm
  have hb : ∀ s ∈ D.primaryPart 3, n * s * n⁻¹ = s := by
    intro s hs
    refine hcube s (D.P3_le_S3 h3A hs) (hnZ _ ?_)
    rw [hu₀] at hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, (zpow_pow_comm' u₀ j 3).symm⟩
  intro s hs
  exact hcube s hs (hb _ (D.cube_mem_P3 h3A hs))

theorem normalizer_S3_act (h3A : ¬ 3 ∣ Nat.card D.A) (h9 : 9 ∣ D.q + 1) {u₀ : G}
    (hu₀ : D.primaryPart 3 = Subgroup.zpowers u₀)
    (hu₀o : orderOf u₀ = 3 ^ (D.q + 1).factorization 3) {σ : G}
    (hσS : σ ∈ Subgroup.normalizer (D.S3 h3A : Set G))
    (hσinv : ∀ s ∈ D.S3 h3A, σ * s * σ⁻¹ = s⁻¹) {n : G}
    (hn : n ∈ Subgroup.normalizer (D.S3 h3A : Set G)) :
    (∀ s ∈ D.S3 h3A, n * s * n⁻¹ = s) ∨ (∀ s ∈ D.S3 h3A, n * s * n⁻¹ = s⁻¹) := by
  have hu₀P : u₀ ∈ D.primaryPart 3 := hu₀ ▸ Subgroup.mem_zpowers u₀
  rcases D.normalizer_S3_act_Z h3A h9 hu₀ hu₀o hn with h | h
  · exact Or.inl (D.conj_eq_of_conj_Z h3A h9 hu₀ hu₀o hσinv hn h)
  · right
    have hfix : ∀ z ∈ Subgroup.zpowers (u₀ ^ 3), σ * n * z * (σ * n)⁻¹ = z := by
      intro z hz
      have hzS : z ∈ D.S3 h3A := by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact D.P3_le_S3 h3A ((D.primaryPart 3).zpow_mem ((D.primaryPart 3).pow_mem hu₀P 3) j)
      rw [conj_mul_eq, h z hz, hσinv _ ((D.S3 h3A).inv_mem hzS), inv_inv]
    have hk := D.conj_eq_of_conj_Z h3A h9 hu₀ hu₀o hσinv (mul_mem hσS hn) hfix
    intro s hs
    have h1 := hk s hs
    rw [conj_mul_eq, hσinv _ (D.conj_mem_S3 h3A hn hs)] at h1
    exact inv_eq_iff_eq_inv.mp h1

theorem three_dvd_card_A (h9 : 9 ∣ D.q + 1) : 3 ∣ Nat.card D.A := by
  by_contra h3A
  have h3 : 3 ∣ D.q + 1 := (by norm_num : (3 : ℕ) ∣ 9).trans h9
  have hh := D.two_le_factorization_three h9
  obtain ⟨u₀, hu₀, hu₀o⟩ := D.exists_generator_P3 h3A
  obtain ⟨σ, hσS, hσP, hστ⟩ := D.exists_inverting h3A h3
  have hσinv := D.inverts_S3 h3A h3 hσS hσP hστ
  have hu₀P : u₀ ∈ D.primaryPart 3 := hu₀ ▸ Subgroup.mem_zpowers u₀
  have hu₀inv : u₀⁻¹ ≠ u₀ := by
    intro h1
    have h2 : u₀ ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [← h1]
      exact inv_mul_cancel u₀
    have h4 := orderOf_dvd_of_pow_eq_one h2
    rw [hu₀o] at h4
    have h5 := Nat.le_of_dvd (by norm_num) h4
    have h6 : 3 ^ 2 ≤ 3 ^ (D.q + 1).factorization 3 := Nat.pow_le_pow_right (by norm_num) hh
    omega
  have hN := relIndex_eq_two_of_act' (D.P3_le_S3 h3A hu₀P) hu₀inv
    (fun n hn => D.normalizer_S3_act h3A h9 hu₀ hu₀o hσS hσinv hn) hσS hσinv
  set h := (D.q + 1).factorization 3 with hhdef
  have hcard : Nat.card (D.sylowS3 h3A h3) = 27 * 3 ^ (h - 2) := by
    rw [Sylow.card_eq_multiplicity, D.factorization_three_card_G h3A h3, ← hhdef,
      show h + 1 = (h - 2) + 3 by omega, pow_add]
    ring
  obtain ⟨c, hc⟩ : 3 ^ h ∣ D.q + 1 := Nat.ordProj_dvd (D.q + 1) 3
  have hqZ : (D.q : ℤ) = 9 * 3 ^ (h - 2) * c - 1 := by
    have hc' : (D.q : ℤ) + 1 = (3 : ℤ) ^ h * c := by exact_mod_cast hc
    rw [show h = (h - 2) + 2 by omega, pow_add] at hc'
    linear_combination hc'
  have hcardZ : ((Nat.card (D.sylowS3 h3A h3) : ℕ) : ℤ) = 27 * 3 ^ (h - 2) := by
    rw [hcard]
    push_cast
    ring
  refine D.false_of_inverted_sylow (r := 3) (by norm_num) (D.sylowS3 h3A h3) (D.S3_comm h3A) hN
    σ hσS hσinv ?_ ?_ ?_ ?_ ?_
  · rw [hcard]
    have := Nat.one_le_pow (h - 2) 3 (by norm_num)
    omega
  · rw [hcardZ, hqZ]
    exact ⟨27 * (3 ^ (h - 2)) ^ 2 * c ^ 3 - 9 * 3 ^ (h - 2) * c ^ 2 + c, by ring⟩
  · rw [hcardZ, hqZ]
    exact ⟨3 * 3 ^ (h - 2) * c ^ 2 - c, by ring⟩
  · rw [hcardZ, hqZ]
    exact ⟨c, by ring⟩
  · intro h5
    rw [hcard] at h5
    have := Nat.one_le_pow (h - 2) 3 (by norm_num)
    omega

end DValueData

end CFSG.Semidihedral.UnitaryDValue




