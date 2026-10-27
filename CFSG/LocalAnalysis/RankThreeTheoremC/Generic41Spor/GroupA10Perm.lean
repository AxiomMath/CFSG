module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

@[expose] def A10LineOrbits (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow 5 K, ∃ A₁ A₂ : Subgroup K, Nat.card A₁ = 5 ∧ Nat.card A₂ = 5 ∧ A₁ ≠ A₂ ∧
    A₁ ≤ (S : Subgroup K) ∧ A₂ ≤ (S : Subgroup K) ∧
    (∀ n ∈ normalizer ((S : Subgroup K) : Set K),
      A₁.map (MulAut.conj n).toMonoidHom = A₁ ∨ A₁.map (MulAut.conj n).toMonoidHom = A₂) ∧
    (∀ L L' : Subgroup K, L ≤ (S : Subgroup K) → L' ≤ (S : Subgroup K) → Nat.card L = 5 →
      Nat.card L' = 5 → L ≠ A₁ → L ≠ A₂ → L' ≠ A₁ → L' ≠ A₂ →
      ∃ n ∈ normalizer ((S : Subgroup K) : Set K), L.map (MulAut.conj n).toMonoidHom = L')

namespace A10Perm

open Equiv Equiv.Perm

abbrev A10 : Type := ↥(alternatingGroup (Fin 10))

def c₁ : Perm (Fin 10) := c[0, 1, 2, 3, 4]
def c₂ : Perm (Fin 10) := c[5, 6, 7, 8, 9]
def g₁ : Perm (Fin 10) := c[1, 2, 4, 3]
def g₂ : Perm (Fin 10) := c[6, 7, 9, 8]
def τ : Perm (Fin 10) := swap 0 5 * swap 1 6 * swap 2 7 * swap 3 8 * swap 4 9

def mkA (π : Perm (Fin 10)) (h : sign π = 1 := by decide) : A10 := ⟨π, mem_alternatingGroup.2 h⟩

def a₁ : A10 := mkA c₁
def a₂ : A10 := mkA c₂
def ν₀ : A10 := mkA (g₁ * g₂)
def ν₁ : A10 := mkA (g₁ ^ 2)
def ν₂ : A10 := mkA (τ * g₁)
def ν₃ : A10 := mkA (g₁ ^ 2 * (τ * g₁))

theorem a₁_pow : a₁ ^ 5 = 1 := by decide
theorem a₂_pow : a₂ ^ 5 = 1 := by decide
theorem a₁₂_comm : a₁ * a₂ = a₂ * a₁ := by decide
theorem a₁_ne : a₁ ≠ 1 := by decide
theorem a₂_ne : a₂ ≠ 1 := by decide

theorem ν₀_a₁ : ν₀ * a₁ * ν₀⁻¹ = a₁ ^ 2 * a₂ ^ 0 := by decide
theorem ν₀_a₂ : ν₀ * a₂ * ν₀⁻¹ = a₁ ^ 0 * a₂ ^ 2 := by decide
theorem ν₁_a₁ : ν₁ * a₁ * ν₁⁻¹ = a₁ ^ 4 * a₂ ^ 0 := by decide
theorem ν₁_a₂ : ν₁ * a₂ * ν₁⁻¹ = a₁ ^ 0 * a₂ ^ 1 := by decide
theorem ν₂_a₁ : ν₂ * a₁ * ν₂⁻¹ = a₁ ^ 0 * a₂ ^ 2 := by decide
theorem ν₂_a₂ : ν₂ * a₂ * ν₂⁻¹ = a₁ ^ 1 * a₂ ^ 0 := by decide
theorem ν₃_a₁ : ν₃ * a₁ * ν₃⁻¹ = a₁ ^ 0 * a₂ ^ 2 := by decide +kernel
theorem ν₃_a₂ : ν₃ * a₂ * ν₃⁻¹ = a₁ ^ 4 * a₂ ^ 0 := by decide +kernel

theorem a₁₂_commute : Commute a₁ a₂ := a₁₂_comm

theorem mul_aux (i j k l : ℕ) :
    (a₁ ^ i * a₂ ^ j) * (a₁ ^ k * a₂ ^ l) = a₁ ^ (i + k) * a₂ ^ (j + l) := by
  have h : a₂ ^ j * a₁ ^ k = a₁ ^ k * a₂ ^ j := (a₁₂_commute.symm.pow_pow j k).eq
  calc (a₁ ^ i * a₂ ^ j) * (a₁ ^ k * a₂ ^ l) = a₁ ^ i * (a₂ ^ j * a₁ ^ k) * a₂ ^ l := by
        simp only [mul_assoc]
    _ = a₁ ^ (i + k) * a₂ ^ (j + l) := by
        rw [h]; simp only [pow_add, mul_assoc]

def S₀ : Subgroup A10 where
  carrier := {x | ∃ i j : ℕ, x = a₁ ^ i * a₂ ^ j}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact ⟨i + k, j + l, mul_aux i j k l⟩
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨4 * i, 4 * j, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [mul_aux]
    have h1 : i + 4 * i = 5 * i := by omega
    have h2 : j + 4 * j = 5 * j := by omega
    rw [h1, h2, pow_mul, pow_mul, a₁_pow, a₂_pow]
    simp

theorem mem_S₀ {x : A10} : x ∈ S₀ ↔ ∃ i j : ℕ, x = a₁ ^ i * a₂ ^ j := Iff.rfl
theorem a₁_mem : a₁ ∈ S₀ := ⟨1, 0, by simp⟩
theorem a₂_mem : a₂ ∈ S₀ := ⟨0, 1, by simp⟩

theorem key_inj : ∀ i j k l : Fin 5, a₁ ^ (i : ℕ) * a₂ ^ (j : ℕ) = a₁ ^ (k : ℕ) * a₂ ^ (l : ℕ) →
    i = k ∧ j = l := by decide +kernel

theorem exp_inj {i j k l : ℕ} (h : a₁ ^ i * a₂ ^ j = a₁ ^ k * a₂ ^ l) :
    i % 5 = k % 5 ∧ j % 5 = l % 5 := by
  rw [pow_eq_pow_mod i a₁_pow, pow_eq_pow_mod j a₂_pow, pow_eq_pow_mod k a₁_pow,
    pow_eq_pow_mod l a₂_pow] at h
  have := key_inj ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩ ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩
    ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩ ⟨l % 5, Nat.mod_lt _ (by norm_num)⟩ h
  simpa [Fin.ext_iff] using this

def toS (p : Fin 5 × Fin 5) : S₀ := ⟨a₁ ^ (p.1 : ℕ) * a₂ ^ (p.2 : ℕ), p.1, p.2, rfl⟩

theorem card_S₀ : Nat.card S₀ = 25 := by
  have hb : Function.Bijective toS := by
    constructor
    · intro p q h
      have := exp_inj (congrArg Subtype.val h)
      rw [Nat.mod_eq_of_lt p.1.2, Nat.mod_eq_of_lt q.1.2, Nat.mod_eq_of_lt p.2.2,
        Nat.mod_eq_of_lt q.2.2] at this
      exact Prod.ext (Fin.ext this.1) (Fin.ext this.2)
    · rintro ⟨x, i, j, rfl⟩
      refine ⟨(⟨i % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩),
        Subtype.ext ?_⟩
      simp only [toS]
      rw [← pow_eq_pow_mod i a₁_pow, ← pow_eq_pow_mod j a₂_pow]
  have := Nat.card_eq_of_bijective toS hb
  rw [← this]
  simp

theorem card_A10 : Nat.card A10 = 1814400 := by
  have h := nat_card_alternatingGroup (α := Fin 10)
  rw [Nat.card_eq_fintype_card (α := Fin 10), Fintype.card_fin] at h
  rw [h]
  decide

theorem factorization_A10 : (Nat.card A10).factorization 5 = 2 := by
  rw [card_A10, show (1814400 : ℕ) = 5 ^ 2 * 72576 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

open scoped Pointwise in
theorem exists_iso_sylow {K : Type} [Group K] [Finite K] (e : K ≃* A10) (S : Sylow 5 K) :
    ∃ ψ : K ≃* A10, ∀ x : K, x ∈ (S : Subgroup K) ↔ ψ x ∈ S₀ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let S' : Sylow 5 A10 := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q : Sylow 5 A10 := Sylow.ofCard S₀ (by rw [card_S₀, factorization_A10]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A10 Q S'
  refine ⟨e.trans (MulAut.conj g⁻¹), fun x => ?_⟩
  have h1 : x ∈ (S : Subgroup K) ↔ e x ∈ (S' : Subgroup A10) := by
    show x ∈ (S : Subgroup K) ↔ e x ∈ (S : Subgroup K).map e.toMonoidHom
    rw [Subgroup.mem_map_equiv]; simp
  have h2 : (S' : Subgroup A10) = MulAut.conj g • (Q : Subgroup A10) := by
    rw [← hg]; rfl
  rw [h1, h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [Q]

theorem zpowers_pow_eq {G : Type} [Group G] {x : G} (hx : orderOf x = 5) {j : ℕ} (hj : ¬ 5 ∣ j) :
    zpowers (x ^ j) = zpowers x := by
  have hx5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  apply le_antisymm
  · exact zpowers_le.mpr (pow_mem (mem_zpowers x) j)
  · have hcop : Nat.Coprime j 5 :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hj)
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 5)
    refine zpowers_le.mpr ?_
    have : (x ^ j) ^ m = x := by
      rw [← pow_mul, pow_eq_pow_mod _ hx5, hm, pow_one]
    have h := pow_mem (mem_zpowers (x ^ j)) m
    rwa [this] at h

theorem eq_zpowers_of_card_five {G : Type} [Group G] {L : Subgroup G} (hL : Nat.card L = 5)
    {x : G} (hxL : x ∈ L) (hx1 : x ≠ 1) : L = zpowers x := by
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have hord : orderOf x = 5 := by
    have h1 : orderOf x ∣ 5 := hL ▸ Subgroup.orderOf_dvd_natCard L hxL
    rcases (Nat.dvd_prime Nat.prime_five).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  symm
  apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxL)
  rw [Nat.card_zpowers, hord, hL]

theorem card_zpowers_of_pow_eq {G : Type} [Group G] {x : G} (hx : x ^ 5 = 1) (hx1 : x ≠ 1) :
    Nat.card (zpowers x) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hx hx1]

theorem orderOf_eq_five {G : Type} [Group G] {x : G} (hx : x ^ 5 = 1) (hx1 : x ≠ 1) :
    orderOf x = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime hx hx1

theorem conj_gen (n : A10) (i j : ℕ) :
    n * (a₁ ^ i * a₂ ^ j) * n⁻¹ = (n * a₁ * n⁻¹) ^ i * (n * a₂ * n⁻¹) ^ j := by
  have h : (MulAut.conj n) (a₁ ^ i * a₂ ^ j) =
      (MulAut.conj n a₁) ^ i * (MulAut.conj n a₂) ^ j := by
    rw [map_mul, map_pow, map_pow]
  simpa only [MulAut.conj_apply] using h

theorem mem_normalizer_S₀ {n : A10} (h1 : n * a₁ * n⁻¹ ∈ S₀) (h2 : n * a₂ * n⁻¹ ∈ S₀) :
    n ∈ normalizer (S₀ : Set A10) := by
  apply Subgroup.mem_normalizer_fintype
  rintro x ⟨i, j, rfl⟩
  rw [conj_gen]
  exact S₀.mul_mem (S₀.pow_mem h1 i) (S₀.pow_mem h2 j)

theorem ν₀_mem : ν₀ ∈ normalizer (S₀ : Set A10) :=
  mem_normalizer_S₀ (by rw [ν₀_a₁]; exact ⟨2, 0, rfl⟩) (by rw [ν₀_a₂]; exact ⟨0, 2, rfl⟩)

theorem ν₀_conj {x : A10} (hx : x ∈ S₀) : ν₀ * x * ν₀⁻¹ = x * x := by
  obtain ⟨i, j, rfl⟩ := hx
  rw [mul_aux, conj_gen, ν₀_a₁, ν₀_a₂]
  simp only [pow_zero, mul_one, one_mul, ← pow_mul, two_mul]

theorem concrete_noFixed {x : A10} (hx : x ∈ S₀) (hx1 : x ≠ 1) :
    ∃ n ∈ normalizer (S₀ : Set A10), n * x ≠ x * n := by
  refine ⟨ν₀, ν₀_mem, fun h => hx1 ?_⟩
  have h1 : ν₀ * x * ν₀⁻¹ = x := by rw [h, mul_assoc, mul_inv_cancel, mul_one]
  rw [ν₀_conj hx] at h1
  exact mul_eq_left.1 h1

theorem noFixed_of_equiv {K : Type} [Group K] (ψ : K ≃* A10) (S : Subgroup K)
    (hS : ∀ x : K, x ∈ S ↔ ψ x ∈ S₀) {a : K} (ha : a ∈ S) (ha1 : a ≠ 1) :
    ∃ n ∈ normalizer (S : Set K), n * a ≠ a * n := by
  obtain ⟨n₀, hn₀, hne⟩ := concrete_noFixed ((hS a).1 ha)
    (fun h => ha1 (ψ.injective (by rw [h, map_one])))
  refine ⟨ψ.symm n₀, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hS, hS]
    have := (Subgroup.mem_normalizer_iff.1 hn₀) (ψ y)
    simpa [map_mul, map_inv] using this
  · intro h
    apply hne
    have := congrArg ψ h
    simpa [map_mul] using this

theorem fixed_check : ∀ u v : Fin 5, ∀ p : Fin 10,
    ((a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ) : A10) : Perm (Fin 10)) p = p → u = 0 ∨ v = 0 := by
  decide +kernel

@[expose] def OrbitCheck (u v u' v' : Fin 5) : Prop :=
  u ≠ 0 → v ≠ 0 → u' ≠ 0 → v' ≠ 0 →
    ∃ n ∈ ([1, ν₁, ν₂, ν₃] : List A10), ∃ k ∈ ([1, 2, 3, 4] : List ℕ),
      n * (a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ)) * n⁻¹ = (a₁ ^ (u' : ℕ) * a₂ ^ (v' : ℕ)) ^ k

instance (u v u' v' : Fin 5) : Decidable (OrbitCheck u v u' v') := by
  unfold OrbitCheck; infer_instance

theorem orbit_check : ∀ u v u' v' : Fin 5, OrbitCheck u v u' v' := by decide +kernel

theorem mem_zpowers_nat {G : Type} [Group G] [Finite G] {x y : G} :
    y ∈ zpowers x ↔ ∃ n : ℕ, x ^ n = y := by
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]

def line₁ : Subgroup A10 := zpowers a₁
def line₂ : Subgroup A10 := zpowers a₂

theorem card_line₁ : Nat.card line₁ = 5 := card_zpowers_of_pow_eq a₁_pow a₁_ne
theorem card_line₂ : Nat.card line₂ = 5 := card_zpowers_of_pow_eq a₂_pow a₂_ne
theorem line₁_le : line₁ ≤ S₀ := zpowers_le.mpr a₁_mem
theorem line₂_le : line₂ ≤ S₀ := zpowers_le.mpr a₂_mem

theorem line₁_ne_line₂ : line₁ ≠ line₂ := by
  intro h
  have h1 : a₁ ∈ line₂ := h ▸ mem_zpowers a₁
  obtain ⟨n, hn⟩ := mem_zpowers_nat.1 h1
  have := exp_inj (i := 0) (j := n) (k := 1) (l := 0) (by simpa using hn)
  simp at this

theorem zpowers_a₁_pow {i : ℕ} (h : a₁ ^ i ≠ 1) : zpowers (a₁ ^ i) = line₁ := by
  refine zpowers_pow_eq (orderOf_eq_five a₁_pow a₁_ne) (fun hd => h ?_)
  obtain ⟨c, rfl⟩ := hd
  rw [pow_mul, a₁_pow, one_pow]

theorem zpowers_a₂_pow {j : ℕ} (h : a₂ ^ j ≠ 1) : zpowers (a₂ ^ j) = line₂ := by
  refine zpowers_pow_eq (orderOf_eq_five a₂_pow a₂_ne) (fun hd => h ?_)
  obtain ⟨c, rfl⟩ := hd
  rw [pow_mul, a₂_pow, one_pow]

theorem line_of_fixed {x : A10} (hx : x ∈ S₀) (hx1 : x ≠ 1) (p : Fin 10)
    (hp : (x : Perm (Fin 10)) p = p) : zpowers x = line₁ ∨ zpowers x = line₂ := by
  obtain ⟨i, j, rfl⟩ := hx
  have hi := pow_eq_pow_mod i a₁_pow
  have hj := pow_eq_pow_mod j a₂_pow
  have key := fixed_check ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩
    ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ p (by rw [hi, hj] at hp; exact hp)
  rcases key with h | h
  · have h0 : i % 5 = 0 := by simpa [Fin.ext_iff] using h
    have h1 : a₁ ^ i = 1 := by rw [hi, h0, pow_zero]
    rw [h1, one_mul] at hx1 ⊢
    exact Or.inr (zpowers_a₂_pow hx1)
  · have h0 : j % 5 = 0 := by simpa [Fin.ext_iff] using h
    have h1 : a₂ ^ j = 1 := by rw [hj, h0, pow_zero]
    rw [h1, mul_one] at hx1 ⊢
    exact Or.inl (zpowers_a₁_pow hx1)

theorem orbit_pair {n : A10} (hn : n ∈ normalizer (S₀ : Set A10)) :
    line₁.map (MulAut.conj n).toMonoidHom = line₁ ∨
      line₁.map (MulAut.conj n).toMonoidHom = line₂ := by
  have hx : n * a₁ * n⁻¹ ∈ S₀ := (Subgroup.mem_normalizer_iff.1 hn a₁).1 a₁_mem
  have hx1 : n * a₁ * n⁻¹ ≠ 1 := by
    intro h
    apply a₁_ne
    have := congrArg (fun y => n⁻¹ * y * n) h
    simpa [mul_assoc] using this
  have hfix : ((n * a₁ * n⁻¹ : A10) : Perm (Fin 10)) ((n : Perm (Fin 10)) 5) =
      (n : Perm (Fin 10)) 5 := by
    have h5 : (a₁ : Perm (Fin 10)) 5 = 5 := by decide
    simp [Perm.mul_apply, h5]
  have := line_of_fixed hx hx1 _ hfix
  have hmap : line₁.map (MulAut.conj n).toMonoidHom = zpowers (n * a₁ * n⁻¹) := by
    rw [line₁, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  rw [hmap]
  exact this

theorem line_data {L : Subgroup A10} (hLS : L ≤ S₀) (hL : Nat.card L = 5) (h1 : L ≠ line₁)
    (h2 : L ≠ line₂) :
    ∃ u v : Fin 5, u ≠ 0 ∧ v ≠ 0 ∧ L = zpowers (a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ)) := by
  haveI : Nontrivial L := Finite.one_lt_card_iff_nontrivial.1 (by rw [hL]; norm_num)
  obtain ⟨⟨x, hxL⟩, hx1⟩ := exists_ne (1 : L)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hLx : L = zpowers x := eq_zpowers_of_card_five hL hxL hx1'
  obtain ⟨i, j, hxij⟩ := hLS hxL
  have hi := pow_eq_pow_mod i a₁_pow
  have hj := pow_eq_pow_mod j a₂_pow
  have hxe : x = a₁ ^ (i % 5) * a₂ ^ (j % 5) := by rw [hxij, ← hi, ← hj]
  refine ⟨⟨i % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩, ?_, ?_, ?_⟩
  · intro h
    have h0 : i % 5 = 0 := by simpa [Fin.ext_iff] using h
    apply h2
    rw [hLx, hxe, h0, pow_zero, one_mul]
    rw [hxe, h0, pow_zero, one_mul] at hx1'
    exact zpowers_a₂_pow hx1'
  · intro h
    have h0 : j % 5 = 0 := by simpa [Fin.ext_iff] using h
    apply h1
    rw [hLx, hxe, h0, pow_zero, mul_one]
    rw [hxe, h0, pow_zero, mul_one] at hx1'
    exact zpowers_a₁_pow hx1'
  · rw [hLx, hxe]

theorem mem_normalizer_of_mem_list {n : A10} (hn : n ∈ ([1, ν₁, ν₂, ν₃] : List A10)) :
    n ∈ normalizer (S₀ : Set A10) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact mem_normalizer_S₀ (by rw [ν₁_a₁]; exact ⟨4, 0, rfl⟩)
      (by rw [ν₁_a₂]; exact ⟨0, 1, rfl⟩)
  · exact mem_normalizer_S₀ (by rw [ν₂_a₁]; exact ⟨0, 2, rfl⟩)
      (by rw [ν₂_a₂]; exact ⟨1, 0, rfl⟩)
  · exact mem_normalizer_S₀ (by rw [ν₃_a₁]; exact ⟨0, 2, rfl⟩)
      (by rw [ν₃_a₂]; exact ⟨4, 0, rfl⟩)

theorem orbit_diag {L L' : Subgroup A10} (hL : L ≤ S₀) (hL' : L' ≤ S₀) (c : Nat.card L = 5)
    (c' : Nat.card L' = 5) (h1 : L ≠ line₁) (h2 : L ≠ line₂) (h1' : L' ≠ line₁)
    (h2' : L' ≠ line₂) :
    ∃ n ∈ normalizer (S₀ : Set A10), L.map (MulAut.conj n).toMonoidHom = L' := by
  obtain ⟨u, v, hu, hv, rfl⟩ := line_data hL c h1 h2
  obtain ⟨u', v', hu', hv', rfl⟩ := line_data hL' c' h1' h2'
  obtain ⟨n, hn, k, hk, hnk⟩ := orbit_check u v u' v' hu hv hu' hv'
  refine ⟨n, mem_normalizer_of_mem_list hn, ?_⟩
  rw [MonoidHom.map_zpowers]
  have hord : orderOf (a₁ ^ (u' : ℕ) * a₂ ^ (v' : ℕ)) = 5 := by
    rw [← Nat.card_zpowers]; exact c'
  have hk5 : ¬ 5 ∣ k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have hnk' : (MulAut.conj n).toMonoidHom (a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ)) =
      (a₁ ^ (u' : ℕ) * a₂ ^ (v' : ℕ)) ^ k := by
    simpa [MulAut.conj_apply] using hnk
  rw [hnk']
  exact zpowers_pow_eq hord hk5

@[expose] def LineOrbitsAt (K : Type) [Group K] (S : Subgroup K) : Prop :=
  ∃ A₁ A₂ : Subgroup K, Nat.card A₁ = 5 ∧ Nat.card A₂ = 5 ∧ A₁ ≠ A₂ ∧ A₁ ≤ S ∧ A₂ ≤ S ∧
    (∀ n ∈ normalizer (S : Set K),
      A₁.map (MulAut.conj n).toMonoidHom = A₁ ∨ A₁.map (MulAut.conj n).toMonoidHom = A₂) ∧
    (∀ L L' : Subgroup K, L ≤ S → L' ≤ S → Nat.card L = 5 →
      Nat.card L' = 5 → L ≠ A₁ → L ≠ A₂ → L' ≠ A₁ → L' ≠ A₂ →
      ∃ n ∈ normalizer (S : Set K), L.map (MulAut.conj n).toMonoidHom = L')

theorem lineOrbitsAt_A10 : LineOrbitsAt A10 S₀ :=
  ⟨line₁, line₂, card_line₁, card_line₂, line₁_ne_line₂, line₁_le, line₂_le,
    fun _ hn => orbit_pair hn,
    fun _ _ hL hL' c c' h1 h2 h1' h2' => orbit_diag hL hL' c c' h1 h2 h1' h2'⟩

theorem lineOrbitsAt_of_equiv {K K' : Type} [Group K] [Group K'] (ψ : K ≃* K')
    (S : Subgroup K) (S' : Subgroup K') (hS : ∀ x : K, x ∈ S ↔ ψ x ∈ S')
    (h : LineOrbitsAt K' S') : LineOrbitsAt K S := by
  obtain ⟨B₁, B₂, c1, c2, hne, h1, h2, hO2, hO3⟩ := h
  have hmem : ∀ (B : Subgroup K') (x : K), x ∈ B.map ψ.symm.toMonoidHom ↔ ψ x ∈ B := by
    intro B x
    rw [Subgroup.mem_map_equiv]; simp
  have hcard : ∀ B : Subgroup K', Nat.card (B.map ψ.symm.toMonoidHom) = Nat.card B := fun B =>
    Subgroup.card_map_of_injective ψ.symm.injective
  have hnorm : ∀ n : K, n ∈ normalizer (S : Set K) ↔ ψ n ∈ normalizer (S' : Set K') := by
    intro n
    simp only [Subgroup.mem_normalizer_iff]
    constructor
    · intro hn y
      have := hn (ψ.symm y)
      rw [hS, hS] at this
      simpa [map_mul, map_inv] using this
    · intro hn x
      rw [hS, hS]
      have := hn (ψ x)
      simpa [map_mul, map_inv] using this
  have hconj : ∀ (n : K) (B : Subgroup K'),
      (B.map ψ.symm.toMonoidHom).map (MulAut.conj n).toMonoidHom =
        (B.map (MulAut.conj (ψ n)).toMonoidHom).map ψ.symm.toMonoidHom := by
    intro n B
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext y
    simp [map_mul, map_inv]
  have hLmap : ∀ M : Subgroup K, (M.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = M := by
    intro M
    rw [Subgroup.map_map]
    have : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id K := by ext y; simp
    rw [this, Subgroup.map_id]
  refine ⟨B₁.map ψ.symm.toMonoidHom, B₂.map ψ.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcard]; exact c1
  · rw [hcard]; exact c2
  · intro heq
    exact hne (Subgroup.map_injective ψ.symm.injective heq)
  · intro x hx
    rw [hmem] at hx
    exact (hS x).2 (h1 hx)
  · intro x hx
    rw [hmem] at hx
    exact (hS x).2 (h2 hx)
  · intro n hn
    rw [hconj]
    rcases hO2 (ψ n) ((hnorm n).1 hn) with h | h
    · left; rw [h]
    · right; rw [h]
  · intro L L' hL hL' cL cL' hL1 hL2 hL1' hL2'
    have hM : L.map ψ.toMonoidHom ≤ S' := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hS x).1 (hL hx)
    have hM' : L'.map ψ.toMonoidHom ≤ S' := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hS x).1 (hL' hx)
    have cM : Nat.card (L.map ψ.toMonoidHom) = 5 := by
      rw [Subgroup.card_map_of_injective ψ.injective]; exact cL
    have cM' : Nat.card (L'.map ψ.toMonoidHom) = 5 := by
      rw [Subgroup.card_map_of_injective ψ.injective]; exact cL'
    have ne : ∀ (M : Subgroup K) (B : Subgroup K'), M ≠ B.map ψ.symm.toMonoidHom →
        M.map ψ.toMonoidHom ≠ B := by
      intro M B hMB heq
      apply hMB
      rw [← heq, hLmap]
    obtain ⟨n', hn', hLn'⟩ := hO3 _ _ hM hM' cM cM' (ne L B₁ hL1) (ne L B₂ hL2)
      (ne L' B₁ hL1') (ne L' B₂ hL2')
    refine ⟨ψ.symm n', (hnorm _).2 (by simpa using hn'), ?_⟩
    have h3 := hconj (ψ.symm n') (L.map ψ.toMonoidHom)
    rw [hLmap, ψ.apply_symm_apply, hLn', hLmap] at h3
    exact h3

end A10Perm

theorem a10_noFixed : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → NormalizerNoFixed 5 K := by
  intro K _ _ hK S a ha ha1
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨ψ, hψ⟩ := A10Perm.exists_iso_sylow e S
  exact A10Perm.noFixed_of_equiv ψ (S : Subgroup K) hψ ha ha1

theorem a10_orbits : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10LineOrbits K := by
  intro K _ _ hK S
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨ψ, hψ⟩ := A10Perm.exists_iso_sylow e S
  exact A10Perm.lineOrbitsAt_of_equiv ψ (S : Subgroup K) A10Perm.S₀ hψ A10Perm.lineOrbitsAt_A10

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
