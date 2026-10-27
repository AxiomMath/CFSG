module

public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.QuasithinUnique CFSG.GorensteinWalter
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

theorem exists_commuting_involutions_dihedral {m : ℕ} (hm : 1 ≤ m) :
    ∃ x y : DihedralGroup (2 ^ m), x * x = 1 ∧ y * y = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧
      x * y = y * x := by
  have hne : NeZero (2 ^ m) := ⟨by positivity⟩
  have hpow : 2 * 2 ^ (m - 1) = 2 ^ m := by
    rw [← pow_succ']
    congr 1
    omega
  set a : ZMod (2 ^ m) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with ha
  have ha2 : a + a = 0 := by
    have h : a + a = ((2 ^ m : ℕ) : ZMod (2 ^ m)) := by
      rw [ha, ← Nat.cast_add, ← two_mul, hpow]
    rw [h, ZMod.natCast_self]
  have ha0 : a ≠ 0 := by
    rw [ha, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have h1 := Nat.le_of_dvd (by positivity) h
    have h2 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hneg : -a = a := by
    have := congrArg (fun z => z - a) ha2
    simp only [add_sub_cancel_right, zero_sub] at this
    exact this.symm
  refine ⟨DihedralGroup.sr 0, DihedralGroup.r a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [DihedralGroup.r_mul_r, ha2]
    rfl
  · intro h
    rw [DihedralGroup.one_def] at h
    cases h
  · intro h
    rw [DihedralGroup.one_def] at h
    exact ha0 (DihedralGroup.r.inj h)
  · intro h
    cases h
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    simp [hneg]

theorem exists_sq_ne_one_dihedral {m : ℕ} (hm : 2 ≤ m) :
    ∃ x : DihedralGroup (2 ^ m), x ^ 2 ≠ 1 := by
  have hne : NeZero (2 ^ m) := ⟨by positivity⟩
  refine ⟨DihedralGroup.r 1, ?_⟩
  rw [pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def]
  intro h
  have h2 : (1 + 1 : ZMod (2 ^ m)) = 0 := DihedralGroup.r.inj h
  have h3 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
    rw [← h2]
    norm_num
  rw [ZMod.natCast_eq_zero_iff] at h3
  have h4 := Nat.le_of_dvd (by norm_num) h3
  have h5 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_of_isSylowTwoOf_top {P : Subgroup G} (h : IsSylowTwoOf P ⊤) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card P = 2 ^ (Nat.card G).factorization 2 := by
    rw [h.card_eq]
    simp [twoPart]
  exact ⟨Sylow.ofCard P hc, Sylow.coe_ofCard _ _⟩

end Sylow

section PSL2

variable {K : Type} [Field K] [Finite K]

theorem exists_commuting_involutions_of_sylow (hK : IsOddPrimePower (Nat.card K))
    (S : Sylow 2 PSL(2, K)) :
    ∃ t s : PSL(2, K), t ∈ (S : Subgroup PSL(2, K)) ∧ s ∈ (S : Subgroup PSL(2, K)) ∧
      t * t = 1 ∧ s * s = 1 ∧ t ≠ 1 ∧ s ≠ 1 ∧ t ≠ s ∧ t * s = s * t := by
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hK S
  obtain ⟨x, y, hx, hy, hx1, hy1, hxy, hcomm⟩ := exists_commuting_involutions_dihedral hm
  have hmul : ∀ u v : ↥(S : Subgroup PSL(2, K)),
      ((u * v : ↥(S : Subgroup PSL(2, K))) : PSL(2, K)) = (u : PSL(2, K)) * v := fun u v => rfl
  have hone : ((1 : ↥(S : Subgroup PSL(2, K))) : PSL(2, K)) = 1 := rfl
  refine ⟨(e.symm x : PSL(2, K)), (e.symm y : PSL(2, K)), (e.symm x).2, (e.symm y).2, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← hmul, ← map_mul, hx, map_one, hone]
  · rw [← hmul, ← map_mul, hy, map_one, hone]
  · intro h
    apply hx1
    have : e.symm x = 1 := Subtype.ext h
    simpa using this
  · intro h
    apply hy1
    have : e.symm y = 1 := Subtype.ext h
    simpa using this
  · intro h
    apply hxy
    have : e.symm x = e.symm y := Subtype.ext h
    exact e.symm.injective this
  · rw [← hmul, ← hmul, ← map_mul, ← map_mul, hcomm]

theorem exists_sq_ne_one_of_sylow (hK : IsOddPrimePower (Nat.card K))
    (h8 : 8 ∣ Nat.card PSL(2, K)) (S : Sylow 2 PSL(2, K)) :
    ∃ y ∈ (S : Subgroup PSL(2, K)), y ^ 2 ≠ 1 := by
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hK S
  have hcard : Nat.card (S : Subgroup PSL(2, K)) = 2 ^ (Nat.card PSL(2, K)).factorization 2 :=
    S.card_eq_multiplicity
  have hcard2 : Nat.card (S : Subgroup PSL(2, K)) = 2 * 2 ^ m :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hv : 3 ≤ (Nat.card PSL(2, K)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
      (by simpa using h8)
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by omega
    subst hm1
    have h8' : 2 ^ 3 ≤ 2 ^ (Nat.card PSL(2, K)).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) hv
    omega
  obtain ⟨x, hx⟩ := exists_sq_ne_one_dihedral hm2
  refine ⟨(e.symm x : PSL(2, K)), (e.symm x).2, ?_⟩
  intro h
  apply hx
  have h1 : e.symm x ^ 2 = 1 := Subtype.ext (by simpa using h)
  have h2 := congrArg e h1
  simpa using h2

end PSL2

theorem eight_dvd_psl2_order {p : ℕ} (h8 : p % 8 = 1 ∨ p % 8 = 7) :
    8 ∣ p * (p ^ 2 - 1) / 2 := by
  rcases h8 with h | h
  · obtain ⟨a, rfl⟩ : ∃ a, p = 8 * a + 1 := ⟨p / 8, by omega⟩
    have h1 : (8 * a + 1) ^ 2 - 1 = 64 * a ^ 2 + 16 * a := by
      have : (8 * a + 1) ^ 2 = 64 * a ^ 2 + 16 * a + 1 := by ring
      omega
    have h2 : (8 * a + 1) * (64 * a ^ 2 + 16 * a) =
        2 * (8 * ((8 * a + 1) * (4 * a ^ 2 + a))) := by ring
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    exact Dvd.intro _ rfl
  · obtain ⟨a, rfl⟩ : ∃ a, p = 8 * a + 7 := ⟨p / 8, by omega⟩
    have h1 : (8 * a + 7) ^ 2 - 1 = 64 * a ^ 2 + 112 * a + 48 := by
      have : (8 * a + 7) ^ 2 = 64 * a ^ 2 + 112 * a + 49 := by ring
      omega
    have h2 : (8 * a + 7) * (64 * a ^ 2 + 112 * a + 48) =
        2 * (8 * ((8 * a + 7) * (4 * a ^ 2 + 7 * a + 3))) := by ring
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    exact Dvd.intro _ rfl

section Facts

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

omit [Field K] [Finite K] in
theorem isOddPrimePower_of_card_prime (hp7 : 7 ≤ p) (hK : Nat.card K = p) :
    IsOddPrimePower (Nat.card K) :=
  ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩

theorem eight_dvd_card_psl2 (hp7 : 7 ≤ p) (hK : Nat.card K = p)
    (h8 : p % 8 = 1 ∨ p % 8 = 7) : 8 ∣ Nat.card PSL(2, K) := by
  rw [psl2_card_formula K (isOddPrimePower_of_card_prime hp7 hK), hK]
  exact eight_dvd_psl2_order h8

theorem not_comm_of_simple_of_four_dvd' {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h4 : 4 ∣ Nat.card X) : ∃ x y : X, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hcon }
  have hprime := IsSimpleGroup.prime_card (α := X)
  rcases hprime.eq_one_or_self_of_dvd 4 h4 with h | h
  · omega
  · rw [← h] at hprime
    exact absurd hprime (by norm_num)

omit [Finite K] [Fact p.Prime] in
theorem psl2_simple (hp7 : 7 ≤ p) (hK : Nat.card K = p) : IsSimpleGroup PSL(2, K) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)

theorem psl2_nonabelian (hp7 : 7 ≤ p) (hK : Nat.card K = p) (h8 : p % 8 = 1 ∨ p % 8 = 7) :
    ∃ a b : PSL(2, K), a * b ≠ b * a := by
  have := psl2_simple hp7 hK
  exact not_comm_of_simple_of_four_dvd'
    (dvd_trans (by norm_num : 4 ∣ 8) (eight_dvd_card_psl2 hp7 hK h8))

theorem psl2_single_class (hp7 : 7 ≤ p) (hK : Nat.card K = p) :
    ∀ i j : PSL(2, K), orderOf i = 2 → orderOf j = 2 → ∃ k : PSL(2, K), k * i * k⁻¹ = j := by
  intro i j hi hj
  exact isConj_iff.mp (CFSG.Walter.psl2_isConj_of_orderOf_eq_two K (p := p) (f := 1)
    (by rw [hK, pow_one]) ((Fact.out : p.Prime).odd_of_ne_two (by omega)) one_pos hi hj)

theorem psl2_cent_two (hp7 : 7 ≤ p) (hK : Nat.card K = p)
    (hpow : (p % 8 = 1 ∧ ∃ m : ℕ, p = 2 ^ m + 1) ∨ (p % 8 = 7 ∧ ∃ m : ℕ, p + 1 = 2 ^ m)) :
    ∀ i : PSL(2, K), orderOf i = 2 → IsPGroup 2 (Subgroup.centralizer ({i} : Set PSL(2, K))) := by
  intro i hi
  obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution K (p := p) (f := 1)
    (by rw [hK, pow_one]) ((Fact.out : p.Prime).odd_of_ne_two (by omega)) one_pos hi
  simp only [pow_one] at h1 h3
  rcases hpow with ⟨h8, m, hm⟩ | ⟨h8, m, hm⟩
  · obtain ⟨hc, -⟩ := h1 (by omega)
    exact IsPGroup.of_card (n := m) (by rw [hc, hm]; simp)
  · obtain ⟨hc, -⟩ := h3 (by omega)
    exact IsPGroup.of_card (n := m) (by rw [hc, hm])

omit [Finite K] in
theorem psl2_inner_three (hK : Nat.card K = p) :
    ∀ α : MulAut PSL(2, K), (∃ n : ℕ, orderOf α = 3 ^ n) →
      ∃ k : PSL(2, K), ∀ x : PSL(2, K), α x = k * x * k⁻¹ := by
  rintro α ⟨n, hn⟩
  have hout := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
    (p := p) (f := 1) Fact.out K (by rw [hK, pow_one])).1
  have hcard2 : Nat.card (Outer PSL(2, K)) ∣ 2 := by
    refine hout.trans ?_
    rw [one_mul]
    exact Nat.gcd_dvd_left _ _
  have hord1 : orderOf (QuotientGroup.mk α : Outer PSL(2, K)) ∣ 3 ^ n := by
    rw [← hn]
    exact orderOf_map_dvd (QuotientGroup.mk' (inner PSL(2, K))) α
  have hord2 : orderOf (QuotientGroup.mk α : Outer PSL(2, K)) ∣ 2 :=
    (orderOf_dvd_natCard _).trans hcard2
  have hcop : Nat.Coprime (3 ^ n) 2 := Nat.Coprime.pow_left n (by norm_num)
  have h1 : orderOf (QuotientGroup.mk α : Outer PSL(2, K)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  have h2 : (QuotientGroup.mk α : Outer PSL(2, K)) = 1 := orderOf_eq_one_iff.mp h1
  rw [QuotientGroup.eq_one_iff] at h2
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, fun x => by rw [← hk]; rfl⟩

end Facts

end CFSG.QuasithinUnique.Unc25K1
