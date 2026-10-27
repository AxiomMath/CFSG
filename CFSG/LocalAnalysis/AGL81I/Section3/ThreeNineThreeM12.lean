module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeM11

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

abbrev m12PermA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

abbrev m12PermB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

abbrev m12PermG : Equiv.Perm (Fin 12) :=
  m12PermA * m12PermB⁻¹ * m12PermA * m12PermB⁻¹ * m12PermA * m12PermB⁻¹ * m12PermA * m12PermB *
    m12PermA * m12PermB⁻¹ * m12PermA * m12PermB * m12PermA * m12PermB⁻¹

abbrev m12PermT : Equiv.Perm (Fin 12) :=
  m12PermB⁻¹ * m12PermA * m12PermB * m12PermA * m12PermB⁻¹ * m12PermA * m12PermB * m12PermA *
    m12PermB * m12PermA * m12PermB⁻¹ * m12PermA * m12PermB * m12PermA * m12PermB⁻¹ * m12PermA *
    m12PermB * m12PermA * m12PermB * m12PermA * m12PermB

abbrev m12PermS : Equiv.Perm (Fin 12) :=
  m12PermB * m12PermA * m12PermB⁻¹ * m12PermA * m12PermB * m12PermA * m12PermB * m12PermA *
    m12PermB * m12PermA * m12PermB⁻¹ * m12PermA * m12PermB⁻¹ * m12PermA * m12PermB * m12PermA *
    m12PermB * m12PermA * m12PermB * m12PermA * m12PermB⁻¹ * m12PermA * m12PermB * m12PermA *
    m12PermB * m12PermA * m12PermB * m12PermA

theorem m12PermA_mem : m12PermA ∈ NativeSporadic.M12 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m12PermB_mem : m12PermB ∈ NativeSporadic.M12 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem m12PermG_mem : m12PermG ∈ NativeSporadic.M12 := by
  have ha := m12PermA_mem
  have hb := m12PermB_mem
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (ha) (inv_mem hb)) ha) (inv_mem hb)) ha) (inv_mem hb)) ha) hb) ha) (inv_mem hb)) ha) hb) ha) (inv_mem hb)

theorem m12PermT_mem : m12PermT ∈ NativeSporadic.M12 := by
  have ha := m12PermA_mem
  have hb := m12PermB_mem
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ((inv_mem hb)) ha) hb) ha) (inv_mem hb)) ha) hb) ha) hb) ha) (inv_mem hb)) ha) hb) ha) (inv_mem hb)) ha) hb) ha) hb) ha) hb

theorem m12PermS_mem : m12PermS ∈ NativeSporadic.M12 := by
  have ha := m12PermA_mem
  have hb := m12PermB_mem
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hb) ha) (inv_mem hb)) ha) hb) ha) hb) ha) hb) ha) (inv_mem hb)) ha) (inv_mem hb)) ha) hb) ha) hb) ha) hb) ha) (inv_mem hb)) ha) hb) ha) hb) ha) hb) ha

theorem orderOf_m12PermG : orderOf m12PermG = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · ext i
    revert i
    decide +kernel
  · intro h
    have := congrArg (fun f : Equiv.Perm (Fin 12) => f 1) h
    revert this
    decide +kernel

theorem orderOf_m12PermS : orderOf m12PermS = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · ext i
    revert i
    decide +kernel
  · intro h
    have := congrArg (fun f : Equiv.Perm (Fin 12) => f 0) h
    revert this
    decide +kernel

theorem m12PermT_pow_four : m12PermT ^ 4 = 1 := by
  ext i
  revert i
  decide +kernel

theorem m12PermT_sq_ne : m12PermT ^ 2 * m12PermG ≠ m12PermG * m12PermT ^ 2 := by
  intro h
  have := congrArg (fun f : Equiv.Perm (Fin 12) => f 1) h
  revert this
  decide +kernel

theorem m12PermT_conj_G : m12PermT * m12PermG * m12PermT⁻¹ = m12PermG ^ 3 := by
  ext i
  revert i
  decide +kernel

theorem m12PermT_inv_conj_G : m12PermT⁻¹ * m12PermG * m12PermT = m12PermG ^ 2 := by
  ext i
  revert i
  decide +kernel

theorem m12PermS_comm_G : m12PermS * m12PermG = m12PermG * m12PermS := by
  ext i
  revert i
  decide +kernel

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_M12
    (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .M12) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  obtain ⟨e⟩ := hK
  dsimp only [CFSG.Blueprint.NativeSporadic.Carrier] at e
  have hcard : Nat.card ↥K = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m12_card
  have hZ : Subgroup.center ↥K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center NativeSporadic.M12 := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      have := hz (e.symm y)
      rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, this]
    rw [CFSG.ComponentClassification.M12Cover.m12_center, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hz', map_one])
  have hOut : Nat.card (Outer ↥K) = 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.ComponentClassification.M12Cover.card_outer
  have hd3 : 3 ≤ d := by
    have := h.d_prime.two_le
    have := h.d_ne_two
    omega
  have hdOut : ¬ d ∣ Nat.card (Outer ↥K) := fun hdv => by
    rw [hOut] at hdv
    have := Nat.le_of_dvd (by norm_num) hdv
    omega
  have h3Out : ¬ 3 ∣ Nat.card (Outer ↥K) := by
    rw [hOut]
    norm_num
  obtain ⟨hY, hm3, hmd, h3Y, hdY, hdK⟩ := h.index_facts hZ h3Out hdOut
  obtain ⟨SD, hSD⟩ := h.exists_sylow_normalizer_le hZ hdOut
  rw [hcard] at h3Y hdY hdK
  have hY1 : (X₁.subgroupOf K).index ≠ 1 := fun h1 => hY (Subgroup.index_eq_one.mp h1)
  have h27 : (3 : ℕ) ^ (95040 : ℕ).factorization 3 = 27 :=
    (pow_eq_pow_factorization_of_eq (a := 3) (k := 3520) Nat.prime_three (by norm_num)
      (by norm_num)).symm
  rw [h27] at h3Y
  have hd511 : d = 5 ∨ d = 11 := by
    have hfac : (95040 : ℕ) = 2 ^ 6 * 3 ^ 3 * 5 * 11 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
  rcases hd511 with rfl | rfl
  ·
    have h5 : (5 : ℕ) ^ (95040 : ℕ).factorization 5 = 5 :=
      (pow_eq_pow_factorization_of_eq (a := 1) (k := 19008) (by norm_num) (by norm_num)
        (by norm_num)).symm
    rw [h5] at hdY
    have h135 : 135 ∣ Nat.card (X₁.subgroupOf K) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 5) h3Y hdY
    have hidx := index_dvd_div_of_dvd_card h135
    rw [hcard] at hidx
    have key : ∀ m ∈ Nat.divisors 704, m ≡ 1 [MOD 3] → m ≡ 1 [MOD 5] → m ≠ 1 → m = 16 := by
      decide +kernel
    have h16 := key _ (Nat.mem_divisors.mpr ⟨hidx, by norm_num⟩) hm3 hmd hY1
    have hYcard : Nat.card (X₁.subgroupOf K) = 5940 := by
      have hmul := (X₁.subgroupOf K).card_mul_index
      rw [hcard, h16] at hmul
      omega
    let gM : ↥NativeSporadic.M12 := ⟨m12PermG, m12PermG_mem⟩
    let tM : ↥NativeSporadic.M12 := ⟨m12PermT, m12PermT_mem⟩
    let sM : ↥NativeSporadic.M12 := ⟨m12PermS, m12PermS_mem⟩
    have hgM : orderOf gM = 5 := by rw [Subgroup.orderOf_mk, orderOf_m12PermG]
    have hsM : orderOf sM = 2 := by rw [Subgroup.orderOf_mk, orderOf_m12PermS]
    have hc1 : tM * gM * tM⁻¹ = gM ^ 3 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact m12PermT_conj_G)
    have hc2 : tM⁻¹ * gM * tM = gM ^ 2 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact m12PermT_inv_conj_G)
    have ht4 : tM ^ 4 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact m12PermT_pow_four)
    have ht2 : tM ^ 2 * gM ≠ gM * tM ^ 2 := fun heq => m12PermT_sq_ne (by
      have := congrArg Subtype.val heq
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow] at this)
    have hsg : sM * gM = gM * sM := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact m12PermS_comm_G)
    set g' : ↥K := e.symm gM
    set t' : ↥K := e.symm tM
    set s' : ↥K := e.symm sM
    have hg' : orderOf g' = 5 := by rw [MulEquiv.orderOf_eq, hgM]
    have hs' : orderOf s' = 2 := by rw [MulEquiv.orderOf_eq, hsM]
    have hc1' : t' * g' * t'⁻¹ ∈ Subgroup.zpowers g' := by
      have : t' * g' * t'⁻¹ = g' ^ 3 := by
        simp only [t', g', ← map_inv, ← map_mul, ← map_pow, hc1]
      rw [this]
      exact Subgroup.npow_mem_zpowers g' 3
    have hc2' : t'⁻¹ * g' * t' ∈ Subgroup.zpowers g' := by
      have : t'⁻¹ * g' * t' = g' ^ 2 := by
        simp only [t', g', ← map_inv, ← map_mul, ← map_pow, hc2]
      rw [this]
      exact Subgroup.npow_mem_zpowers g' 2
    have ht4' : t' ^ 4 = 1 := by
      simp only [t', ← map_pow, ht4, map_one]
    have ht2' : t' ^ 2 * g' ≠ g' * t' ^ 2 := by
      simp only [t', g', ← map_pow, ← map_mul]
      exact fun heq => ht2 (e.symm.injective heq)
    have hsg' : s' * g' = g' * s' := by
      simp only [s', g', ← map_mul, hsg]
    have hgc : Nat.card (Subgroup.zpowers g') = 5 ^ (Nat.card ↥K).factorization 5 := by
      rw [Nat.card_zpowers, hg', hcard, h5]
    have h8N := eight_dvd_card_normalizer_sylow SD hgc hc1' hc2' ht4' ht2' hs' hsg'
    have h8Y : 8 ∣ Nat.card (X₁.subgroupOf K) := h8N.trans (Subgroup.card_dvd_of_le hSD)
    rw [hYcard] at h8Y
    norm_num at h8Y
  ·
    have h11 : (11 : ℕ) ^ (95040 : ℕ).factorization 11 = 11 :=
      (pow_eq_pow_factorization_of_eq (a := 1) (k := 8640) (by norm_num) (by norm_num)
        (by norm_num)).symm
    rw [h11] at hdY
    have h297 : 297 ∣ Nat.card (X₁.subgroupOf K) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 11) h3Y hdY
    have hidx := index_dvd_div_of_dvd_card h297
    rw [hcard] at hidx
    have key : ∀ m ∈ Nat.divisors 320, m ≡ 1 [MOD 3] → m ≡ 1 [MOD 11] → m = 1 := by
      decide +kernel
    exact hY1 (key _ (Nat.mem_divisors.mpr ⟨hidx, by norm_num⟩) hm3 hmd)

end CFSG.LocalAnalysis.AGL81I.Section3
