module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusClauses
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialPrimes
public import CFSG.CharacterTheory.Semidihedral.Principal.TrivialCoreTorusRegular
public import CFSG.CharacterTheory.Semidihedral.StationarySevenNineFinal

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem not_four_mul_eq_add_three {p f b : ℕ} (hp : p.Prime) (hq : 9 < p ^ f) (hb1 : 1 < b)
    (hbodd : Odd b)
    (hprimes : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ b → ℓ ∣ p ^ f * (p ^ f - 1) * (p ^ f + 1))
    {e : ℤ} (he : e = 1 ∨ e = -1) (hb : 4 * (b : ℤ) = ((p ^ f : ℕ) : ℤ) + 3 * e) : False := by
  have he2 : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have key : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ b → ℓ = 3 := by
    intro ℓ hℓ hℓb
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hbodd) (even_iff_two_dvd.mpr hℓb)
    have hq1 : 1 ≤ p ^ f := by omega
    set Q : ℤ := ((p ^ f : ℕ) : ℤ) with hQ
    have h1 : (ℓ : ℤ) ∣ Q + 3 * e := by
      rw [← hb]
      exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hℓb) 4
    have h2 : (ℓ : ℤ) ∣ Q * (Q - 1) * (Q + 1) := by
      have h := Int.natCast_dvd_natCast.mpr (hprimes ℓ hℓ hℓb)
      push_cast [hq1] at h
      exact h
    have h3 : (ℓ : ℤ) ∣ 24 * e := by
      have hid : 24 * e = (Q + 3 * e) * (Q ^ 2 - 3 * e * Q + 8) - Q * (Q - 1) * (Q + 1) := by
        linear_combination (9 * Q) * he2
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_left h1 _) h2
    have h24 : ℓ ∣ 2 ^ 3 * 3 := by
      have h4 : (ℓ : ℤ) ∣ 24 := by
        rcases he with rfl | rfl
        · simpa using h3
        · have h5 := dvd_neg.mpr h3
          simpa using h5
      have h6 : ℓ ∣ 24 := by exact_mod_cast h4
      norm_num
      exact h6
    rcases (Nat.Prime.dvd_mul hℓ).mp h24 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h)) hℓ2
    · exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h
  obtain ⟨ℓ, hℓ, hℓb⟩ := Nat.exists_prime_and_dvd (show b ≠ 1 by omega)
  have hℓ3 := key ℓ hℓ hℓb
  rw [hℓ3] at hℓb
  have h3q : (3 : ℤ) ∣ ((p ^ f : ℕ) : ℤ) := by
    have h1 : (3 : ℤ) ∣ 4 * (b : ℤ) := dvd_mul_of_dvd_right (by exact_mod_cast hℓb) 4
    rw [hb] at h1
    have h2 := dvd_sub h1 (dvd_mul_right (3 : ℤ) e)
    simpa using h2
  have hp3 : p = 3 := by
    have h1 : 3 ∣ p ^ f := by exact_mod_cast h3q
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h1)).symm
  subst hp3
  have hf3 : 3 ≤ f := by
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at hq
  have h27 : 27 ∣ 3 ^ f := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.pow_dvd_pow 3 hf3
  have hqge : 27 ≤ 3 ^ f := Nat.le_of_dvd (by positivity) h27
  obtain ⟨b', hb'⟩ := hℓb
  have hb'1 : 1 < b' := by
    have h1 : (27 : ℤ) ≤ ((3 ^ f : ℕ) : ℤ) := by exact_mod_cast hqge
    have h2 : (24 : ℤ) ≤ 4 * (b : ℤ) := by
      rw [hb]
      rcases he with rfl | rfl <;> linarith
    have h3 : (b : ℤ) = 3 * b' := by exact_mod_cast hb'
    omega
  obtain ⟨ℓ', hℓ', hℓ'b⟩ := Nat.exists_prime_and_dvd (show b' ≠ 1 by omega)
  have hℓ'3 := key ℓ' hℓ' (hb' ▸ Dvd.dvd.mul_left hℓ'b 3)
  rw [hℓ'3] at hℓ'b
  obtain ⟨b'', hb''⟩ := hℓ'b
  have h9 : (9 : ℤ) ∣ ((3 ^ f : ℕ) : ℤ) + 3 * e - 4 * (b : ℤ) := by
    rw [← hb, sub_self]
    exact dvd_zero 9
  have hb9 : (b : ℤ) = 9 * b'' := by
    have : b = 9 * b'' := by rw [hb', hb'']; ring
    exact_mod_cast this
  have h27' : (27 : ℤ) ∣ ((3 ^ f : ℕ) : ℤ) := by exact_mod_cast h27
  obtain ⟨c, hc⟩ := h27'
  rw [hb9, hc] at h9
  rcases he with rfl | rfl <;> omega

theorem fixed_core_nontrivial_of_cases
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 7 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hI : 9 < p ^ f →
      (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥ → N t ≠ ⊥ →
      ∀ (d : G) (F' : Type) [Field F'] [Finite F']
        (φ : torusH G t (fS (s n) : G) ⧸ CFSG.pPrimeCore 2 (torusH G t (fS (s n) : G)) ≃*
          CFSG.GorensteinWalter.PGL2 F'),
        TorusNormalizerClauses G t (fS (s n) : G) d (p ^ f) F' φ →
        ((Nat.card F' : ℕ) : ℤ) + (if Nat.card F' % 4 = 1 then 1 else -1) =
          ((p ^ f : ℕ) : ℤ) + (if p ^ f % 4 = 1 then 1 else -1))
    (hIIa : 9 < p ^ f →
      (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥ → N t ≠ ⊥ →
      ∀ (d : G) (F' : Type) [Field F'] [Finite F']
        (φ : torusH G t (fS (s n) : G) ⧸ CFSG.pPrimeCore 2 (torusH G t (fS (s n) : G)) ≃*
          CFSG.GorensteinWalter.PGL2 F'),
        TorusNormalizerClauses G t (fS (s n) : G) d (p ^ f) F' φ → Nat.card F' ≠ p ^ f) :
    (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} ≠ ⊥ := by
  intro hA₀
  obtain ⟨-, -, -, hsC, -, -⟩ := Principal.supplied_t_s_facts hn fS ht
  have hqodd : Odd (p ^ f) := hpodd.pow
  by_cases hN : N t = ⊥
  ·
    obtain ⟨h57, -⟩ := Principal.simple_trivial_core_field_factor_one_is_regular hGnonab n hn S fS
      t ht hnonab hcentral hnc p f hp hpodd hf (by omega) hmodel hN hY
    omega
  rcases (show p ^ f = 9 ∨ 9 < p ^ f by obtain ⟨k, hk⟩ := hqodd; omega) with h9 | h9
  ·
    obtain ⟨hNZ, -⟩ :=
      StationarySevenNine.stationary_all_prime_parameter_nine_with_nontrivial_odd_core_is_regular
        hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf h9 hmodel hcov hN
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hxA : (x : G) ∈ (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} := by
      refine ⟨⟨x, hx, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hz := Subgroup.mem_center_iff.mp (hNZ hx) ⟨fS (s n), hsC⟩
      exact (congrArg Subtype.val hz).symm
    rw [hA₀, Subgroup.mem_bot] at hxA
    exact Subgroup.mem_bot.mpr (Subtype.ext hxA)
  obtain ⟨d, F', hF', hF'fin, φ, hcl⟩ := trivial_fixed_core_torus_clauses G hGnonab hrecognition n
    hn S fS t ht hnonab hcentral hnc p f hp hpodd hf h9 hmodel hcov hY hA₀ hN
  have hsum := hI h9 hA₀ hN d F' φ hcl
  have hne := hIIa h9 hA₀ hN d F' φ hcl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h4B, -⟩ := hcl
  have hBcard : Nat.card ((N t).map (C t).subtype) = Nat.card (N t) :=
    Subgroup.card_map_of_injective (C t).subtype_injective
  rw [hBcard] at h4B
  have hprimes := trivial_fixed_core_odd_core_primes_divide_characteristic_orders G hGnonab
    hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf h9 hmodel hcov hY hA₀
  have hbodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hb1 : 1 < Nat.card (N t) := by
    have h0 : 0 < Nat.card (N t) := Nat.card_pos
    have h1 : Nat.card (N t) ≠ 1 := fun h1 => hN (Subgroup.card_eq_one.mp h1)
    omega
  set e : ℤ := if p ^ f % 4 = 1 then 1 else -1 with hedef
  set e' : ℤ := if Nat.card F' % 4 = 1 then 1 else -1 with he'def
  have he : e = 1 ∨ e = -1 := by rw [hedef]; split_ifs <;> simp
  have he' : e' = 1 ∨ e' = -1 := by rw [he'def]; split_ifs <;> simp
  have hne' : ((Nat.card F' : ℕ) : ℤ) ≠ ((p ^ f : ℕ) : ℤ) := fun h => hne (by exact_mod_cast h)
  have hb : 4 * (Nat.card (N t) : ℤ) = ((p ^ f : ℕ) : ℤ) + 3 * e := by
    change 4 * (Nat.card (N t) : ℤ) = (Nat.card F' : ℤ) - e' at h4B
    rcases he with he | he <;> rcases he' with he' | he' <;> rw [he, he'] at hsum <;>
      rw [he'] at h4B <;> rw [he] <;> omega
  exact not_four_mul_eq_add_three hp h9 hb1 hbodd hprimes he hb

end CFSG.Semidihedral.FixedCoreNontrivial
