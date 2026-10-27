module

public import CFSG.CharacterTheory.Semidihedral.FusionTypes
public import CFSG.Dihedral.DihedralFusionStepReplacement

public section

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral

variable {n : ℕ}

theorem modulus_neZero (n : ℕ) : NeZero (modulus n) := ⟨pow_ne_zero _ two_ne_zero⟩

theorem aut_r_coords (hn : 4 ≤ n) (ψ : MulAut (SemidihedralGroup n)) :
    ∃ a : ZMod (modulus n), a.val % 2 = 1 ∧ ψ (r n) = element n (by omega) a 0 := by
  obtain ⟨⟨a, e⟩, he⟩ := (coordinateEquiv n (by omega)).symm.surjective (ψ (r n))
  change element n (by omega) a e = ψ (r n) at he
  have hord : orderOf (ψ (r n)) = modulus n := by
    rw [MulEquiv.orderOf_eq, orderOf_r n (by omega)]
  rcases exponent_cases e with rfl | rfl
  · refine ⟨a, ?_, he.symm⟩
    rw [← he] at hord
    exact (rotation_full_order_iff n hn a).mp hord
  · exfalso
    rw [← he] at hord
    have hb := modulus_ge_eight n hn
    rcases exterior_order_cases n (by omega) a with h | h <;> omega

theorem aut_rotation (hn : 4 ≤ n) (ψ : MulAut (SemidihedralGroup n)) {a : ZMod (modulus n)}
    (ha : ψ (r n) = element n (by omega) a 0) (i : ZMod (modulus n)) :
    ψ (element n (by omega) i 0) = element n (by omega) (a * i) 0 := by
  have := modulus_neZero n
  have h : element n (by omega) i 0 = r n ^ i.val := by
    rw [r_pow_eq_element n (by omega), ZMod.natCast_zmod_val]
  rw [h, map_pow, ha, element_rotation_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

theorem isUnit_of_odd (a : ZMod (modulus n)) (ha : a.val % 2 = 1) : IsUnit a := by
  have := modulus_neZero n
  have hcop : Nat.Coprime a.val (modulus n) := by
    apply Nat.Coprime.pow_right
    exact Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ha)
  rw [← ZMod.natCast_zmod_val a]
  exact (ZMod.isUnit_iff_coprime _ _).mpr hcop

theorem aut_s_coords (hn : 4 ≤ n) (ψ : MulAut (SemidihedralGroup n)) {a : ZMod (modulus n)}
    (ha : a.val % 2 = 1) (har : ψ (r n) = element n (by omega) a 0) :
    ∃ b : ZMod (modulus n), ψ (s n) = element n (by omega) b 1 := by
  obtain ⟨⟨b, e⟩, he⟩ := (coordinateEquiv n (by omega)).symm.surjective (ψ (s n))
  change element n (by omega) b e = ψ (s n) at he
  rcases exponent_cases e with rfl | rfl
  · exfalso
    obtain ⟨u, hu⟩ := isUnit_of_odd a ha
    have hrot := aut_rotation hn ψ har (↑u⁻¹ * b)
    have hab : a * (↑u⁻¹ * b) = b := by
      rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hab, he] at hrot
    have hinj := ψ.injective hrot
    rw [s_eq_element n (by omega), element_eq_iff] at hinj
    exact absurd hinj.2 (by decide)
  · exact ⟨b, he.symm⟩

theorem aut_outside (hn : 4 ≤ n) (ψ : MulAut (SemidihedralGroup n)) {a b : ZMod (modulus n)}
    (har : ψ (r n) = element n (by omega) a 0) (hbs : ψ (s n) = element n (by omega) b 1)
    (i : ZMod (modulus n)) :
    ψ (element n (by omega) i 1) = element n (by omega) (a * i + b) 1 := by
  have h : element n (by omega) i 1 = element n (by omega) i 0 * s n := by
    rw [s_eq_element n (by omega), element_rotation_mul, add_zero]
  rw [h, map_mul, aut_rotation hn ψ har, hbs, element_rotation_mul]

theorem aut_pow_coords (hn : 4 ≤ n) (ψ : MulAut (SemidihedralGroup n)) {a b : ZMod (modulus n)}
    (har : ψ (r n) = element n (by omega) a 0) (hbs : ψ (s n) = element n (by omega) b 1)
    (j : ℕ) :
    (ψ ^ j) (r n) = element n (by omega) (a ^ j) 0 ∧
      (ψ ^ j) (s n) = element n (by omega) (b * ∑ i ∈ Finset.range j, a ^ i) 1 := by
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [pow_zero, pow_zero, MulAut.one_apply]
      have h := r_pow_eq_element n (by omega) 1
      rw [pow_one, Nat.cast_one] at h
      exact h
    · rw [pow_zero, MulAut.one_apply, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact s_eq_element n (by omega)
  | succ j ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ', MulAut.mul_apply, ih.1, aut_rotation hn ψ har, pow_succ']
    · rw [pow_succ', MulAut.mul_apply, ih.2, aut_outside hn ψ har hbs,
        Finset.sum_range_succ', pow_zero]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, mul_add, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

theorem unit_eq_one_of_pow_odd (u : (ZMod (modulus n))ˣ) {m : ℕ} (hm : Odd m) (hu : u ^ m = 1) :
    u = 1 := by
  have := modulus_neZero n
  have h1 : orderOf u ∣ m := orderOf_dvd_of_pow_eq_one hu
  have htot : (modulus n).totient ∣ 2 ^ (n - 1 - 1) * (2 - 1) := by
    rw [modulus]
    rcases Nat.eq_zero_or_pos (n - 1) with h0 | hpos
    · rw [h0, pow_zero, Nat.totient_one]
      exact one_dvd _
    · rw [Nat.totient_prime_pow Nat.prime_two hpos]
  have h2 : orderOf u ∣ 2 ^ (n - 1 - 1) * (2 - 1) := by
    have hc := orderOf_dvd_card (G := (ZMod (modulus n))ˣ) (x := u)
    rw [ZMod.card_units_eq_totient] at hc
    exact hc.trans htot
  have h2' : orderOf u ∣ 2 ^ (n - 1 - 1) := by simpa using h2
  have hcop : Nat.Coprime m (2 ^ (n - 1 - 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  have h3 : orderOf u ∣ Nat.gcd m (2 ^ (n - 1 - 1)) := Nat.dvd_gcd h1 h2'
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem aut_eq_one_of_pow_odd (hn : 4 ≤ n) (ψ : MulAut (SemidihedralGroup n)) {m : ℕ}
    (hm : Odd m) (hψ : ψ ^ m = 1) : ψ = 1 := by
  have := modulus_neZero n
  obtain ⟨a, ha, har⟩ := aut_r_coords hn ψ
  obtain ⟨b, hbs⟩ := aut_s_coords hn ψ ha har
  obtain ⟨hr, hs⟩ := aut_pow_coords hn ψ har hbs m
  rw [hψ, MulAut.one_apply] at hr hs
  have hr1 : r n = element n (by omega) 1 0 := by
    have h := r_pow_eq_element n (by omega) 1
    rw [pow_one, Nat.cast_one] at h
    exact h
  rw [hr1, element_eq_iff] at hr
  obtain ⟨u, hu⟩ := isUnit_of_odd a ha
  have hum : u ^ m = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, ← hr.1, Units.val_one]
  have hu1 := unit_eq_one_of_pow_odd u hm hum
  have ha1 : a = 1 := by rw [← hu, hu1, Units.val_one]
  rw [s_eq_element n (by omega), element_eq_iff, ha1] at hs
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
  have hmu : IsUnit (m : ZMod (modulus n)) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  have hb0 : b = 0 := by
    obtain ⟨v, hv⟩ := hmu
    have h := hs.1
    rw [← hv] at h
    have h' : b * ↑v * ↑v⁻¹ = 0 * ↑v⁻¹ := by rw [h]
    rwa [mul_assoc, Units.mul_inv, mul_one, zero_mul] at h'
  apply MulEquiv.ext
  intro x
  have hhom : (ψ : SemidihedralGroup n →* SemidihedralGroup n) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro i
    fin_cases i
    · change ψ (r n) = r n
      rw [har, ha1, ← hr1]
    · change ψ (s n) = s n
      rw [hbs, hb0, ← s_eq_element n (by omega)]
  have := DFunLike.congr_fun hhom x
  simpa using this

theorem semidihedral_automorphism_isPGroup (hn : 4 ≤ n) :
    IsPGroup 2 (MulAut (SemidihedralGroup n)) := by
  have := presentation_finite n (by omega)
  intro φ
  have hpos : 0 < orderOf φ := orderOf_pos φ
  set e := (orderOf φ).factorization 2
  obtain ⟨m, hm, hdecomp⟩ : ∃ m, Odd m ∧ orderOf φ = 2 ^ e * m := by
    refine ⟨orderOf φ / 2 ^ e, ?_, (Nat.mul_div_cancel' (Nat.ordProj_dvd _ 2)).symm⟩
    have hnd := Nat.not_dvd_ordCompl Nat.prime_two hpos.ne'
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  refine ⟨e, aut_eq_one_of_pow_odd hn (φ ^ 2 ^ e) hm ?_⟩
  rw [← pow_mul, ← hdecomp, pow_orderOf_eq_one]

theorem sylow_normalizer_eq_mul_centralizer {G : Type*} [Group G] [Finite G] (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) :
    ∀ x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), ∃ q ∈ (S : Subgroup G),
      ∃ c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G), x = q * c := by
  intro g hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haut : IsPGroup 2 (MulAut (S : Subgroup G)) :=
    (semidihedral_automorphism_isPGroup hn).of_equiv (MulAut.congr fS)
  obtain ⟨q, hq, hqg⟩ := CFSG.GorensteinWalter.hom_to_pGroup_image_on_sylow haut
    (S : Subgroup G).normalizerMonoidHom (S.subtype (Subgroup.le_normalizer)) ⟨g, hg⟩
  rw [Sylow.coe_subtype] at hq
  refine ⟨q, hq, (q : G)⁻¹ * g, ?_, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := DFunLike.congr_fun hqg ⟨x, hx⟩
  have h' := congrArg Subtype.val h
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.normalizerMonoidHom_apply_apply_coe] at h'
  change (q : G) * x * (q : G)⁻¹ = g * x * g⁻¹ at h'
  calc
    x * ((q : G)⁻¹ * g) = (q : G)⁻¹ * ((q : G) * x * (q : G)⁻¹) * g := by group
    _ = (q : G)⁻¹ * (g * x * g⁻¹) * g := by rw [h']
    _ = (q : G)⁻¹ * g * x := by group

end CFSG.Semidihedral.FieldFactorOne
