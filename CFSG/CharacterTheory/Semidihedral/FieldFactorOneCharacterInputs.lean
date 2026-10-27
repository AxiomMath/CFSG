module

public import CFSG.CharacterTheory.Semidihedral.Principal.PerfectSemidihedralRotationCongruences
public import CFSG.CharacterTheory.Semidihedral.Principal.EvenFourierFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.Principal CFSG.TwoRankLowerBound.Helpers

theorem sign_mul_sub_one_modEq {n : ℕ} (hn : 4 ≤ n) {q : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (hqM : 2 ^ padicValNat 2 (q ^ 2 - 1) = modulus n) {e : ℤ} (he1 : q % 4 = 1 → e = 1)
    (he3 : q % 4 = 3 → e = -1) :
    e * q - 1 ≡ 2 * ((2 ^ (n - 3) : ℕ) : ℤ) [ZMOD 4 * ((2 ^ (n - 3) : ℕ) : ℤ)] := by
  obtain ⟨u, hu⟩ := RotationCongruence.eq_sub_one_odd_multiple_half hn hq hqodd hqM he1 he3
  have hhalf : (half n : ℤ) = 2 * ((2 ^ (n - 3) : ℕ) : ℤ) := by
    rw [half, show n - 2 = (n - 3) + 1 by omega, pow_succ]
    push_cast
    ring
  rw [Int.modEq_iff_dvd]
  refine ⟨-u, ?_⟩
  rw [hu, hhalf]
  ring

theorem transversal_enum_inputs {n : ℕ} (hn : 4 ≤ n) {I : Finset (ZMod (modulus n))}
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I)
    {o : ℕ → ZMod (modulus n)} (ho0 : o 0 = 1)
    (homem : ∀ i ∈ Finset.range (2 ^ (n - 3)), o i ∈ I)
    (hosurj : ∀ x ∈ I, ∃ i ∈ Finset.range (2 ^ (n - 3)), o i = x) :
    (∀ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1), Odd (o j).val ∧ (o j).val < 4 * 2 ^ (n - 3)) ∧
    (∀ j < 4 * 2 ^ (n - 3), Odd j → j = 1 ∨ j = (2 * 2 ^ (n - 3) - 1) % (4 * 2 ^ (n - 3)) ∨
      ∃ i ∈ Finset.Icc 1 (2 ^ (n - 3) - 1), j = (o i).val ∨
        j = (2 * 2 ^ (n - 3) - 1) * (o i).val % (4 * 2 ^ (n - 3))) := by
  obtain ⟨hM4, hKeven, hK2, hhalf⟩ := modulus_eq_four_mul hn
  set k : ℕ := 2 ^ (n - 3) with hk
  set a : ZMod (modulus n) := ((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1 with ha
  have haval : a.val = 2 * k - 1 := supplied_twist_val hn
  have haa : a * a = 1 := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (twist_sq_modEq hn)
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one] at h
    exact h
  have hval1 : (1 : ZMod (modulus n)).val = 1 := by
    have : Fact (1 < modulus n) := ⟨by omega⟩
    exact ZMod.val_one _
  have hIcc : ∀ i ∈ Finset.range k, i ≠ 0 → i ∈ Finset.Icc 1 (k - 1) := fun i hi hi0 => by
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]
    omega
  refine ⟨fun j hj => ⟨hI.odd _ (homem j (Finset.mem_range.mpr (by
    have := (Finset.mem_Icc.mp hj).2
    omega))), by rw [← hM4]; exact ZMod.val_lt _⟩, ?_⟩
  intro j hj hjodd
  set x : ZMod (modulus n) := (j : ZMod (modulus n)) with hx
  have hxval : x.val = j := ZMod.val_natCast_of_lt (by omega)
  have hpair := hI.pair x (by rw [hxval]; exact hjodd)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (({x, a * x} : Finset _) ∩ I).card)
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hy
  obtain ⟨hy1 | hy2, hyI⟩ := hy
  · rw [hy1] at hyI
    obtain ⟨i, hi, hoi⟩ := hosurj x hyI
    by_cases hi0 : i = 0
    · left
      rw [← hxval, ← hoi, hi0, ho0, hval1]
    · right
      right
      exact ⟨i, hIcc i hi hi0, Or.inl (by rw [← hxval, hoi])⟩
  · rw [hy2] at hyI
    obtain ⟨i, hi, hoi⟩ := hosurj (a * x) hyI
    have hxa : x = a * o i := by rw [hoi, ← mul_assoc, haa, one_mul]
    have hjval : j = (2 * k - 1) * (o i).val % (4 * k) := by
      rw [← hxval, hxa, ZMod.val_mul, haval]
      exact congrArg _ hM4
    by_cases hi0 : i = 0
    · right
      left
      rw [hjval, hi0, ho0, hval1, mul_one]
    · right
      right
      exact ⟨i, hIcc i hi hi0, Or.inr hjval⟩

variable {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}

theorem character_multiplicity_inputs (hn : 4 ≤ n) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index) :
    (∀ j < 4 * 2 ^ (n - 3),
      multiplicityColumn basis (fS (r n) : G) (modulus n)
          (((2 * 2 ^ (n - 3) - 1) * j % (4 * 2 ^ (n - 3)) : ℕ) : ℤ) χ =
        multiplicityColumn basis (fS (r n) : G) (modulus n) (j : ℤ) χ) ∧
    (Module.finrank ℂ (basis.representation χ).vector : ℤ) =
      ∑ j ∈ Finset.range (4 * 2 ^ (n - 3)),
        multiplicityColumn basis (fS (r n) : G) (modulus n) (j : ℤ) χ ∧
    (basis.representation χ).character ((fS (r n) : G) ^ 2 ^ (n - 2)) =
      ((∑ j ∈ Finset.range (4 * 2 ^ (n - 3)),
        (-1) ^ j * multiplicityColumn basis (fS (r n) : G) (modulus n) (j : ℤ) χ : ℤ) : ℂ) := by
  obtain ⟨hM4, hKeven, hK2, hhalf⟩ := modulus_eq_four_mul hn
  set k : ℕ := 2 ^ (n - 3) with hk
  have hM : 0 < modulus n := by omega
  have hr : (fS (r n) : G) ^ modulus n = 1 := supplied_r_pow_modulus fS
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  ·
    have hcong : ((((2 * k - 1) * j % (4 * k) : ℕ)) : ℤ) ≡
        (((modulus n / 2 : ℕ) : ℤ) - 1) * (j : ℤ) [ZMOD modulus n] := by
      have h1 : 1 ≤ 2 * k := by omega
      have h2 : ((modulus n / 2 : ℕ) : ℤ) = 2 * (k : ℤ) := by
        rw [show modulus n / 2 = 2 * k by omega]
        push_cast
        ring
      have h3 : ((modulus n : ℕ) : ℤ) = 4 * (k : ℤ) := by
        rw [hM4]
        push_cast
        ring
      rw [h2, h3, Int.natCast_mod, Nat.cast_mul, Nat.cast_sub h1]
      push_cast
      exact Int.mod_modEq _ _
    rw [multiplicityColumn_congr basis _ _ hcong]
    exact congrFun (supplied_multiplicityColumn_twist hn fS basis (j : ℤ)) χ
  ·
    have h := cyclicMultiplicity_inversion (basis.representation χ).character (fS (r n) : G) hM
      (w := 0) hM
    rw [pow_zero, (basis_character_one basis χ).1] at h
    have h' : (((Module.finrank ℂ (basis.representation χ).vector : ℤ)) : ℂ) =
        ((∑ j ∈ Finset.range (4 * k),
          multiplicityColumn basis (fS (r n) : G) (modulus n) (j : ℤ) χ : ℤ) : ℂ) := by
      rw [Int.cast_natCast, h, Int.cast_sum, ← hM4]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [multiplicityColumn_cast basis hM hr, Nat.cast_zero, mul_zero, zpow_zero, mul_one]
    exact_mod_cast h'
  ·
    have h := character_half_pow_eq_signed_sum basis hM ⟨2 * k, by omega⟩ hr χ
    rw [show modulus n / 2 = 2 ^ (n - 2) by omega] at h
    rw [← hM4]
    exact h

end CFSG.Semidihedral.FieldFactorOne
