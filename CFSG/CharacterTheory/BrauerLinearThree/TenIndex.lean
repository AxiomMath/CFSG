module

public import CFSG.CharacterTheory.BrauerLinearThree.TenExclusion
public import CFSG.CharacterTheory.BrauerLinearThree.TenArith

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.LargePrimeTorus
open CFSG.Semidihedral (r s modulus)

theorem chi_one_column_false {Gc c m q f₁ f₂ f₃ : ℕ} {e δ δ₁ δ₂ δ₃ A : ℤ} {x : ℂ}
    (he : e = -1) (hδ : δ = 1 ∨ δ = -1) (hδ₁ : δ₁ = 1 ∨ δ₁ = -1) (hA : A = 9 ∨ A = 5)
    (hm5 : 5 ≤ m) (hm7 : A = 5 → 7 ≤ m) (hqe : (q : ℤ) + e = 2 * m)
    (hc : (c : ℤ) = 2 * q * ((q : ℤ) ^ 2 - 1)) (hc0 : c ≠ 0)
    (hf₁ : 1 < (f₁ : ℤ)) (ho₁ : Odd (f₁ : ℤ))
    (hsigns : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hsum : 1 + δ₁ * (f₁ : ℤ) + δ₂ * (f₂ : ℤ) + δ₃ * (f₃ : ℤ) = 0)
    (hprod : (f₁ : ℤ) * (f₂ : ℤ) = (q : ℤ) ^ 2 * (f₃ : ℤ))
    (hne : (f₁ : ℚ) - e * δ₁ * q ≠ 0)
    (hG : (Gc : ℚ) = (c : ℚ) ^ 3 / ((4 * m : ℕ) : ℚ) ^ 2 *
      ((f₁ : ℚ) * (f₁ + δ₁) / (f₁ - e * δ₁ * q) ^ 2) * ((q + e) / q))
    (hx : x = (δ₁ : ℂ) * e * q)
    (h3 : 3 * (Gc : ℂ) * ((f₁ : ℂ) - x) ^ 2 =
      A * m * (c : ℂ) ^ 2 * ((f₁ : ℂ) * ((f₁ : ℂ) + δ))) : False := by
  have hm0 : m ≠ 0 := by omega
  have hq9 : (9 : ℤ) ≤ q := by omega
  have hqZ0 : (q : ℤ) ≠ 0 := by omega
  rw [hx] at h3
  have h3Z : 3 * (Gc : ℤ) * ((f₁ : ℤ) - e * δ₁ * q) ^ 2 =
      A * m * (c : ℤ) ^ 2 * ((f₁ : ℤ) * (f₁ + δ)) := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination h3
  have hX : (f₁ : ℤ) - e * δ₁ * q ≠ 0 := by
    intro h0
    apply hne
    have h0' : (((f₁ : ℤ) - e * δ₁ * q : ℤ) : ℚ) = 0 := by exact_mod_cast h0
    rw [← h0']
    push_cast
    ring
  have hord := order_column_int (Y := (f₁ : ℤ) * (f₁ + δ₁)) (Z := (q : ℤ) + e) hX hc0 hm0
    hqZ0 (by rw [hG]; push_cast; ring) h3Z hqe.symm
  rw [hc] at hord
  rcases (show δ = δ₁ ∨ δ = -δ₁ by omega) with hδ' | hδ'
  · rw [hδ'] at hord
    exact TenArith.chi_one_same_false (Or.inr he) hA (by omega)
      (mul_ne_zero (by omega) (by omega)) hqe.symm hord
  · rw [hδ', ← sub_eq_add_neg] at hord
    rcases hA with hA' | hA'
    · rw [hA'] at hord
      exact chi_one_four_false (Or.inr he) hδ₁ hq9 hf₁ ho₁ hqe.symm hord
    · rw [hA'] at hord
      have hm7' : (7 : ℤ) ≤ m := by exact_mod_cast hm7 hA'
      by_cases hm9 : (m : ℤ) = 9
      · have hq19 : (q : ℤ) = 19 := by omega
        rw [hq19, he, hm9] at hord
        rw [hq19] at hprod
        exact TenArith.chi_one_nineteen_false hsigns hf₁ hsum hprod (by linear_combination hord)
      · exact chi_one_five_false (Or.inr he) hδ₁ hm7' hm9 hf₁ hqe.symm hord

theorem chi_two_column_false {Gc c m q f₂ n : ℕ} {e δ δ₂ A : ℤ} {x : ℂ} (hn : 4 ≤ n)
    (he : e = -1) (hδ : δ = 1 ∨ δ = -1) (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hA : A = 9 ∨ A = 5)
    (hm5 : 5 ≤ m) (hmodd : Odd m) (hqe : (q : ℤ) + e = 2 * m)
    (hv2 : padicValNat 2 (q ^ 2 - 1) = n - 1)
    (hc : (c : ℤ) = 2 * q * ((q : ℤ) ^ 2 - 1)) (hc0 : c ≠ 0) (hf₂ : 1 < (f₂ : ℤ))
    (hc₂ : (f₂ : ℤ) ≡ -δ₂ * e * q [ZMOD 2 * modulus n])
    (hne : (f₂ : ℚ) + e * δ₂ * q ≠ 0)
    (hG : (Gc : ℚ) = (c : ℚ) ^ 3 / ((4 * m : ℕ) : ℚ) ^ 2 *
      ((f₂ : ℚ) * (f₂ + δ₂) / (f₂ + e * δ₂ * q) ^ 2) * ((q - e) / q))
    (hx : x = -((δ₂ : ℂ) * e * q))
    (h3 : 3 * (Gc : ℂ) * ((f₂ : ℂ) - x) ^ 2 =
      A * m * (c : ℂ) ^ 2 * ((f₂ : ℂ) * ((f₂ : ℂ) + δ))) : False := by
  have hm0 : m ≠ 0 := by omega
  have hqm : q = 2 * m + 1 := by omega
  have hq9 : (9 : ℤ) ≤ q := by omega
  have hqZ0 : (q : ℤ) ≠ 0 := by omega
  rw [hx] at h3
  have h3Z : 3 * (Gc : ℤ) * ((f₂ : ℤ) + e * δ₂ * q) ^ 2 =
      A * m * (c : ℤ) ^ 2 * ((f₂ : ℤ) * (f₂ + δ)) := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination h3
  have hX : (f₂ : ℤ) + e * δ₂ * q ≠ 0 := by
    intro h0
    apply hne
    have h0' : (((f₂ : ℤ) + e * δ₂ * q : ℤ) : ℚ) = 0 := by exact_mod_cast h0
    rw [← h0']
    push_cast
    ring
  have hord := order_column_int (Y := (f₂ : ℤ) * (f₂ + δ₂)) (Z := (q : ℤ) - e) hX hc0 hm0
    hqZ0 (by rw [hG]; push_cast; ring) h3Z hqe.symm
  rw [hc] at hord
  rcases (show δ = δ₂ ∨ δ = -δ₂ by omega) with hδ' | hδ'
  · rw [hδ'] at hord
    exact chi_two_false (Or.inr he) hA hq9 (mul_ne_zero (by omega) (by omega)) hqe.symm hord
  · rw [hδ', ← sub_eq_add_neg, he] at hord
    rw [he] at hqe
    have hkey : (2 * (q : ℤ) * ((q : ℤ) - 1) * f₂) *
        (3 * ((q : ℤ) + 1) ^ 2 * (f₂ + δ₂) - A * ((q : ℤ) - 1) ^ 2 * (f₂ - δ₂)) = 0 := by
      linear_combination hord - 2 * A * (q : ℤ) * ((q : ℤ) - 1) ^ 2 * f₂ * (f₂ - δ₂) * hqe
    have hne' : 2 * (q : ℤ) * ((q : ℤ) - 1) * f₂ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by omega)
    have h := sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_left hne')
    have hAodd : Odd A := by
      rcases hA with h' | h' <;> rw [h']
      · exact ⟨4, by norm_num⟩
      · exact ⟨2, by norm_num⟩
    have hmoddZ : Odd (m : ℤ) := by exact_mod_cast hmodd
    have hqu : (q : ℤ) - 1 = 2 * m := by linear_combination hqe
    have hdvd : 2 ^ (n - 1) ∣ q ^ 2 - 1 := by
      have h' := pow_padicValNat_dvd (p := 2) (n := q ^ 2 - 1)
      rwa [hv2] at h'
    have hq2 : q ^ 2 - 1 = 2 * (m * (q + 1)) := by
      apply Nat.sub_eq_of_eq_add
      rw [hqm]
      ring
    have hdvd' : 2 ^ (n - 2) ∣ m * (q + 1) := by
      have h2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hq2, h2] at hdvd
      exact (Nat.mul_dvd_mul_iff_left two_pos).mp hdvd
    have hcop : Nat.Coprime (2 ^ (n - 2)) m :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hmodd)
    obtain ⟨v, hv⟩ := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd'
    have hqv : (q : ℤ) + 1 = 2 ^ (n - 2) * v := by exact_mod_cast hv
    obtain ⟨k₂, hk₂⟩ := Int.ModEq.dvd hc₂.symm
    have h2M : (2 : ℤ) * (modulus n : ℕ) = 2 ^ n := by
      rw [modulus]
      push_cast
      rw [← pow_succ']
      congr 1
      omega
    have hf2 : (f₂ : ℤ) = δ₂ * q + 2 ^ n * k₂ := by
      rw [← h2M]
      rw [he] at hk₂
      linear_combination hk₂
    exact TenArith.chi_two_opposite_false hn hδ₂ hAodd hmoddZ hqv hqu hf2 h

theorem chi_three_column_false {Gc c m q f₃ n : ℕ} {δ δ₃ A : ℤ} {x : ℂ} (hn : 4 ≤ n)
    (hδ : δ = 1 ∨ δ = -1) (hδ₃ : δ₃ = 1 ∨ δ₃ = -1) (hA : A = 9 ∨ A = 5) (hmodd : Odd m)
    (hq7 : 7 ≤ q) (hqodd : Odd q) (hGc : Gc ≠ 0) (hfac : Gc.factorization 2 = n)
    (hv2 : padicValNat 2 (q ^ 2 - 1) = n - 1)
    (hc : (c : ℤ) = 2 * q * ((q : ℤ) ^ 2 - 1)) (ho₃ : Odd (f₃ : ℤ))
    (hc₃ : (f₃ : ℤ) ≡ δ₃ * (modulus n - 1) [ZMOD 2 * modulus n])
    (hx : x = -(δ₃ : ℂ))
    (h3 : 3 * (Gc : ℂ) * ((f₃ : ℂ) - x) ^ 2 =
      A * m * (c : ℂ) ^ 2 * ((f₃ : ℂ) * ((f₃ : ℂ) + δ))) : False := by
  rw [hx] at h3
  have h3Z : 3 * (Gc : ℤ) * ((f₃ : ℤ) + δ₃) ^ 2 =
      A * m * (c : ℤ) ^ 2 * ((f₃ : ℤ) * (f₃ + δ)) := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination h3
  have hGdec := Nat.ordProj_mul_ordCompl_eq_self Gc 2
  have hGodd := Nat.not_dvd_ordCompl Nat.prime_two hGc
  rw [hfac] at hGdec hGodd
  have hq21 : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (by omega)
    omega
  have hqdec := Nat.ordProj_mul_ordCompl_eq_self (q ^ 2 - 1) 2
  have huodd := Nat.not_dvd_ordCompl Nat.prime_two hq21
  rw [Nat.factorization_def _ Nat.prime_two, hv2] at hqdec huodd
  set u := (q ^ 2 - 1) / 2 ^ (n - 1) with hudef
  set g := Gc / 2 ^ n with hgdef
  have hcdec : (c : ℤ) = 2 ^ n * ((q : ℤ) * u) := by
    rw [hc]
    have h1 : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub this]
      ring
    have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← h1, ← hqdec, h2]
    push_cast
    ring
  have hGZ : (Gc : ℤ) = 2 ^ n * g := by
    rw [← hGdec]
    push_cast
    ring
  obtain ⟨k₃, hk₃⟩ := Int.ModEq.dvd hc₃.symm
  have hM : ((modulus n : ℕ) : ℤ) = 2 ^ (n - 1) := by
    rw [modulus]
    norm_cast
  rw [hM] at hk₃
  have hy' : (f₃ : ℤ) + δ₃ = 2 ^ (n - 1) * (2 * k₃ + δ₃) := by linear_combination hk₃
  have hyodd : Odd (2 * k₃ + δ₃) := by
    rcases hδ₃ with h | h <;> rw [h]
    · exact ⟨k₃, rfl⟩
    · exact ⟨k₃ - 1, by ring⟩
  have hAodd : Odd A := by
    rcases hA with h | h <;> rw [h]
    · exact ⟨4, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  have hmoddZ : Odd (m : ℤ) := by exact_mod_cast hmodd
  have hc'odd : Odd ((q : ℤ) * u) := by
    have hqo : Odd (q : ℤ) := by exact_mod_cast hqodd
    have huo : Odd (u : ℤ) := by
      have : Odd u := Nat.odd_iff.mpr (by omega)
      exact_mod_cast this
    exact hqo.mul huo
  have hgodd : Odd (g : ℤ) := by
    have : Odd g := Nat.odd_iff.mpr (by omega)
    exact_mod_cast this
  rw [hGZ, hcdec] at h3Z
  rcases (show δ = δ₃ ∨ δ = -δ₃ by omega) with hδ' | hδ'
  · rw [hδ'] at h3Z
    exact TenArith.chi_three_same_false (g := (g : ℤ)) (c' := (q : ℤ) * u) (A := A)
      (m := (m : ℤ)) hn hgodd hyodd hy' (by linear_combination h3Z)
  · rw [hδ'] at h3Z
    exact chi_three_false (g := (g : ℤ)) hn hδ₃ hAodd hmoddZ hc'odd ho₃ hy'
      (by linear_combination h3Z)

theorem card_torus_dvd_index
    {G : Type} [Group G] [Fintype G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    Nat.card W ∣ (W.subgroupOf K).index := by
  intro s₀ V D W K
  by_contra hndvd
  set q : ℕ := p ^ f with hqdef
  set e : ℤ := if q % 4 = 1 then 1 else -1 with hedef
  have he' : e = -1 := by simp [hedef, show ¬ q % 4 = 1 by omega]
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨hC, -, hWcyc, hWodd, hWcard, ⟨hsup, hdisj, -⟩, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hWcyc : IsCyclic W := hWcyc
  have hWodd : Odd (Nat.card W) := hWodd
  have hsup : V ⊔ W = D := hsup
  have hdisj : Disjoint V W := hdisj
  have hqodd : Odd q := hpodd.pow
  have hqe : (q : ℤ) + e = 2 * Nat.card W := by
    have hWcard' : (Nat.card W : ℤ) = ((q : ℤ) + e) / 2 := hWcard
    rw [he'] at hWcard' ⊢
    obtain ⟨k, hk⟩ := hqodd
    have hk' : (q : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    rw [hk'] at hWcard' ⊢
    omega
  have hq7 : 7 ≤ q := by omega
  have hm3 : 3 ≤ Nat.card W := by omega
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hDcard, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have hcZ : (Nat.card (C t) : ℤ) = 2 * q * ((q : ℤ) ^ 2 - 1) := by
    rw [hC]
    have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by positivity))
    push_cast [Nat.cast_sub h1]
    rfl
  have hScard : Nat.card (S : Subgroup G) = 2 ^ n := by
    rw [← Nat.card_congr fS.toEquiv]
    exact CFSG.Semidihedral.card n (by omega)
  have hfac : (Nat.card G).factorization 2 = n := by
    have h := S.card_eq_multiplicity
    rw [hScard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  obtain ⟨⟨ideal₂, hmax₂, h2mem⟩, hchar₂⟩ := CFSG.BlockBasics.residue_prime_existence 2
    Nat.prime_two
  have : ideal₂.IsMaximal := hmax₂
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2 := hchar₂ ideal₂ hmax₂ h2mem
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨ρ, δ, A, hA, hA9, hA5, hδ, hρo, hρodd, hρr, h3C⟩ :=
    exists_torus_column_relation n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hN
      hY basis principal hprincipal hndvd
  have hA9 : A = 9 → ¬ Nat.card W ∣ 3 := hA9
  have hA5 : A = 5 → ¬ Nat.card W ∣ 15 := hA5
  have h3C : 3 * (Nat.card G : ℂ) * ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) -
      (basis.representation ρ).character t) ^ 2 =
      A * Nat.card W * (Nat.card (C t) : ℂ) ^ 2 *
        ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) *
          ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) + δ)) := h3C
  have hm3' : Nat.card W ≠ 3 := by
    intro h3
    rcases hA with hA' | hA'
    · exact hA9 hA' ⟨1, by omega⟩
    · exact hA5 hA' ⟨5, by omega⟩
  have hm5 : 5 ≤ Nat.card W := by
    obtain ⟨j, hj⟩ := hWodd
    omega
  have hm7 : A = 5 → 7 ≤ Nat.card W := by
    intro hA'
    have h5 : Nat.card W ≠ 5 := fun h5 => hA5 hA' ⟨3, by omega⟩
    obtain ⟨j, hj⟩ := hWodd
    omega
  obtain ⟨F, hfield, hfinite, ρF, hFcard, hρF, hLρF, -, hrest⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal₂ basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  obtain ⟨hφ1, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ₂, ν₂, hfam, hdeg, -, hOFall⟩ := hrest
  have hOF := hOFall S fS hcent
  have heF : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = e := by rw [hFcard]
  have hq3' : 3 ≤ Nat.card F := by rw [hFcard]; omega
  have hqoddF : Odd (Nat.card F) := by rw [hFcard]; exact hqodd
  have he1 : Nat.card F % 4 = 1 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 :=
    fun h => by simp [h]
  have he3 : Nat.card F % 4 = 3 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 :=
    fun h => by simp [show ¬ Nat.card F % 4 = 1 by omega]
  obtain ⟨F', hF', hF'fin, A', ρ', hdata⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht2
    hnonab hcentral hnc p f hp hpodd hf hmodel
  have hqM : 2 ^ padicValNat 2 (Nat.card F ^ 2 - 1) = modulus n := by
    have h := hdata.two_part
    rw [hdata.field_card, Nat.factorization_def _ Nat.prime_two] at h
    rw [hFcard, h]
    rfl
  have hv2 : padicValNat 2 (q ^ 2 - 1) = n - 1 := by
    have h := hqM
    rw [hFcard, modulus] at h
    exact Nat.pow_right_injective le_rfl h
  obtain ⟨hf₁, hf₂, -, ho₁, -, ho₃, hsigns, hsum2, hprod, -, hc₂⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal₂ principal hprincipal
      localBasis localPrincipal (Nat.card F) hq3' hqoddF hqM _ he1 he3 _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄
      ψ₂ ν₂ hfam hdeg
  obtain ⟨hrot, -, -, -⟩ := actual_principal_rotation_values_and_congruences hG hn ht2 hnonab
    basis ideal₂ principal hprincipal localBasis localPrincipal (Nat.card F) hq3' hqoddF _ he1 he3
    _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ₂ ν₂ hfam hdeg fS hcent
  obtain ⟨-, hδ₁, hδ₂, hδ₃, -, -, -, -, -, -, -, -, -, hodd2, hsec, -⟩ := hfam
  obtain ⟨h₁t, h₂t, h₃t, -⟩ := hsec 1 (by rw [orderOf_one]; decide)
  simp only [OneMemClass.coe_one, mul_one, hφ1] at h₁t h₂t h₃t
  obtain ⟨-, -, hc₃⟩ := perfect_semidihedral_rotation_values_full_sylow_degree_congruences hn
    S fS (fS (r n) : G) t rfl hcent.symm (Nat.card F) hq3' hqoddF hqM _ he1 he3
    (basis.representation χ₁) (basis.representation χ₂) (basis.representation χ₃) δ₁ δ₂ δ₃ hδ₁
    hδ₂ hδ₃ (by rw [h₁t]; push_cast; ring) (by rw [h₂t]; push_cast; ring)
    (by rw [h₃t]; push_cast; ring) (fun v hv0 hv1 => (hrot v hv0 hv1).1)
    (fun v hv0 hv1 => (hrot v hv0 hv1).2.1) (fun v hv0 hv1 => (hrot v hv0 hv1).2.2)
  have hρχ : ρ = χ₁ ∨ ρ = χ₂ ∨ ρ = χ₃ := by
    have hρB := real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal₂ principal
      hprincipal ρ hρr hρodd
    rcases (hodd2 ρ hρB).mp hρodd with h | h
    · exact absurd h hρo
    · exact h
  obtain ⟨hne₁, hne₂, hG₁, hG₂⟩ := hOF
  rw [heF, hFcard] at hne₁ hne₂ hG₁ hG₂
  have hdD : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 4 * Nat.card W := by
    rw [← hDcard]
    change _ = Nat.card (Subgroup.centralizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G))
    rw [centralizer_zpowers_sup_zpowers]
  rw [hdD] at hG₁ hG₂
  rw [heF, hFcard] at h₁t h₂t hc₂
  rw [hFcard] at hprod
  rw [show p ^ f = q from rfl] at hne₁ hne₂ hG₁ hG₂ h₁t h₂t hc₂ hprod
  rcases hρχ with rfl | rfl | rfl
  · exact chi_one_column_false he' hδ hδ₁ hA hm5 hm7 hqe hcZ Nat.card_pos.ne' hf₁ ho₁ hsigns
      hsum2 hprod hne₁ hG₁ h₁t h3C
  · exact chi_two_column_false hn he' hδ hδ₂ hA hm5 hWodd hqe hv2 hcZ Nat.card_pos.ne' hf₂ hc₂
      hne₂ hG₂ h₂t h3C
  · exact chi_three_column_false hn hδ hδ₃ hA hWodd hq7 hqodd Nat.card_pos.ne' hfac hv2 hcZ ho₃
      hc₃ h₃t h3C

end CFSG.BrauerLinearThree
