module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.DiagCube
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent

public section

open CFSG.HardMathSupport.Lang.Proving

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem neg_one_pow_of_card_eq_sq {L : Type*} [Field L] [Finite L] {q0 : ℕ} (hL : Nat.card L = q0 ^ 2) {m : ℕ}
    (hm : m = q0 - 1 ∨ m = q0 + 1) (hq : 2 ≤ q0) : (-1 : Lˣ) ^ m = 1 := by
  by_cases he : Even q0
  · have hc : ringChar L = 2 := by
      have := Fintype.ofFinite L
      rw [FiniteField.even_card_iff_char_two]
      have h1 : Even (Fintype.card L) := by
        rw [← Nat.card_eq_fintype_card, hL]; exact Nat.even_pow.2 ⟨he, by norm_num⟩
      exact Nat.even_iff.1 h1
    have : (-1 : Lˣ) = 1 := by
      ext
      have := Fact.mk (Nat.prime_two)
      have : CharP L 2 := hc ▸ ringChar.charP L
      simp [CharTwo.neg_eq]
    rw [this, one_pow]
  · have : Even m := by
      rcases hm with rfl | rfl
      · exact (Nat.even_sub (by omega)).2 (by simp [he])
      · exact (Nat.even_add_one).2 he
    exact this.neg_one_pow

theorem exists_norm_data {L : Type*} [Field L] [Finite L] {q0 : ℕ} (hL : Nat.card L = q0 ^ 2)
    (h3 : 3 ∣ q0 + 1) :
    ∃ ε ζ τ : L, ε ^ (q0 + 1) = -1 ∧ ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ τ ≠ 0 ∧ τ ^ q0 = -τ := by
  have hq : 2 ≤ q0 := by omega
  have hcard : Nat.card Lˣ = (q0 + 1) * (q0 - 1) := by
    rw [Nat.card_units, hL]
    obtain ⟨r, rfl⟩ : ∃ r, q0 = r + 2 := ⟨q0 - 2, by omega⟩
    simp only [show r + 2 - 1 = r + 1 by omega, show r + 2 + 1 = r + 3 by omega]
    have : (r + 2) ^ 2 = (r + 3) * (r + 1) + 1 := by ring
    omega
  have hcard' : Nat.card Lˣ = (q0 - 1) * (q0 + 1) := by rw [hcard, mul_comm]
  obtain ⟨ε, hε⟩ := (mem_range_pow_iff_of_card_eq_mul hcard (by omega) (-1 : Lˣ)).2
    (neg_one_pow_of_card_eq_sq hL (Or.inl rfl) hq)
  obtain ⟨t, ht⟩ := (mem_range_pow_iff_of_card_eq_mul hcard' (by omega) (-1 : Lˣ)).2
    (neg_one_pow_of_card_eq_sq hL (Or.inr rfl) hq)
  have h3c : 3 ∣ Nat.card Lˣ := by rw [hcard]; exact Dvd.dvd.mul_right h3 _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3c
  refine ⟨(ε : L), (z : L), (t : L), ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg (fun u : Lˣ => (u : L)) hε
    simpa using this
  · have := pow_orderOf_eq_one z
    rw [hz] at this
    have := congrArg (fun u : Lˣ => (u : L)) this
    simpa using this
  · intro h1
    have : z = 1 := Units.ext h1
    rw [this, orderOf_one] at hz
    omega
  · exact t.ne_zero
  · have h1 : (t : L) ^ (q0 - 1) = -1 := by
      have := congrArg (fun u : Lˣ => (u : L)) ht
      simpa using this
    have : (t : L) ^ q0 = (t : L) ^ (q0 - 1) * t := by
      rw [← pow_succ]; congr 1; omega
    rw [this, h1]; ring

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem map_planeVec (σ : K ≃+* K) (i j : Fin n) (t : K) (k : Fin n) :
    σ (planeVec i j t k) = planeVec i j (σ t) k := by
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [planeVec, Pi.single_apply, hki, hkj, apply_ite σ]

theorem cube_mod_three (q0 : ℕ) (h : 3 ∣ q0 ^ 3 + 1) : 3 ∣ q0 + 1 := by
  have key : ∀ x : ZMod 3, x ^ 3 + 1 = 0 → x + 1 = 0 := by decide
  have h1 := (ZMod.natCast_eq_zero_iff _ _).2 h
  have h2 := key (q0 : ZMod 3) (by exact_mod_cast h1)
  exact (ZMod.natCast_eq_zero_iff _ _).1 (by exact_mod_cast h2)

theorem hasFixedThreePair_of_fieldFactor_ne_one (h : UnitaryFieldData p f K)
    (h3 : 3 ∣ p ^ f + 1) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    (a : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (ha3 : a ^ 3 = 1)
    (hσ : primeFormFieldFactor h (isPrimeFormGram_idGL (n := n)) hn hq a ≠ 1) :
    HasFixedThreePair a := by
  classical
  have hp3 : p ≠ 3 := prime_ne_three_of_dvd h.prime h.one_le h3
  have hfin := h.finite
  have hchar := h.charP
  set ψ := primeFormFieldFactor h (isPrimeFormGram_idGL (n := n)) hn hq with hψ
  set σ : K ≃+* K := ψ a with hσdef
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, ha3, map_one]
  have hoσ : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  have ha1 : a ≠ 1 := fun h1 => hσ (by rw [hσdef, h1, map_one])
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  obtain ⟨hf3, hcard, hbar, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq Nat.prime_three
      (by norm_num) (Ne.symm hp3) a hoa σ rfl hoσ
  refine HasFixedThreePair.of_conj
    (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M) ?_
  rw [hM]
  change HasFixedThreePair (primeFormFieldHom h (isPrimeFormGram_idGL (n := n)) σ)
  obtain ⟨f', hf'⟩ := hf3
  set q0 : ℕ := p ^ (f / 3) with hq0
  have hf'' : f / 3 = f' := by omega
  have hpq : p ^ f = q0 ^ 3 := by rw [hq0, hf'', hf', ← pow_mul, mul_comm]
  have h3q : 3 ∣ q0 + 1 := cube_mod_three q0 (hpq ▸ h3)
  set K0 := CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ with hK0
  have : Finite K0 := Subtype.finite
  obtain ⟨ε, ζ, τ, hε, hζ3, hζ1, hτ0, hτq⟩ := exists_norm_data (L := K0) hcard h3q
  have hfix : ∀ x : K0, σ (x : K) = x := fun x => RingHom.mem_eqLocusField.mp x.2
  have hbarK : ∀ x : K0, h.bar (x : K) = (x : K) ^ q0 := fun x => hbar x (hfix x)
  have hε' : h.bar (ε : K) * (ε : K) = -1 := by
    rw [hbarK, ← pow_succ]
    have := congrArg (fun u : K0 => (u : K)) hε
    simpa using this
  have hζ' : h.bar (ζ : K) * (ζ : K) = 1 := by
    rw [hbarK, ← pow_succ]
    obtain ⟨k, hk⟩ := h3q
    have := congrArg (fun u : K0 => (u : K)) hζ3
    have h33 : (ζ : K) ^ 3 = 1 := by simpa using this
    rw [hk, pow_mul, h33, one_pow]
  have hζ1' : (ζ : K) ≠ 1 := fun h1 => hζ1 (Subtype.ext h1)
  have hτ' : h.bar (τ : K) = -(τ : K) := by
    rw [hbarK]
    have := congrArg (fun u : K0 => (u : K)) hτq
    simpa using this
  have hτ0' : (τ : K) ≠ 0 := fun h1 => hτ0 (Subtype.ext h1)
  have h3K : (3 : K) ≠ 0 := by
    intro h0
    have : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 this)
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := fun h1 => by simpa [i, j] using congrArg Fin.val h1
  set ε1 : K := (ε : K) with hε1
  set ζ1 : K := (ζ : K) with hζ1def
  set τ1 : K := (τ : K) with hτ1
  have e00 : hpair h (planeVec i j ε1) (planeVec i j ε1) = 0 := by
    rw [hpair_planeVec h hij, hε']; ring
  have e11 : hpair h (planeVec i j (ε1 * ζ1)) (planeVec i j (ε1 * ζ1)) = 0 := by
    rw [hpair_planeVec h hij, map_mul]
    linear_combination (h.bar ζ1 * ζ1) * hε' - hζ'
  set c : K := hpair h (planeVec i j ε1) (planeVec i j (ε1 * ζ1)) with hcdef
  have hc : c = 1 - ζ1 := by
    rw [hcdef, hpair_planeVec h hij]
    linear_combination ζ1 * hε'
  have hc0 : c ≠ 0 := by
    rw [hc]; exact sub_ne_zero.2 (Ne.symm hζ1')
  have hbc : h.bar c ≠ 0 := (map_ne_zero h.bar).2 hc0
  have hN : c * h.bar c ≠ 0 := mul_ne_zero hc0 hbc
  have hbN : h.bar (c * h.bar c) = c * h.bar c := by
    rw [map_mul, h.bar_bar, mul_comm]
  set β' : K := -3 / (τ1 * (c * h.bar c)) with hβ'
  have hβτ : τ1 + h.bar τ1 = 0 := by rw [hτ']; ring
  have hβ'1 : β' + h.bar β' = 0 := by
    have hb3 : h.bar (3 : K) = 3 := map_ofNat h.bar 3
    rw [hβ', map_div₀, map_neg, hb3, map_mul, hτ', hbN]
    field_simp
    ring
  have hββ : τ1 * β' * (c * h.bar c) = -3 := by
    rw [hβ']
    field_simp
  have hσε : σ ε1 = ε1 := hfix ε
  have hσζ : σ ζ1 = ζ1 := hfix ζ
  have hσc : σ c = c := by rw [hc, map_sub, map_one, hσζ]
  have hσbc : σ (h.bar c) = h.bar c := by
    rw [map_bar_comm h σ c, hσc]
  have hσβ' : σ β' = β' := by
    have hσ3 : σ (3 : K) = 3 := map_ofNat σ 3
    rw [hβ', map_div₀, map_neg, hσ3, map_mul, map_mul, hfix τ, hσc, hσbc]
  have hvec1 : (fun k => σ (planeVec i j ε1 k)) = planeVec i j ε1 := by
    funext k; rw [map_planeVec, hσε]
  have hvec2 : (fun k => σ (planeVec i j (ε1 * ζ1) k)) = planeVec i j (ε1 * ζ1) := by
    funext k; rw [map_planeVec, map_mul, hσε, hσζ]
  have hx := transvGL_mem_gramSU h e00 hβτ
  have hy := transvGL_mem_gramSU h e11 hβ'1
  let x : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, hx⟩
  let y : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, hy⟩
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes h.prime Nat.prime_three).2 hp3
  have hxp : ((x : GL (Fin n) K)) ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val]; exact transvMat_pow_char e00 τ1)
  have hyp : ((y : GL (Fin n) K)) ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val]; exact transvMat_pow_char e11 β')
  refine ⟨(x : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
    (y : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), ?_, ?_, ?_, ?_, ?_⟩
  · refine fixed_fieldHom_of_map_eq h σ x ?_
    show (transvMat h (planeVec i j ε1) τ1).map σ = _
    rw [map_transvMat σ (map_bar_comm h σ), hvec1, hfix τ]
    rfl
  · refine fixed_fieldHom_of_map_eq h σ y ?_
    show (transvMat h (planeVec i j (ε1 * ζ1)) β').map σ = _
    rw [map_transvMat σ (map_bar_comm h σ), hvec2, hσβ']
    rfl
  · exact Nat.Coprime.coprime_dvd_left (orderOf_mk_dvd h x p hxp) hcop
  · exact Nat.Coprime.coprime_dvd_left (orderOf_mk_dvd h y p hyp) hcop
  · rw [← QuotientGroup.mk_mul]
    refine orderOf_mk_eq_three h (x * y) ?_ ?_
    · apply Units.ext
      exact (Units.val_pow_eq_pow_val _ _).trans (transvMat_pair_cube e00 e11 hc0 hββ)
    · intro s
      exact transvMat_pair_not_scalar e00 e11 hc0 hββ h3K hn s

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
