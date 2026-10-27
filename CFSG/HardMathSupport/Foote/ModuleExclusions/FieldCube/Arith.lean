module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Finite F]

@[expose] def fixF (σ : F ≃+* F) : Subfield F := FixedPoints.subfield (Subgroup.zpowers σ) F

theorem mem_fixF {σ : F ≃+* F} {x : F} : x ∈ fixF σ ↔ σ x = x :=
  ⟨fun h => h ⟨σ, Subgroup.mem_zpowers σ⟩, mem_fixedPoints_subfield_of_apply_eq σ x⟩

theorem finrank_fixF {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    Module.finrank (fixF σ) F = 3 := by
  classical
  have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  have h := FixedPoints.finrank_eq_card (Subgroup.zpowers σ) F
  rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, hσ] at h
  exact h

theorem natCard_eq_pow_three {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    Nat.card F = Nat.card (fixF σ) ^ 3 := by
  have := Module.natCard_eq_pow_finrank (K := fixF σ) (V := F)
  rwa [finrank_fixF hσ] at this

theorem three_dvd_sub_one_of_pow_three {q₀ : ℕ} (hq : 1 ≤ q₀) (h : 3 ∣ q₀ ^ 3 - 1) :
    3 ∣ q₀ - 1 := by
  have h1 : 1 ≤ q₀ ^ 3 := Nat.one_le_pow _ _ hq
  have h2 : ((q₀ ^ 3 - 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  have h3 : ∀ x : ZMod 3, x ^ 3 = x := by decide
  rw [Nat.cast_sub h1, Nat.cast_pow, h3, Nat.cast_one] at h2
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, Nat.cast_one]
  exact h2

theorem exists_threePrime_not_fixed {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (h3 : 3 ∣ Nat.card F - 1) : ∃ u : F, u ≠ 0 ∧ (orderOf u).Coprime 3 ∧ σ u ≠ u := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set q₀ := Nat.card (fixF σ) with hq₀
  have hq : Nat.card F = q₀ ^ 3 := natCard_eq_pow_three hσ
  have hq₀1 : 1 < q₀ := by
    have : Finite (fixF σ) := inferInstance
    exact Finite.one_lt_card_iff_nontrivial.2 inferInstance
  rw [hq] at h3
  have h3' : 3 ∣ q₀ - 1 := three_dvd_sub_one_of_pow_three hq₀1.le h3
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hordγ : orderOf γ = q₀ ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hq]
  set n := q₀ ^ 3 - 1 with hn
  have hn0 : n ≠ 0 := by
    have : 1 < q₀ ^ 3 := Nat.one_lt_pow (by norm_num) hq₀1
    omega
  set a := n.factorization 3 with ha
  have hdvd : 3 ^ a ∣ n := Nat.ordProj_dvd n 3
  set u : Fˣ := γ ^ (3 ^ a) with hu
  have hordu : orderOf u = n / 3 ^ a := by
    rw [hu, orderOf_pow_of_dvd (by positivity) (by rwa [hordγ]), hordγ]
  refine ⟨(u : F), u.ne_zero, ?_, ?_⟩
  · rw [orderOf_units, hordu]
    exact (Nat.coprime_ordCompl Nat.prime_three hn0).symm
  · intro hfix
    have hmem : (u : F) ∈ fixF σ := mem_fixF.2 hfix
    have hu0 : (⟨(u : F), hmem⟩ : fixF σ) ≠ 0 := fun h => u.ne_zero (congrArg Subtype.val h)
    have hpow : (u : F) ^ (q₀ - 1) = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one (⟨(u : F), hmem⟩ : fixF σ) hu0
      have h' := congrArg Subtype.val this
      simpa [hq₀] using h'
    have hdiv : n / 3 ^ a ∣ q₀ - 1 := by
      rw [← hordu, ← orderOf_units]
      exact orderOf_dvd_of_pow_eq_one hpow
    have hm : n / 3 ^ a ≤ q₀ - 1 := Nat.le_of_dvd (by omega) hdiv
    have hlte : a = (q₀ - 1).factorization 3 + 1 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h3q : ¬ 3 ∣ q₀ := by
        intro h
        have : 3 ∣ 1 := by
          have := (Nat.dvd_sub h h3')
          simp [Nat.sub_sub_self (by omega : 1 ≤ q₀)] at this
        omega
      have := padicValNat.pow_sub_pow (p := 3) (x := q₀) (y := 1) ⟨1, rfl⟩ hq₀1
        (by simpa using h3') h3q (n := 3) (by norm_num)
      rw [one_pow] at this
      rw [ha, Nat.factorization_def n Nat.prime_three,
        Nat.factorization_def (q₀ - 1) Nat.prime_three, hn, this, padicValNat_self]
    have h3v : 3 ^ (q₀ - 1).factorization 3 ≤ q₀ - 1 := Nat.ordProj_le 3 (by omega)
    have hpa : 3 ^ a ≤ 3 * (q₀ - 1) := by
      rw [hlte, pow_succ]; linarith
    have hmul : n = n / 3 ^ a * 3 ^ a := (Nat.div_mul_cancel hdvd).symm
    have hle : n ≤ (q₀ - 1) * (3 * (q₀ - 1)) := by
      calc n = n / 3 ^ a * 3 ^ a := hmul
        _ ≤ (q₀ - 1) * (3 * (q₀ - 1)) := Nat.mul_le_mul hm hpa
    obtain ⟨r, hr⟩ : ∃ r, q₀ = r + 1 := ⟨q₀ - 1, by omega⟩
    have hr1 : 1 ≤ r := by omega
    rw [hn, hr] at hle
    have e1 : (r + 1) ^ 3 - 1 = r ^ 3 + 3 * r ^ 2 + 3 * r := by
      have : (r + 1) ^ 3 = r ^ 3 + 3 * r ^ 2 + 3 * r + 1 := by ring
      omega
    rw [e1, Nat.add_sub_cancel] at hle
    nlinarith

theorem span_threePrime_eq_top {σ : F ≃+* F} (hσ : orderOf σ = 3) (h3 : 3 ∣ Nat.card F - 1) :
    Submodule.span (fixF σ) {u : F | u ≠ 0 ∧ (orderOf u).Coprime 3} = ⊤ := by
  classical
  obtain ⟨u, hu0, hu3, hux⟩ := exists_threePrime_not_fixed hσ h3
  have hfr : Module.finrank (fixF σ) F = 3 := finrank_fixF hσ
  have hint : IsIntegral (fixF σ) u := Algebra.IsIntegral.isIntegral u
  have hdvd : (minpoly (fixF σ) u).natDegree ∣ 3 := hfr ▸ minpoly.degree_dvd hint
  have hne1 : (minpoly (fixF σ) u).natDegree ≠ 1 := by
    intro h
    rw [minpoly.natDegree_eq_one_iff] at h
    obtain ⟨x, hx⟩ := h
    apply hux
    rw [← hx]
    exact mem_fixF.1 x.2
  have hdeg : (minpoly (fixF σ) u).natDegree = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hli := linearIndependent_pow (K := fixF σ) u
  have hli3 : LinearIndependent (fixF σ) (fun i : Fin 3 => u ^ (i : ℕ)) :=
    hli.comp (Fin.cast hdeg.symm) (Fin.cast_injective _)
  have hspan : Submodule.span (fixF σ) (Set.range (fun i : Fin 3 => u ^ (i : ℕ))) = ⊤ :=
    hli3.span_eq_top_of_card_eq_finrank' (by rw [hfr]; simp)
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  refine ⟨pow_ne_zero _ hu0, ?_⟩
  exact Nat.Coprime.coprime_dvd_left (orderOf_pow_dvd (i : ℕ)) hu3

end CFSG.HardMathSupport.Foote.ModuleExclusions
