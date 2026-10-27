module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

abbrev scalarSquareField (A : Module.End K V) : Subalgebra K (Module.End K V) :=
  Algebra.adjoin K {A}

variable {A : Module.End K V} {d : K}

theorem smul_add_smul_mem (a b : K) : a • (1 : Module.End K V) + b • A ∈ scalarSquareField A :=
  add_mem (Subalgebra.smul_mem _ (one_mem _) a)
    (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton A)) b)

theorem smul_add_smul_mul (hAA : A * A = d • 1) (a b c e : K) :
    (a • (1 : Module.End K V) + b • A) * (c • 1 + e • A) =
      (a * c + b * e * d) • 1 + (a * e + b * c) • A := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hAA, smul_smul]
  rw [add_smul, add_smul]
  abel

theorem mem_scalarSquareField_iff (hAA : A * A = d • 1) {x : Module.End K V} :
    x ∈ scalarSquareField A ↔ ∃ a b : K, x = a • 1 + b • A := by
  refine ⟨fun hx => ?_, fun ⟨a, b, hx⟩ => hx ▸ smul_add_smul_mem a b⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx, zero_smul, zero_add, one_smul]⟩
  | algebraMap r =>
    exact ⟨r, 0, by rw [zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by rw [add_smul, add_smul]; abel⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a * c + b * e * d, a * e + b * c, smul_add_smul_mul hAA a b c e⟩

theorem smul_add_smul_inj [Nontrivial V] (hA : ∀ c : K, A ≠ c • 1) {a b a' b' : K}
    (h : a • (1 : Module.End K V) + b • A = a' • 1 + b' • A) : a = a' ∧ b = b' := by
  have hbb : b = b' := by
    by_contra hne
    have hne' : b - b' ≠ 0 := sub_ne_zero.mpr hne
    refine hA ((b - b')⁻¹ * (a' - a)) ?_
    have h1 : (b - b') • A = (a' - a) • (1 : Module.End K V) := by
      rw [sub_smul, sub_smul]
      linear_combination (norm := module) h
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hne', one_smul]
  subst hbb
  refine ⟨?_, rfl⟩
  have h1 : (a - a') • (1 : Module.End K V) = 0 := by
    rw [sub_smul]
    linear_combination (norm := module) h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h2 := congrArg (fun φ : Module.End K V => φ v) h1
  simp only [LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply] at h2
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv)

theorem isField_scalarSquareField [Nontrivial V] (hAA : A * A = d • 1)
    (hd : ∀ l : K, l ^ 2 ≠ d) : IsField (scalarSquareField A) := by
  refine ⟨⟨0, 1, fun h0 => ?_⟩, fun {x y} => mul_comm x y, fun {x} hx => ?_⟩
  · have h1 := congrArg (fun z : scalarSquareField A => (z : Module.End K V)) h0
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 := congrArg (fun φ : Module.End K V => φ v) h1
    simp only [ZeroMemClass.coe_zero, OneMemClass.coe_one, LinearMap.zero_apply,
      Module.End.one_apply] at h2
    exact hv h2.symm
  · obtain ⟨a, b, hab⟩ := (mem_scalarSquareField_iff hAA).mp x.2
    have hn : a ^ 2 - d * b ^ 2 ≠ 0 := by
      intro h0
      by_cases hb : b = 0
      · subst hb
        have ha : a = 0 := by
          have : a ^ 2 = 0 := by linear_combination h0
          exact pow_eq_zero_iff (two_ne_zero) |>.mp this
        subst ha
        exact hx (Subtype.ext (by rw [hab, zero_smul, zero_smul, add_zero]; rfl))
      · exact hd (a / b) (by field_simp; linear_combination h0)
    refine ⟨⟨(a / (a ^ 2 - d * b ^ 2)) • 1 + (-b / (a ^ 2 - d * b ^ 2)) • A,
      smul_add_smul_mem _ _⟩, Subtype.ext ?_⟩
    change (x : Module.End K V) * _ = 1
    rw [hab, smul_add_smul_mul hAA]
    have e1 : a * (a / (a ^ 2 - d * b ^ 2)) + b * (-b / (a ^ 2 - d * b ^ 2)) * d = 1 := by
      field_simp
      ring
    have e2 : a * (-b / (a ^ 2 - d * b ^ 2)) + b * (a / (a ^ 2 - d * b ^ 2)) = 0 := by
      field_simp
      ring
    rw [e1, e2, one_smul, zero_smul, add_zero]

theorem card_scalarSquareField [Nontrivial V] (hA : ∀ c : K, A ≠ c • 1) (hAA : A * A = d • 1) :
    Nat.card (scalarSquareField A) = Nat.card K ^ 2 := by
  have hbij : Function.Bijective fun ab : K × K =>
      (⟨ab.1 • 1 + ab.2 • A, smul_add_smul_mem _ _⟩ : scalarSquareField A) := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · obtain ⟨h1, h2⟩ := smul_add_smul_inj hA (congrArg Subtype.val hxy)
      exact Prod.ext h1 h2
    · obtain ⟨a, b, hab⟩ := (mem_scalarSquareField_iff hAA).mp z.2
      exact ⟨(a, b), Subtype.ext hab.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, pow_two]

theorem charP_scalarSquareField [Nontrivial V] {ℓ : ℕ} [CharP K ℓ] :
    CharP (scalarSquareField A) ℓ :=
  charP_of_injective_algebraMap (algebraMap K (scalarSquareField A)).injective ℓ

theorem pow_card_eq_neg [Fintype K] (h2 : ringChar K ≠ 2) (hAA : A * A = d • 1) (hd0 : d ≠ 0)
    (hd : ∀ l : K, l ^ 2 ≠ d) : A ^ Fintype.card K = -A := by
  have hodd : Odd (Fintype.card K) := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two h2)
  obtain ⟨m, hm⟩ := hodd
  have hdm : d ^ (Fintype.card K / 2) = -1 := by
    rcases FiniteField.pow_dichotomy h2 hd0 with h1 | h1
    · exfalso
      obtain ⟨r, hr⟩ := (FiniteField.isSquare_iff h2 hd0).mpr h1
      exact hd r (by rw [pow_two, hr])
    · exact h1
  have hm2 : Fintype.card K / 2 = m := by omega
  rw [hm2] at hdm
  rw [hm, pow_succ, pow_mul, pow_two, hAA, smul_pow, one_pow, hdm, neg_one_smul, neg_mul,
    one_mul]

theorem pow_card_scalarSquare [Nontrivial V] [Fintype K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {f : ℕ} (hK : Fintype.card K = ℓ ^ f) (h2 : ringChar K ≠ 2) (hAA : A * A = d • 1)
    (hd0 : d ≠ 0) (hd : ∀ l : K, l ^ 2 ≠ d) (a b : K) :
    (⟨a • 1 + b • A, smul_add_smul_mem a b⟩ : scalarSquareField A) ^ (ℓ ^ f) =
      ⟨a • 1 - b • A, by rw [sub_eq_add_neg, ← neg_smul]; exact smul_add_smul_mem a (-b)⟩ := by
  have := charP_scalarSquareField (A := A) (ℓ := ℓ)
  have e : (⟨a • 1 + b • A, smul_add_smul_mem a b⟩ : scalarSquareField A) =
      ⟨a • 1, Subalgebra.smul_mem _ (one_mem _) a⟩ +
        ⟨b • A, Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton A)) b⟩ := rfl
  rw [e, add_pow_char_pow]
  apply Subtype.ext
  change (a • (1 : Module.End K V)) ^ (ℓ ^ f) + (b • A) ^ (ℓ ^ f) = a • 1 - b • A
  rw [smul_pow, smul_pow, one_pow, ← hK, FiniteField.pow_card, FiniteField.pow_card,
    pow_card_eq_neg h2 hAA hd0 hd, smul_neg, ← sub_eq_add_neg]

theorem finrank_scalarSquareField [Finite K] [FiniteDimensional K V] [Nontrivial V]
    (hA : ∀ c : K, A ≠ c • 1) (hAA : A * A = d • 1) (hd : ∀ l : K, l ^ 2 ≠ d) {r : ℕ}
    (hdim : finrank K V = 2 * r) : finrank (scalarSquareField A) V = r := by
  have hF := isField_scalarSquareField hAA hd
  let _ : Field (scalarSquareField A) := hF.toField
  have : Finite V := Module.finite_of_finite K
  have : Module.Finite (scalarSquareField A) V := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := scalarSquareField A) (V := V)
  have h3 := Module.natCard_eq_pow_finrank (K := K) (V := V)
  rw [card_scalarSquareField hA hAA, ← pow_mul] at h1
  rw [hdim] at h3
  have h4 : 2 ≤ Nat.card K := Finite.one_lt_card
  have h5 := Nat.pow_right_injective h4 (h1.symm.trans h3)
  omega

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
