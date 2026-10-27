module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldU
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Open TauCeti CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Curtis.Coordinator

@[expose] def UnitaryRestSlice : Prop :=
  ∀ (ℓ f n : ℕ) (F : Type) [Field F] (h : UnitaryFieldData ℓ f F) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))),
    β ^ 3 = 1 →
    ((primeFormFieldFactor h isPrimeFormGram_one hn hne β = 1 ∧
        (n = 3 ∨ (ℓ ^ f = 2 ∧ n < 10))) ∨ (n = 3 ∧ ℓ ^ (f / 3) = 2)) →
    (∀ k, β ≠ MulAut.conj k) →
    (∀ D : Subgroup (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)),
      (∀ x ∈ D, β x = x) → ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D) →
    (∀ Q : Subgroup (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)),
      (∀ x ∈ Q, β x = x) → IsPGroup 3 Q → Nat.card Q ≤ 9) →
    (∃ T : Subgroup (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)),
      (∀ x ∈ T, β x = x) ∧ IsElemAbelian 3 T ∧ Nat.card T = 9) →
    3 ^ 5 ∣ Nat.card (MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))) →
    False

theorem e27LieOuterAutAt_twistedA_of_rest (hrest : UnitaryRestSlice) :
    E27LieOuterAutAt (fun i => ∃ r q, i = .twistedA r q) := by
  rintro K _ _ d ⟨r, q, hd⟩ ⟨e⟩ hAut u hu3 hout hfixD hQ hT
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .twistedA r q := hd
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hn : 3 ≤ r + 1 := by have := hrange.1; omega
  obtain ⟨⟨hℓ, hf, -, hne⟩, F, _, _, hFcard, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have hne' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hC1 : IsPrimeFormGram (1 : GL (Fin (r + 1)) F) := isPrimeFormGram_one
  obtain ⟨θ⟩ : Nonempty (K ≃* primeFormP h ((1 : GL (Fin (r + 1)) F) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) F)) :=
    ⟨(e₁.trans (unitaryPSUEquiv h (by omega)).symm).trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization h hC1 hn hne').1).symm⟩
  set β := MulAut.congr θ u with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hu3, map_one]
  have hout' : ∀ k, β ≠ MulAut.conj k := by
    intro k hk
    apply hout (θ.symm k)
    apply (MulAut.congr θ).injective
    rw [← hβ, hk]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hAut' : 3 ^ 5 ∣ Nat.card (MulAut (primeFormP h ((1 : GL (Fin (r + 1)) F) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) F))) := (Nat.card_congr (MulAut.congr θ).toEquiv) ▸ hAut
  have hrest' := fun hc =>
    hrest q.p q.exponent (r + 1) F h hn hne' β hβ3 hc hout' (noPerfect_of_congr θ u hfixD)
      (card_le_nine_of_congr θ u hQ) (exists_elemAbelian_of_congr θ u hT) hAut'
  by_cases hσ1 : primeFormFieldFactor h isPrimeFormGram_one hn hne' β = 1
  ·
    have hD : β ∈ primeFormD h ((1 : GL (Fin (r + 1)) F) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
      rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn hne']
      exact hσ1
    by_cases hg : 3 ∣ Nat.gcd (r + 1) (q.p ^ q.exponent + 1)
    · have hℓ3 : q.p ≠ 3 := by
        intro h3
        have h3' : 3 ∣ q.p ^ q.exponent + 1 := hg.trans (Nat.gcd_dvd_right _ _)
        rw [h3] at h3'
        have : 3 ∣ 3 ^ q.exponent := dvd_pow_self 3 (by omega : q.exponent ≠ 0)
        omega
      have hq3 : q.p ^ q.exponent ≠ 3 := fun h3 =>
        hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
          (h3 ▸ dvd_pow_self q.p (by omega : q.exponent ≠ 0)))
      have hq2 : 2 ≤ q.p ^ q.exponent := (Nat.one_lt_pow (by omega : q.exponent ≠ 0) hℓ.one_lt)
      by_cases hqn : (4 ≤ q.p ^ q.exponent ∧ 4 ≤ r + 1) ∨ (q.p ^ q.exponent = 2 ∧ 10 ≤ r + 1)
      · obtain ⟨y, hy⟩ := hD
        obtain ⟨c, hc⟩ := exists_scalar_of_conjHom_pow_three hn hne' y (hy ▸ hβ3)
        obtain ⟨R, hRfix, hRperf, hR3⟩ := exists_perfect_three_dvd_autFix_of_diag hℓ3 hqn y c hc
        obtain ⟨R', hfix', hperf', h3'⟩ := exists_fixed_perfect_of_congr θ u
          (fun x hx => by have := hRfix hx; rwa [mem_autFix, hy] at this) hRperf hR3
        exact hfixD R' hfix' hperf' h3'
      · refine hrest' (Or.inl ⟨hσ1, ?_⟩)
        omega
    · obtain ⟨k, hk⟩ := CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_primeFormD h hn
        hne' Nat.prime_three hg hD hβ3
      exact hout' k hk.symm
  by_cases hq0 : r + 1 = 3 ∧ q.p ^ (q.exponent / 3) = 2
  · exact hrest' (Or.inr hq0)
  obtain ⟨D, hfix, hperf, h3⟩ := exists_fixed_perfect_three_PSU h hn hne' hq0 β hβ3 hσ1
  obtain ⟨D', hfix', hperf', h3'⟩ := exists_fixed_perfect_of_congr θ u hfix hperf h3
  exact hfixD D' hfix' hperf' h3'

end CFSG.HardMathSupport.Malle.E27Lie
