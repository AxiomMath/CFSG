module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalIndexU
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldU38

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.Open TauCeti CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Curtis.Coordinator

@[expose] def UnitaryTwoDiagSlice : Prop :=
  ∀ {ℓ f n : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData ℓ f F), ℓ ^ f = 2 →
    (n = 6 ∨ n = 9) → ∀ (y : primeFormUnitary h (idGram F n)) (c : Fˣ),
    (y : GL (Fin n) F) ^ 3 = GeneralLinearGroup.scalar (Fin n) c →
    (∃ R : Subgroup (primeFormP h (idGram F n)),
      (∀ x ∈ R, primeFormConjHom h (idGram F n) y x = x) ∧ ⁅R, R⁆ = R ∧ 3 ∣ Nat.card R) ∨
    (∃ Q : Subgroup (primeFormP h (idGram F n)),
      (∀ x ∈ Q, primeFormConjHom h (idGram F n) y x = x) ∧ IsPGroup 3 Q ∧ 27 ≤ Nat.card Q)

theorem unitaryRestSlice_of_diag (h3 : ∀ {ℓ f : ℕ} {F : Type} [Field F] [Finite F] (h :
    UnitaryFieldData ℓ f F), ℓ ≠ 3 → 4 ≤ ℓ ^ f → 3 ∣ ℓ ^ f + 1 → ∀ (y : primeFormUnitary h (idGram F
    3)) (c : Fˣ), (y : GL (Fin 3) F) ^ 3 = GeneralLinearGroup.scalar (Fin 3) c → (∀ k,
    primeFormConjHom h (idGram F 3) y ≠ MulAut.conj k) → (∀ D : Subgroup (primeFormP h (idGram F
    3)), (∀ x ∈ D, primeFormConjHom h (idGram F 3) y x = x) → ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D) → (∃ T
    : Subgroup (primeFormP h (idGram F 3)), (∀ x ∈ T, primeFormConjHom h (idGram F 3) y x = x) ∧
    IsElemAbelian 3 T ∧ Nat.card T = 9) → False) (h2 : UnitaryTwoDiagSlice) :
    UnitaryRestSlice := by
  unfold UnitaryTwoDiagSlice at h2
  intro ℓ f n F _ h hn hne β hβ3 hdis hout ha hb hT _
  have hfin := h.finite
  have hℓ := h.prime
  by_cases hσ1 : primeFormFieldFactor h isPrimeFormGram_one hn hne β = 1
  · have hD : β ∈ primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn hne]
      exact hσ1
    have hdiag : n = 3 ∨ (ℓ ^ f = 2 ∧ n < 10) := by
      rcases hdis with ⟨-, h'⟩ | ⟨h3', -⟩
      · exact h'
      · exact Or.inl h3'
    by_cases hg : 3 ∣ Nat.gcd n (ℓ ^ f + 1)
    · have hℓ3 : ℓ ≠ 3 := by
        intro h3'
        have h3'' : 3 ∣ ℓ ^ f + 1 := hg.trans (Nat.gcd_dvd_right _ _)
        rw [h3'] at h3''
        have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
        omega
      obtain ⟨y, hy⟩ := hD
      obtain ⟨c, hc⟩ := exists_scalar_of_conjHom_pow_three hn hne y (hy ▸ hβ3)
      subst hy
      rcases hdiag with rfl | ⟨hq2, hn10⟩
      · have hq2' : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by have := h.one_le; omega) hℓ.one_lt
        have hq3 : ℓ ^ f ≠ 3 := fun h3' =>
          hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
            (h3' ▸ dvd_pow_self ℓ (by have := h.one_le; omega)))
        have hq4 : 4 ≤ ℓ ^ f := by
          have : ℓ ^ f ≠ 2 := fun h2' => hne ⟨rfl, h2'⟩
          omega
        exact h3 h hℓ3 hq4 (Nat.dvd_gcd_iff.1 hg).2 y c hc hout ha hT
      · have h3n : 3 ∣ n := (Nat.dvd_gcd_iff.1 hg).1
        have hn69 : n = 6 ∨ n = 9 := by
          have : n ≠ 3 := fun h3' => hne ⟨h3', hq2⟩
          omega
        rcases h2 h hq2 hn69 y c hc with ⟨R, hRf, hRp, hR3⟩ | ⟨Q, hQf, hQp, hQ27⟩
        · exact ha R hRf hRp hR3
        · exact absurd (le_trans hQ27 (hb Q hQf hQp)) (by norm_num)
    · obtain ⟨k, hk⟩ := CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_primeFormD h hn
        hne Nat.prime_three hg hD hβ3
      exact hout k hk.symm
  · obtain ⟨rfl, hq0⟩ : n = 3 ∧ ℓ ^ (f / 3) = 2 := by
      rcases hdis with ⟨h1, -⟩ | h'
      · exact absurd h1 hσ1
      · exact h'
    exact unitary_three_eight_false h hn hne hq0 β hβ3 hσ1 hb

end CFSG.HardMathSupport.Malle.E27Lie
