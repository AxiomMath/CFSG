module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCentralFourierRows
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsSections

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatCentralFourier

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G]

theorem twisted_section_rows_family (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (B : basis.index) {a : G} {m : ℕ}
    (hm : orderOf a = m) (hm2 : ∃ n : ℕ, m = 2 ^ n) (C : ℕ → Subgroup G)
    (hC : ∀ k, C k = Subgroup.centralizer {a ^ k}) (lamG ΦG : G → ℂ)
    (hΦreal : ∀ g, conj (ΦG g) = ΦG g) (ε : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hlocal : ∀ k ∈ Finset.Ico 1 m, ∀ (hk2 : IsPGroup 2 (Subgroup.zpowers (a ^ k)))
      (lb : FiniteIrreducibleCharacterBasis
        (Subgroup.centralizer (Subgroup.zpowers (a ^ k) : Set G))) (ℓ : lb.index),
      (∀ c, (lb.representation ℓ).character c = lamG c) →
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers (a ^ k)) hk2
          (Subgroup.centralizer (Subgroup.zpowers (a ^ k) : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) lb ℓ =
        centralCharacterResidueHom basis ideal B ∧
      ∀ θ, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers (a ^ k)) hk2
          (Subgroup.centralizer (Subgroup.zpowers (a ^ k) : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) lb θ =
        centralCharacterResidueHom basis ideal B →
        θ ∈ coefficientBlock lb (localizedComplexIntegerRing ideal) ℓ)
    (hlabel : ∀ k ∈ Finset.Ico 1 m, ∀ lb : FiniteIrreducibleCharacterBasis (C k),
      ∃ ℓ : lb.index, ∀ c, (lb.representation ℓ).character c = lamG c)
    (hdata : ∀ k ∈ Finset.Ico 1 m, ∀ (lb : FiniteIrreducibleCharacterBasis (C k))
      (ℓ : lb.index), (∀ c, (lb.representation ℓ).character c = lamG c) →
      TwistedRegularIntegralBasisData lb ideal ℓ (fun c => lamG c) (fun c => ΦG c) ε M)
    (hlam0 : ∀ k ∈ Finset.Ico 1 m, ∀ c ∈ C k, lamG c ≠ 0)
    (hindep : ∀ k ∈ Finset.Ico 1 m, ∀ α β : ℂ,
      (∀ y ∈ C k, Odd (orderOf y) → α + β * (1 + ε * ΦG y) = 0) → α = 0 ∧ β = 0)
    (hnonconj : ∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, IsConj (a ^ k) (a ^ h) → k = h)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    ∃ v : basis.index → ℕ → Fin 2 → ℂ,
      (∀ χ, ∀ k ∈ Finset.Ico 1 m, ∀ t, v χ k t ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
      IsTwistedCentralSectionRows basis ideal B a m C lamG ΦG ε v ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        ∀ k ∈ Finset.Ico 1 m, ∀ w : Fin 2 → ℂ, (∀ r ∈ C k, Odd (orderOf r) →
          (basis.representation χ).character (a ^ k * r) =
            lamG r * (w 0 + w 1 * (1 + ε * ΦG r))) → w = v χ k) ∧
      (∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ s t,
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          conj (v χ k s) * v χ h t = if k = h then (M s t : ℂ) else 0) ∧
      ∀ k ∈ Finset.Ico 1 m, ∀ s, ∀ z : G, Odd (orderOf z) →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          v χ k s * conj ((basis.representation χ).character z) = 0 := by
  classical
  obtain ⟨n, rfl⟩ := hm2
  have hord : ∀ k ∈ Finset.Ico 1 (2 ^ n), ∃ r : ℕ, 1 ≤ r ∧ orderOf (a ^ k) = 2 ^ r := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hdvd : orderOf (a ^ k) ∣ 2 ^ n := by
      rw [← hm]
      exact orderOf_pow_dvd k
    obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    refine ⟨r, ?_, hr⟩
    by_contra hr0
    have : r = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hr
    have := orderOf_dvd_of_pow_eq_one hr
    rw [hm] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hgroup : ∀ k ∈ Finset.Ico 1 (2 ^ n), IsPGroup 2 (Subgroup.zpowers (a ^ k)) := by
    intro k hk
    obtain ⟨r, -, hr⟩ := hord k hk
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hr])
  have hrows : ∀ k ∈ Finset.Ico 1 (2 ^ n), ∃ w : basis.index → Fin 2 → ℂ,
      (∀ χ t, w χ t ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        ∀ y ∈ C k, Odd (orderOf y) →
          (basis.representation χ).character (a ^ k * y) =
            lamG y * (w χ 0 + w χ 1 * (1 + ε * ΦG y))) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        ∀ w' : Fin 2 → ℂ, (∀ y ∈ C k, Odd (orderOf y) →
          (basis.representation χ).character (a ^ k * y) =
            lamG y * (w' 0 + w' 1 * (1 + ε * ΦG y))) → w' = w χ) ∧
      (∀ s t, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        conj (w χ s) * w χ t = M s t) ∧
      (∀ g : G, (∀ a' c : G, a' * c = g → Commute a' c → (∃ e : ℕ, orderOf a' = 2 ^ e) →
          Odd (orderOf c) → ¬ IsConj a' (a ^ k)) →
        ∀ s, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          w χ s * conj ((basis.representation χ).character g) = 0) := by
    intro k hk
    obtain ⟨r, hr1, hr⟩ := hord k hk
    obtain ⟨lb⟩ := finiteIrreducibleCharacterBasis_exists (G := C k)
    obtain ⟨ℓ, hℓ⟩ := hlabel k hk lb
    have hdvd : 2 ^ r ∣ 2 ^ n := by
      rw [← hr, ← hm]
      exact orderOf_pow_dvd k
    have hζk := isPrimitiveRoot_pow_div hζ (by positivity) hdvd (by positivity)
    obtain ⟨w, hw1, hw2, hw3, hw4, hw5⟩ := twisted_section_rows basis ideal B hr1 hr
      (hgroup k hk) lamG ΦG ε M (hlocal k hk (hgroup k hk)) (C k)
      (by rw [hC k, ← CFSG.BlockBasics.centralizer_zpowers_eq_centralizer_singleton]) lb ℓ hℓ
      (hdata k hk lb ℓ hℓ) (hlam0 k hk) (hindep k hk) hζk
    refine ⟨w, fun χ t => ?_, hw2, hw3, hw4, hw5⟩
    have hle : Algebra.adjoin ℤ ({ζ ^ (2 ^ n / 2 ^ r)} : Set ℂ) ≤
        Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _
    exact hle (hw1 χ t)
  choose! w hw1 hw2 hw3 hw4 hw5 using hrows
  refine ⟨fun χ k t => w k χ t, fun χ k hk t => hw1 k hk χ t,
    fun χ hχ k hk r hr hodd => hw2 k hk χ hχ r hr hodd,
    fun χ hχ k hk w' hw' => hw3 k hk χ hχ w' hw', ?_, ?_⟩
  ·
    intro k hk h hh s t
    by_cases hkh : k = h
    · subst hkh
      rw [ite_eq_left rfl]
      exact hw4 k hk s t
    · rw [ite_eq_right hkh]
      have hvan : ∀ r ∈ C h, Odd (orderOf r) →
          ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
            w k χ s * conj ((basis.representation χ).character (a ^ h * r)) = 0 := by
        intro r hr hodd
        apply hw5 k hk
        intro a' c hac hcomm ha' hc hconj
        have hrc : Commute (a ^ h) r := by
          have hmem : r ∈ Subgroup.centralizer {a ^ h} := hC h ▸ hr
          rw [Subgroup.mem_centralizer_singleton_iff] at hmem
          exact hmem.symm
        have hpow : ∃ e : ℕ, orderOf (a ^ h) = 2 ^ e := by
          obtain ⟨e, -, he⟩ := hord h hh
          exact ⟨e, he⟩
        have heq := two_part_unique (g := a ^ h * r) rfl hrc hpow hodd hac hcomm ha' hc
        rw [← heq] at hconj
        exact hkh (hnonconj k hk h hh hconj.symm)
      obtain ⟨h0, h1⟩ := hindep h hh
        (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          w k χ s * conj (w h χ 0))
        (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          w k χ s * conj (w h χ 1)) (fun y hy hyodd => by
          have h' := hvan y hy hyodd
          have hexp : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
              w k χ s * conj ((basis.representation χ).character (a ^ h * y)) =
              conj (lamG y) *
                ((∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
                    w k χ s * conj (w h χ 0)) +
                  (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
                    w k χ s * conj (w h χ 1)) * (1 + ε * ΦG y)) := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun χ hχ => ?_
            rw [hw2 h hh χ hχ y hy hyodd]
            simp only [map_mul, map_add, map_one, hΦreal, map_intCast]
            ring
          rw [hexp] at h'
          exact (mul_eq_zero.mp h').resolve_left
            ((map_ne_zero (starRingEnd ℂ)).mpr (hlam0 h hh y hy)))
      have htarget : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          conj (w k χ s) * w h χ t = conj (∑ χ ∈ coefficientBlock basis
            (localizedComplexIntegerRing ideal) B, w k χ s * conj (w h χ t)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_mul, Complex.conj_conj]
      rw [htarget]
      fin_cases t
      · simp only [Fin.zero_eta]
        rw [h0, map_zero]
      · simp only [Fin.mk_one]
        rw [h1, map_zero]
  ·
    intro k hk s z hz
    refine hw5 k hk z (fun a' c hac hcomm ha' hc hconj => ?_) s
    have heq := two_part_unique (show (1 : G) * z = z from one_mul z) (Commute.one_left z)
      ⟨0, by rw [orderOf_one, pow_zero]⟩ hz hac hcomm ha' hc
    rw [← heq] at hconj
    have h1 := isConj_one_right.mp hconj
    obtain ⟨r, hr1, hr⟩ := hord k hk
    rw [h1, orderOf_one] at hr
    exact (Nat.one_lt_two_pow (by omega)).ne' hr.symm

end CFSG.Wreathed.FlatCentralFourier
