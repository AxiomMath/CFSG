module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersCentralizer
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersLayer
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersOddSplit
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersOddNonsplit

public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.CentralSL2 CFSG.ABGTheoremB
open scoped Pointwise

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem bot_mem_modelSignalizers (p : ℕ) :
    (⊥ : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)) ∈
      signalizers (modelLayer b m hm heven Sigma hSigma) (modelC b m hm heven Sigma hSigma) p := by
  refine ⟨bot_le, IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero]), ?_,
    bot_inf_eq _⟩
  apply le_normalizer_of_forall_conj_mem
  intro c _ r hr
  rw [Subgroup.mem_bot] at hr ⊢
  rw [hr, mul_one, mul_inv_cancel]

theorem four_dvd_of_eq_two_pow_padicValInt {p f : ℕ} (hpodd : Odd p) (hq : 1 < p ^ f) (ε : ℤ)
    (hε : ε = if p ^ f % 4 = 1 then 1 else -1) {m : ℕ}
    (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - ε)) : 4 ∣ m := by
  have hodd : Odd (p ^ f) := hpodd.pow
  have h4 : (2 : ℤ) ^ 2 ∣ ((p ^ f : ℕ) : ℤ) - ε := by
    obtain ⟨k, hk⟩ := hodd
    rw [hε]
    split_ifs with h
    · refine ⟨(p ^ f / 4 : ℕ), ?_⟩
      have := Nat.div_add_mod (p ^ f) 4
      rw [h] at this
      omega
    · refine ⟨((p ^ f / 4 : ℕ) + 1 : ℤ), ?_⟩
      have := Nat.div_add_mod (p ^ f) 4
      have h3 : p ^ f % 4 = 3 := by omega
      rw [h3] at this
      omega
  have hne : ((p ^ f : ℕ) : ℤ) - ε ≠ 0 := by
    rw [hε]
    split_ifs with h
    · intro h0
      have h1 : ((p ^ f : ℕ) : ℤ) = 1 := by linarith
      have h1' : p ^ f = 1 := by exact_mod_cast h1
      omega
    · intro h0
      have h0' : (0 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) := Int.natCast_nonneg _
      linarith
  have hv : 2 ≤ padicValInt 2 (((p ^ f : ℕ) : ℤ) - ε) :=
    ((padicValInt_dvd_iff (p := 2) 2 (((p ^ f : ℕ) : ℤ) - ε)).mp h4).resolve_left hne
  rw [hm2]
  exact (Nat.pow_dvd_pow 2 hv : 2 ^ 2 ∣ 2 ^ _)

theorem isSquare_neg_one_iff_pow_mod_four [Fintype F] {p f : ℕ} (hpodd : Odd p)
    (hcard : Nat.card F = p ^ f) : IsSquare (-1 : F) ↔ p ^ f % 4 = 1 := by
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hcard]
  have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.mp hpodd.pow
  omega

theorem allModelSignalizerFacts : AllModelSignalizerFacts := by
  intro F _ _ p f hp hpodd hf hcard hq ε hε m hm heven hm2 Sigma hd b hSigma hb
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  have h4 : 4 ∣ m := four_dvd_of_eq_two_pow_padicValInt hpodd (by omega) ε hε hm2
  have hq' : 5 < Nat.card F := by rw [hcard]; exact hq
  have hp2 : p ≠ 2 := fun h => by
    rw [h] at hpodd
    exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hsq := isSquare_neg_one_iff_pow_mod_four (F := F) hpodd hcard
  refine
    { centralizer_le := centralizer_le_modelBase h2 hb
      signalizer_le := signalizer_le_modelLayer h4
      layer_signalizer := fun r hr hr2 X hX hX1 =>
        ⟨hsq.mp (isSquare_neg_one_of_signalizer h2 hq' h4 hX hX1),
          prime_eq_of_signalizer h2 hq' h4 hp hcard hr hr2 hX hX1⟩
      layer_signalizer_pair := fun h1 => ?_
      permutable_le := fun U hU hperm => ?_ }
  · obtain ⟨i, hi⟩ := hsq.mpr h1
    have hi' : i * i = -1 := hi.symm
    exact ⟨rootGroup b m hm heven Sigma hSigma i hi',
      rootGroup b m hm heven Sigma hSigma (-i) (neg_mul_neg_eq_neg_one hi'),
      rootGroup_mem_signalizers h2 hd hcard hi',
      rootGroup_mem_signalizers h2 hd hcard (neg_mul_neg_eq_neg_one hi'),
      (card_rootGroup hi').trans hcard, (card_rootGroup _).trans hcard,
      rootGroup_ne_rootGroup_neg h2 hi', modelLayer_eq_rootGroup_sup h2 hi',
      fun _ hh => conjSub_rootGroup_of_conj_modelY h2 hd hi' hh,
      fun _ hX => signalizer_le_rootGroup_or h2 hq' h4 hi' hp hp2 hX,
      fun _ hXQ hXC => eq_bot_or_eq_rootGroup h2 hi' hXQ hXC,
      fun _ hXQ hXC => eq_bot_or_eq_rootGroup h2 (neg_mul_neg_eq_neg_one hi') hXQ hXC⟩
  · by_cases hs : IsSquare (-1 : F)
    · obtain ⟨i, hi⟩ := hs
      have hi' : i * i = -1 := hi.symm
      rcases le_sup_rootGroup_of_permutable h2 hb hd hi' hU hperm with h | h
      · exact ⟨p, _, hp, rootGroup_mem_signalizers h2 hd hcard hi', h⟩
      · exact ⟨p, _, hp, rootGroup_mem_signalizers h2 hd hcard (neg_mul_neg_eq_neg_one hi'), h⟩
    · refine ⟨p, ⊥, hp, bot_mem_modelSignalizers p, ?_⟩
      rw [sup_bot_eq]
      exact le_modelC_of_permutable h2 hb hd hs hU hperm

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
