module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Field

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Census CFSG.Assembly.RankThreeEven TauCeti
open KDRank3FieldAux

namespace KDRank3FieldAux

theorem dvd_exponent_of_dvd_outer_primeFormP {p f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) (hp2 : p ≠ 2)
    (hout : p ∣ Nat.card (Outer (primeFormP h
      (((1 : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) : p ∣ f := by
  classical
  have hp := h.prime
  haveI := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, hsurj, hker, -, hinn, hcard⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set P := primeFormP h (((1 : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set D := primeFormD h (((1 : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hID : inner P ≤ D := by
    intro α hα
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨⟨s, s.2.1⟩, rfl⟩
  have h1 : ¬ p ∣ (inner P).relIndex D := by
    intro hd
    have h' : (inner P).relIndex D ∣ p ^ f + 1 := hcard
    have h2 : p ∣ p ^ f + 1 := hd.trans h'
    have h3 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h3).1 h2))
  have h2 : D.relIndex ⊤ ∣ 2 * f := by
    rw [Subgroup.relIndex_top_right, ← hker, Subgroup.index_ker,
      MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top,
      card_ringEquiv_eq hp (by have := h.one_le; omega) h.card]
  have h3 : ¬ p ∣ (⊤ : Subgroup (MulAut P)).index := by
    rw [Subgroup.index_top]; exact hp.not_dvd_one
  have := dvd_of_dvd_index_chain hID le_top hp h1 h2 h3 hout
  rcases (Nat.Prime.dvd_mul hp).1 this with h2' | h2'
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2') hp2
  · exact h2'

end KDRank3FieldAux

theorem kdRank3Field_twistedA (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid) :
    KDRank3FieldAt ⟨.twistedA r q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  have hr : 2 ≤ r :=
    ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hqp : q.p = p := (LieTypeIndex.characteristic_twistedA r q).symm.trans hchar
  subst hqp
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI := h.finite
  let eU : S ≃* unitaryPSU h (r + 1) := eT.trans (unitaryPSUEquiv h (by omega)).symm
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | hr4
  ·
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 2 + 1) (K := K))
    have hout' : q.p ∣ Nat.card (Outer (primeFormP h
        (((1 : GL (Fin (2 + 1)) K) : GL (Fin (2 + 1)) K) :
          Matrix (Fin (2 + 1)) (Fin (2 + 1)) K))) := by
      rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (eU.trans eP.symm)).toEquiv]
      exact hout
    have hpf : q.p ∣ q.exponent :=
      dvd_exponent_of_dvd_outer_primeFormP h (by omega) hq' hp2 hout'
    have hf3 : 3 ≤ q.exponent := hp3.trans (Nat.le_of_dvd q.exponent_pos hpf)
    have h1 := le_gla_of_carrier eU q.prime_p
      (le_localRank_unitaryPSU h hp2 (n := 2 + 1) (r := 1) (by norm_num) (by norm_num))
    have hf : q.exponent ≤ 3 := by simpa using h1.trans hrank
    have hf' : q.exponent = 3 := le_antisymm hf hf3
    have hq3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 (hf' ▸ hpf)
    right; left
    show q.card = 27
    rw [PrimePower.card_def, hq3, hf']
    norm_num
  ·
    exfalso
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 3 + 1) (K := K))
    have hout' : q.p ∣ Nat.card (Outer (primeFormP h
        (((1 : GL (Fin (3 + 1)) K) : GL (Fin (3 + 1)) K) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) K))) := by
      rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (eU.trans eP.symm)).toEquiv]
      exact hout
    have hpf : q.p ∣ q.exponent :=
      dvd_exponent_of_dvd_outer_primeFormP h (by omega) hq' hp2 hout'
    have hf3 : 3 ≤ q.exponent := hp3.trans (Nat.le_of_dvd q.exponent_pos hpf)
    have h1 := le_gla_of_carrier eU q.prime_p (le_localRank_unitaryPSU_four h hp2)
    omega
  · exfalso
    have h1 := le_gla_of_carrier eU q.prime_p
      (le_localRank_unitaryPSU h hp2 (n := r + 1) (r := 2) (by norm_num) (by omega))
    have := q.exponent_pos
    norm_num at h1
    omega

end CFSG.LocalAnalysis.GLTheoremA
