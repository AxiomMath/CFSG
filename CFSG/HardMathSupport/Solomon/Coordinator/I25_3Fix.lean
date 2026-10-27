module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3FixP
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Ja

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

theorem i253_primeCore_bot {S : Type} [Group S] [Finite S] (hS : CFSG.Open.IsQuasisimple S)
    (h3 : 3 ∣ Nat.card S) (hz : ∀ z ∈ Subgroup.center S, z ^ 3 = 1) : GLAPPrimeCore 3 S = ⊥ := by
  have hle := i253_primeCore_le_center hS h3
  rw [eq_bot_iff]
  intro x hx
  have hcop := coprime_card_gLAPPrimeCore_aux 3 S
  have hx3 : x ^ 3 = 1 := hz x (hle hx)
  have hord : orderOf x ∣ Nat.card (GLAPPrimeCore 3 S) := by
    have := Subgroup.orderOf_dvd_natCard (GLAPPrimeCore 3 S) hx
    exact this
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ Nat.gcd 3 (Nat.card (GLAPPrimeCore 3 S)) := Nat.dvd_gcd h1 hord
  rw [hcop] at h2
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2))

theorem i253_cover_data {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] (hY : SL3EpsOfChar p Y) :
    ∃ (π : Bool) (f : ℕ) (K : Type) (_ : Field K) (hK : PiField π p f K),
      ModThree π (p ^ f) ∧ 2 < p ^ f ∧ Nonempty (Y ≃* ↥(slPi π 3 (p ^ f) K)) ∧
        (π = false → p ^ f = 8 → IsSU38 Y) := by
  rcases hY with ⟨K, hF, hfin, hchar, hmod, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hchar, hcard, hq3, hq2, ⟨e⟩⟩
  · have := Fintype.ofFinite K
    obtain ⟨n, hpn, hcn⟩ := FiniteField.card K p
    rw [← Nat.card_eq_fintype_card] at hcn
    have hpf : Nat.card K = p ^ (n : ℕ) := hcn
    refine ⟨true, n, K, hF, ⟨hp, n.pos, hpf⟩, ?_, ?_, ⟨e⟩, fun h => absurd h (by simp)⟩
    · show (p ^ (n : ℕ)) % 3 = 1
      rw [← hpf]; exact hmod
    · have h1 : (p ^ (n : ℕ)) % 3 = 1 := by rw [← hpf]; exact hmod
      have h2 : 2 ≤ p ^ (n : ℕ) := by
        have := Nat.one_lt_pow n.ne_zero hp.one_lt
        omega
      omega
  · have := Fintype.ofFinite K
    obtain ⟨n, hpn, hcn⟩ := FiniteField.card K p
    rw [← Nat.card_eq_fintype_card] at hcn
    have hpf : Nat.card K = p ^ (n : ℕ) := hcn
    have hqd : q ∣ p ^ (n : ℕ) := by
      rw [← hpf, hcard]; exact Dvd.intro_left q (by ring)
    obtain ⟨i, hi, hqi⟩ := (Nat.dvd_prime_pow hp).1 hqd
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | h
      · simp at hqi; subst hqi; omega
      · exact h
    refine ⟨false, i, K, hF, ⟨hp, hi1, ?_⟩, ?_, ?_, ⟨?_⟩, fun _ h8 => ?_⟩
    · show Nat.card K = (p ^ i) ^ 2
      rw [← hqi]; exact hcard
    · show (p ^ i) % 3 = 2
      rw [← hqi]; exact hq3
    · rw [← hqi]; omega
    · rw [← hqi]; exact e
    · rw [← hqi] at h8
      subst h8
      exact ⟨K, hF, hfin, hcard, ⟨e⟩⟩


theorem i253_fixStruct {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) {p : ℕ}
    (hp : p.Prime) (hpc : SL3EpsOfChar p Y) (hz : ∃ z ∈ Subgroup.center Y, z ≠ 1)
    {α : MulAut Y} (h3 : α ^ 3 = 1) (hf : IsFieldAutThree α) (h8 : α ≠ 1 → ¬ IsSU38 Y) :
    CFSG.Open.IsQuasisimple ↥(fixSubgroup α) ∧ Subgroup.center Y ≤ fixSubgroup α ∧
      3 ∣ Nat.card ↥(fixSubgroup α) ∧
      (∀ z ∈ Subgroup.center ↥(fixSubgroup α), z ^ 3 = 1) ∧
      ∃ x ∈ fixSubgroup α, orderOf x = p := by
  obtain ⟨π, f, K, hF, hK, hq, hq2, ⟨e⟩, h8'⟩ := i253_cover_data hp hpc
  have h8'' : α ≠ 1 → π = false → p ^ f ≠ 8 := fun hα hπ h8p => h8 hα (h8' hπ h8p)
  have hFD : FixData Y α := by
    by_cases hα : α = 1
    · subst hα
      refine fixData_of_congr_eq e (β := 1) (map_one _) ?_
      exact fixData_one (isQuasisimple_slPi hK (fun _ h => by omega)) (isL3Type_slPi hK hq)
        (fun z hz => pow_three_of_mem_center hK hq hz) (three_dvd_card_slPi hK hq)
        (fun _ => isSLThreeEpsAny_slPi hK hq hq2)
    · exact fixData_cover hY hK hq (h8'' hα) hq2 e h3 hf
  obtain ⟨S, hSF, hcomm, hpow, hqs, hty, hz3, h3d, hcen, hZS, hex⟩ := hFD
  obtain ⟨hSeq, -⟩ := hex hz
  have hS' : fixSubgroup α = S := hSeq
  subst hS'
  exact ⟨hqs, hZS, h3d, hz3, i253_fixP_cover hY hK hq hq2 e h3 hf h8''⟩

end CFSG.HardMathSupport.Solomon.Coordinator
