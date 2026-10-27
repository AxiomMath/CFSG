module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.List93

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.CatLeaf (lieSylowExponent lieOrderNumerator lieOrderDivisor)
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd sporadicOrdersTable_holds)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

@[expose] def lie2Tags : List StatedLieTag :=
  [.PSL, .PSU, .PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus, .G2, .F4, .E6, .E7, .E8, .twistedE6,
    .trialityD4, .twistedB2, .twistedG2, .twistedF4, .Tits]

theorem mem_lie2Tags (t : StatedLieTag) : t ∈ lie2Tags := by
  cases t <;> simp [lie2Tags]

theorem fact2_two_pow_mul {a m : ℕ} (hm : Odd m) : (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd]
  · simp
  · intro h2
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)

private theorem tri_ge {n : ℕ} (hn : 2 ≤ n) : n - 1 ≤ n * (n - 1) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

theorem lie_reduce {a : ℕ} (ha : 1 ≤ a) (t : StatedLieTag) (n f : ℕ)
    (h : lieSylowExponent t n * f = a) :
    ∃ n' : ℕ, n' ≤ a + 1 ∧ lieSylowExponent t n' * f = a ∧
      (∀ q, lieOrderNumerator t n' q = lieOrderNumerator t n q) ∧
      (∀ q, lieOrderDivisor t n' q = lieOrderDivisor t n q) := by
  by_cases hn : n ≤ a + 1
  · exact ⟨n, hn, h, fun _ => rfl, fun _ => rfl⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0
      simp at h
      omega
    · exact h0
  have hle : lieSylowExponent t n ≤ a := by
    rw [← h]
    exact Nat.le_mul_of_pos_right _ hf
  cases t
  all_goals first
    | exact ⟨0, by omega, by simpa [lieSylowExponent] using h, fun _ => rfl, fun _ => rfl⟩
    | (exfalso
       simp only [lieSylowExponent] at hle
       first
         | (have := tri_ge (n := n) (by omega); omega)
         | (have := Nat.le_self_pow (show (2 : ℕ) ≠ 0 by norm_num) n; omega)
         | (have := Nat.le_mul_of_pos_right n (show 0 < n - 1 by omega); omega))

theorem chk_of_bounded {a N : ℕ} (ha : 1 ≤ a)
    (hb : ∀ t ∈ lie2Tags, ∀ n ≤ a + 1, ∀ f ≤ a, lieSylowExponent t n * f = a →
      N * lieOrderDivisor t n (2 ^ f) ≠ lieOrderNumerator t n (2 ^ f))
    (t : StatedLieTag) (n f : ℕ) (h : lieSylowExponent t n * f = a) :
    N * lieOrderDivisor t n (2 ^ f) ≠ lieOrderNumerator t n (2 ^ f) := by
  obtain ⟨n', hn', h', e1, e2⟩ := lie_reduce ha t n f h
  have hN : 1 ≤ lieSylowExponent t n := by
    rcases Nat.eq_zero_or_pos (lieSylowExponent t n) with h0 | h0
    · rw [h0, zero_mul] at h
      omega
    · exact h0
  have hf : f ≤ a := by
    rw [← h]
    exact Nat.le_mul_of_pos_left f hN
  have := hb t (mem_lie2Tags t) n' hn' f hf h'
  rw [e1 (2 ^ f), e2 (2 ^ f)] at this
  exact this

theorem amb2_lie {d : TauCeti.LieTypeIndex} (hv : d.Valid)
    (h : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    (∃ q : TauCeti.PrimePower, d = .A 1 q ∧ q.card = 7) ∨
      (∃ q : TauCeti.PrimePower, d = .twistedA 2 q ∧ q.card = 3) := by
  revert h
  cases d
  case A r q =>
    match r, q with
    | 1, q => exact fun h => h.elim (fun h7 => Or.inl ⟨q, rfl, h7.1⟩) (fun h8 => absurd h8.2 (by norm_num))
    | 0, q => exact fun h => False.elim h
    | r' + 2, q => exact fun h => False.elim h
  case twistedA r q =>
    match r, q with
    | 2, q => exact fun h => Or.inr ⟨q, rfl, h.1⟩
    | 3, q => exact fun h => absurd h.2 (by norm_num)
    | 0, q => exact fun h => False.elim h
    | 1, q => exact fun h => False.elim h
    | r' + 4, q => exact fun h => False.elim h
  all_goals exact fun h => False.elim h

theorem l33_lie {d : TauCeti.LieTypeIndex} (hv : d.Valid)
    (h : l33Idx (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    ∃ q : TauCeti.PrimePower, d = .A 2 q ∧ q.card = 3 := by
  revert h
  cases d
  case A r q =>
    match r, q with
    | 2, q => exact fun h => ⟨q, rfl, h⟩
    | 0, q => exact fun h => False.elim h
    | 1, q => exact fun h => False.elim h
    | r' + 3, q => exact fun h => False.elim h
  all_goals exact fun h => False.elim h

end CFSG.LocalAnalysis.GLTheoremA.List93

end
