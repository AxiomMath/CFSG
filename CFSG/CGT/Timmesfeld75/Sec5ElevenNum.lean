module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Timmesfeld CFSG.Assembly.LowTwoRank

theorem eq_of_dvd_mul {s a m n : ℕ} (hs : 1 ≤ s) (ha : 2 ≤ a) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hstar : m * (n - 1) = s * (a - 1)) {i : ℕ} (hi2 : 2 ≤ i) (hia : i ≤ a)
    (hdvd : m * n ∣ s * i) : m = s ∧ n = a := by
  have hd : m * n = s * (a - 1) + m := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hstar
    rw [Nat.mul_succ, hstar]
  have hsa : s * a = s * (a - 1) + s := by
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    simp [Nat.mul_succ]
  have hsle : s ≤ s * (a - 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hia' : i = a := by
    by_contra hne
    have hlt : i ≤ a - 1 := by omega
    have h1 : s * i ≤ s * (a - 1) := Nat.mul_le_mul_left _ hlt
    have h2 : m * n ≤ s * i := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd
    omega
  subst hia'
  have h3 : s * i = m * n :=
    Nat.eq_of_dvd_of_lt_two_mul (Nat.mul_ne_zero (by omega) (by omega)) hdvd (by omega)
  have hms : m = s := by omega
  subst hms
  exact ⟨rfl, (Nat.eq_of_mul_eq_mul_left (by omega) h3).symm⟩

theorem card_sub_one_dvd_card {Y V : Type*} [Group Y] [Finite Y] [Group V] [Finite V]
    (ρ : Y →* MulAut V) (htr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ y : Y, ρ y v = w)
    (hV : 1 < Nat.card V) : Nat.card V - 1 ∣ Nat.card Y := by
  let _ : MulAction Y V := MulAction.compHom V ρ
  have hnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 hV
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  have horb : MulAction.orbit Y v = {w | w ≠ 1} := by
    ext w
    constructor
    · rintro ⟨y, rfl⟩
      show ρ y v ≠ 1
      intro h
      apply hv
      apply (ρ y).injective
      rw [h, map_one]
    · intro hw
      obtain ⟨y, hy⟩ := htr v w hv hw
      exact ⟨y, hy⟩
  have hcard : (MulAction.orbit Y v).ncard = Nat.card V - 1 := by
    rw [horb]
    have : ({w : V | w ≠ 1} : Set V) = Set.univ \ {1} := by
      ext w
      simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
  rw [← hcard, ← MulAction.index_stabilizer Y v]
  exact Subgroup.index_dvd_card _

theorem isPrimitivePrimeDivisor_lt {p k : ℕ} (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) :
    k < p := by
  have hp := h.prime
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (h.ne_two hk).symm
  have h1 : 2 ^ (p - 1) ≡ 1 [MOD p] := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  have h2 : p ∣ 2 ^ (p - 1) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h1.symm
  have h3 : k ∣ p - 1 := (h.dvd_sub_one_iff hk (p - 1)).1 h2
  have := Nat.le_of_dvd (by have := hp.two_le; omega) h3
  have := hp.two_le
  omega

theorem card_dvd_card_SL {K : Type*} [Group K] {F : Type} [Field F] {a : ℕ}
    (e : K ≃* StatedProj (StatedSL a F)) :
    Nat.card K ∣ Nat.card (Matrix.SpecialLinearGroup (Fin a) F) := by
  rw [Nat.card_congr (e.trans (projectiveSpecialLinearGroupEquivStatedProj a F).symm).toEquiv]
  exact Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk'
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin a) F))) (QuotientGroup.mk'_surjective _)

theorem exists_dvd_pow_sub_one_of_dvd_card_SL {F : Type} [Field F] [Finite F] {s a r : ℕ}
    (hF : Nat.card F = 2 ^ s) (ha : 1 ≤ a) (hr : r.Prime) (hr2 : r ≠ 2)
    (hdvd : r ∣ Nat.card (Matrix.SpecialLinearGroup (Fin a) F)) :
    ∃ i, 2 ≤ i ∧ i ≤ a ∧ r ∣ 2 ^ (s * i) - 1 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq ha, hF] at hdvd
  rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
  · exfalso
    have h1 := hr.dvd_of_dvd_pow h
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp at h1
      exact hr.one_lt.ne' h1
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h1))
  · obtain ⟨i, hi, hri⟩ := (Prime.dvd_finsetProd_iff hr.prime _).1 h
    rw [Finset.mem_Icc] at hi
    exact ⟨i, hi.1, hi.2, by rwa [← pow_mul] at hri⟩

@[expose] def MultPrimeInput : Prop :=
  ∀ (a s : ℕ), 2 ≤ a → 1 ≤ s → ∀ (Y : Type) [Group Y] [Finite Y], commutator Y = ⊤ →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ s ∧
      Nonempty (Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL a F))) →
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (Subgroup.center Y) → p ≤ max a 3

theorem eq_of_transitive_primitive (hMult : MultPrimeInput) {Y : Type} [Group Y] [Finite Y]
    (hperf : commutator Y = ⊤) {F : Type} [Field F] [Finite F] {a s m n : ℕ} (hs : 1 ≤ s)
    (ha : 2 ≤ a) (hm : 1 ≤ m) (hn : 2 ≤ n) (hd3 : 3 ≤ m * n) (hd6 : m * n ≠ 6)
    (hstar : m * (n - 1) = s * (a - 1)) (hF : Nat.card F = 2 ^ s)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL a F)) {V : Type} [Group V] [Finite V]
    (hV : Nat.card V = 2 ^ (m * n)) (ρ : Y →* MulAut V)
    (htr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ y : Y, ρ y v = w) : m = s ∧ n = a := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := m * n) (by omega) hd6
  have hmn : 0 < m * n := by omega
  have hrp := hr.prime
  have hr2 := hr.ne_two hmn
  have hrk := isPrimitivePrimeDivisor_lt hr hmn
  have hV1 : 1 < Nat.card V := by
    rw [hV]
    exact Nat.one_lt_two_pow (by omega)
  have h1 : r ∣ Nat.card Y := by
    have h2 := card_sub_one_dvd_card ρ htr hV1
    rw [hV] at h2
    exact (hr.dvd).trans h2
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)] at h1
  have hd : m * n = s * (a - 1) + m := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hstar
    rw [Nat.mul_succ, hstar]
  have hsle : a - 1 ≤ s * (a - 1) := Nat.le_mul_of_pos_left _ (by omega)
  rcases (Nat.Prime.dvd_mul hrp).1 h1 with hK | hZ
  · have hSL := hK.trans (card_dvd_card_SL e)
    obtain ⟨i, hi2, hia, hri⟩ := exists_dvd_pow_sub_one_of_dvd_card_SL hF (by omega) hrp hr2 hSL
    exact eq_of_dvd_mul hs ha hm (by omega) hstar hi2 hia ((hr.dvd_sub_one_iff hmn _).1 hri)
  · exfalso
    have hle := hMult a s ha hs Y hperf ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩ r hrp hZ
    have : a ≤ m * n := by omega
    rcases le_max_iff.1 hle with h | h
    · omega
    · omega

end CFSG.CGT.Timmesfeld75
