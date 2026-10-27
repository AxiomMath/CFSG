module

public import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.LieType.Steinberg.CentralExt.FieldThreeE7Multiplier
public import CFSG.LieType.Steinberg.CentralExt.FieldThreeF4Multiplier
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.Adapters.TauCetiExceptional.EvenAll

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

variable {X : Type} [Group X] {n p f : ℕ}

theorem eq_two_two_of_pow_eq_four {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ^ f = 4) :
    p = 2 ∧ f = 2 := by
  have hdvd : p ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h]
    exact dvd_pow_self p hf.ne'
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num))⟩

theorem pow_cases {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h3 : p ^ f ≠ 3) :
    (p = 2 ∧ p ^ f = 2) ∨ (p = 2 ∧ p ^ f = 4) ∨ 5 ≤ p ^ f := by
  have h2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow hf.ne' p)
  rcases (show p ^ f = 2 ∨ p ^ f = 4 ∨ 5 ≤ p ^ f by omega) with h | h | h
  · refine Or.inl ⟨?_, h⟩
    have hdvd : p ∣ 2 := by
      rw [← h]
      exact dvd_pow_self p hf.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd
  · exact Or.inr (Or.inl ⟨(eq_two_two_of_pow_eq_four hp hf h).1, h⟩)
  · exact Or.inr (Or.inr h)

theorem row_of_subsingleton {t : StatedLieTag} (hg : genericOrders t n p f = (1, 1))
    (he : exceptionalOrders t n p f = (1, 1))
    (h : commutator X = ⊤ ∧ Subsingleton (CFSG.Open.griessHopfMultiplier X)) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f) := by
  obtain ⟨hX, hM⟩ := h
  let _ : Unique (CFSG.Open.griessHopfMultiplier X) := uniqueOfSubsingleton 1
  let _ : Unique ((Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) ×
      (Multiplicative (ZMod 1) × Multiplicative (ZMod 1))) := Unique.mk' _
  exact ⟨hX, ⟨MulEquiv.ofUnique.trans (GriessClassical.toGenEx hg he)⟩⟩

theorem g2_row (hmodel : CFSG.Models.LieModel X .G2 n p f) (hq : 5 ≤ p ^ f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .G2 n p f × exceptional .G2 n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | G2 q =>
      obtain ⟨rfl, rfl⟩ := hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact GaloisField.card _ _ q.exponent_pos.ne'
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv
        (GaloisField q.p q.exponent) hK
      have h22 : ¬(n = 0 ∧ q.p = 2 ∧ q.exponent = 2) := by
        rintro ⟨-, h2, h1⟩
        rw [h2, h1] at hq
        norm_num at hq
      have h31 : ¬(n = 0 ∧ q.p = 3 ∧ q.exponent = 1) := by
        rintro ⟨-, h2, h1⟩
        rw [h2, h1] at hq
        norm_num at hq
      refine GriessClassical.of_mulEquiv (e.trans b.symm) (row_of_subsingleton rfl ?_
        (AdjointClosed.g2_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def]; exact hq)))
      unfold exceptionalOrders
      split <;> simp_all
    | _ => simp [CFSG.Models.NamesTag] at hd

theorem f4_row (hmodel : CFSG.Models.LieModel X .F4 n p f) (hq : 3 ≤ p ^ f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .F4 n p f × exceptional .F4 n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | F4 q =>
      obtain ⟨rfl, rfl⟩ := hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact GaloisField.card _ _ q.exponent_pos.ne'
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv
        (GaloisField q.p q.exponent) hK
      have h21 : ¬(n = 0 ∧ q.p = 2 ∧ q.exponent = 1) := by
        rintro ⟨-, h2, h1⟩
        rw [h2, h1] at hq
        norm_num at hq
      have hM : commutator (AdjointQuotient .F4 (GaloisField q.p q.exponent)) = ⊤ ∧
          Subsingleton (CFSG.Open.griessHopfMultiplier
            (AdjointQuotient .F4 (GaloisField q.p q.exponent))) := by
        rcases eq_or_lt_of_le hq with h3 | h4
        · exact FieldThree.f4_three_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, ← h3])
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt h4) with h4 | h5
        · obtain ⟨hp2, -⟩ := eq_two_two_of_pow_eq_four q.prime_p q.exponent_pos h4.symm
          have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hp2
          exact FieldFour.f4_four_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, ← h4]; norm_num)
        · exact AdjointClosed.f4_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def]; exact h5)
      refine GriessClassical.of_mulEquiv (e.trans b.symm) (row_of_subsingleton rfl ?_ hM)
      unfold exceptionalOrders
      split <;> simp_all
    | _ => simp [CFSG.Models.NamesTag] at hd

theorem e8_row (hmodel : CFSG.Models.LieModel X .E8 n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .E8 n p f × exceptional .E8 n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | E8 q =>
      obtain ⟨rfl, rfl⟩ := hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact GaloisField.card _ _ q.exponent_pos.ne'
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e8 q hv
        (GaloisField q.p q.exponent) hK
      have hM : commutator (AdjointQuotient .E8 (GaloisField q.p q.exponent)) = ⊤ ∧
          Subsingleton (CFSG.Open.griessHopfMultiplier
            (AdjointQuotient .E8 (GaloisField q.p q.exponent))) := by
        by_cases h3 : q.p ^ q.exponent = 3
        · exact FieldThree.e8_three_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, h3])
        rcases pow_cases q.prime_p q.exponent_pos h3 with ⟨hp2, h2⟩ | ⟨hp2, h4⟩ | h5
        · have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hp2
          exact FieldTwo.e8_two_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, h2])
        · have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hp2
          exact FieldFour.e8_four_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, h4]; norm_num)
        · exact AdjointClosed.e8_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def]; exact h5)
      refine GriessClassical.of_mulEquiv (e.trans b.symm) (row_of_subsingleton rfl ?_ hM)
      unfold exceptionalOrders
      split <;> simp_all
    | _ => simp [CFSG.Models.NamesTag] at hd

theorem e6_row (hmodel : CFSG.Models.LieModel X .E6 n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .E6 n p f × exceptional .E6 n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | E6 q =>
      obtain ⟨rfl, rfl⟩ := hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact GaloisField.card _ _ q.exponent_pos.ne'
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e6 q hv
        (GaloisField q.p q.exponent) hK
      have hM : commutator (AdjointQuotient .E6 (GaloisField q.p q.exponent)) = ⊤ ∧
          Nonempty (CFSG.Open.griessHopfMultiplier
            (AdjointQuotient .E6 (GaloisField q.p q.exponent)) ≃*
              Multiplicative (ZMod (Nat.gcd 3 (Nat.card (GaloisField q.p q.exponent) - 1)))) := by
        by_cases h3 : q.p ^ q.exponent = 3
        · exact FieldThree.e6_three_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, h3])
        rcases pow_cases q.prime_p q.exponent_pos h3 with ⟨hp2, h2⟩ | ⟨hp2, h4⟩ | h5
        · have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hp2
          exact FieldTwo.e6_two_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, h2])
        · have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hp2
          exact FieldFour.e6_four_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, h4]; norm_num)
        · exact MinusculeClosed.e6_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def]; exact h5)
      rw [hK, TauCeti.PrimePower.card_def] at hM
      refine GriessClassical.of_mulEquiv (e.trans b.symm)
        (GriessClassical.of_mulEquiv_target ?_ hM)
      refine (GriessClassical.padOne _).trans (GriessClassical.toGenEx (t := .E6) (n := n)
        (p := q.p) (f := q.exponent) (a₁ := Nat.gcd 3 (q.p ^ q.exponent - 1)) (a₂ := 1) (b₁ := 1)
        (b₂ := 1) rfl ?_)
      unfold exceptionalOrders
      split <;> simp_all
    | _ => simp [CFSG.Models.NamesTag] at hd

section E7

theorem e7_row (hmodel : CFSG.Models.LieModel X .E7 n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .E7 n p f × exceptional .E7 n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | E7 q =>
      obtain ⟨rfl, rfl⟩ := hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact GaloisField.card _ _ q.exponent_pos.ne'
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e7 q hv
        (GaloisField q.p q.exponent) hK
      have hM : commutator (AdjointQuotient .E7 (GaloisField q.p q.exponent)) = ⊤ ∧
          Nonempty (CFSG.Open.griessHopfMultiplier
            (AdjointQuotient .E7 (GaloisField q.p q.exponent)) ≃*
              Multiplicative (ZMod (Nat.gcd 2 (Nat.card (GaloisField q.p q.exponent) - 1)))) := by
        by_cases h3 : q.p ^ q.exponent = 3
        · exact FieldThree.e7_three_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, h3])
        rcases pow_cases q.prime_p q.exponent_pos h3 with ⟨hp2, h2⟩ | ⟨hp2, h4⟩ | h5
        · have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hp2
          exact FieldTwo.e7_two_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, h2])
        · have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hp2
          exact FieldFour.e7_four_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def, h4]; norm_num)
        · exact MinusculeClosed.e7_hopfMultiplier (by rw [hK, TauCeti.PrimePower.card_def]; exact h5)
      rw [hK, TauCeti.PrimePower.card_def] at hM
      refine GriessClassical.of_mulEquiv (e.trans b.symm)
        (GriessClassical.of_mulEquiv_target ?_ hM)
      refine (GriessClassical.padOne _).trans (GriessClassical.toGenEx (t := .E7) (n := n)
        (p := q.p) (f := q.exponent) (a₁ := Nat.gcd 2 (q.p ^ q.exponent - 1)) (a₂ := 1) (b₁ := 1)
        (b₂ := 1) rfl ?_)
      unfold exceptionalOrders
      split <;> simp_all
    | _ => simp [CFSG.Models.NamesTag] at hd

end E7

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
