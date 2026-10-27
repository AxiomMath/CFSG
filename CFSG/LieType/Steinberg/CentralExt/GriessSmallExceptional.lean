module

public import CFSG.LieType.Steinberg.CentralExt.GriessAllModels

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

theorem row_of_card_prime {X : Type} [Group X] {t : StatedLieTag} {n p f ℓ : ℕ}
    [Fact ℓ.Prime] (hg : genericOrders t n p f = (1, 1))
    (he : exceptionalOrders t n p f = (ℓ, 1)) (hX : commutator X = ⊤)
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier X) = ℓ) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f) := by
  refine ⟨hX, ⟨?_⟩⟩
  have hℓ : Nat.card (Multiplicative (ZMod ℓ)) = ℓ := by
    have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
    exact ZMod.card ℓ
  let _ : Unique (Multiplicative (ZMod 1)) := inferInstance
  let _ : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) := Unique.mk' _
  exact (mulEquivOfPrimeCardEq hM hℓ).trans (MulEquiv.prodUnique.symm.trans
    (MulEquiv.uniqueProd.symm.trans (GriessClassical.toGenEx hg he)))

variable {X : Type} [Group X]

theorem g2_three_native_row_of_card
    (hcard : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) = 3)
    (hperf : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
      commutator (AdjointQuotient .G2 K) = ⊤)
    (h : ChevalleyExceptionalModel X .G2 3 1) : GriessAll.GriessRow X .G2 0 3 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact GriessClassical.of_mulEquiv e (row_of_card_prime (ℓ := 3) rfl rfl
    (hperf K (by rw [hK]; norm_num)) (hcard K (by rw [hK]; norm_num)))

theorem g2_four_native_row_of_card
    (hcard : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) = 2)
    (hperf : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
      commutator (AdjointQuotient .G2 K) = ⊤)
    (h : ChevalleyExceptionalModel X .G2 2 2) : GriessAll.GriessRow X .G2 0 2 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact GriessClassical.of_mulEquiv e (row_of_card_prime (ℓ := 2) rfl rfl
    (hperf K (by rw [hK]; norm_num)) (hcard K (by rw [hK]; norm_num)))

theorem f4_two_native_row_of_card
    (hcard : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) = 2)
    (hperf : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      commutator (AdjointQuotient .F4 K) = ⊤)
    (h : ChevalleyExceptionalModel X .F4 2 1) : GriessAll.GriessRow X .F4 0 2 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact GriessClassical.of_mulEquiv e (row_of_card_prime (ℓ := 2) rfl rfl
    (hperf K (by rw [hK]; norm_num)) (hcard K (by rw [hK]; norm_num)))

section TauCeti

theorem g2_three_row_of_card
    (hcard : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) = 3)
    (hperf : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
      commutator (AdjointQuotient .G2 K) = ⊤)
    (hmodel : CFSG.Models.LieModel X .G2 0 3 1) : GriessAll.GriessRow X .G2 0 3 1 := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | G2 q =>
      have hp : q.p = 3 := by have := hd.1; omega
      have hf : q.exponent = 1 := by have := hd.2; omega
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact GaloisField.card _ _ q.exponent_pos.ne'
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv
        (GaloisField q.p q.exponent) hK
      have hK3 : Nat.card (GaloisField q.p q.exponent) = 3 := by
        rw [hK, TauCeti.PrimePower.card_def, hp, hf, pow_one]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact GriessClassical.of_mulEquiv (e.trans b.symm)
        (row_of_card_prime (ℓ := 3) rfl rfl (hperf _ hK3) (hcard _ hK3))
    | _ => simp [CFSG.Models.NamesTag] at hd

theorem g2_four_row_of_card
    (hcard : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) = 2)
    (hperf : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
      commutator (AdjointQuotient .G2 K) = ⊤)
    (hmodel : CFSG.Models.LieModel X .G2 0 2 2) : GriessAll.GriessRow X .G2 0 2 2 := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | G2 q =>
      have hp : q.p = 2 := by have := hd.1; omega
      have hf : q.exponent = 2 := by have := hd.2; omega
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact GaloisField.card _ _ q.exponent_pos.ne'
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv
        (GaloisField q.p q.exponent) hK
      have hK4 : Nat.card (GaloisField q.p q.exponent) = 4 := by
        rw [hK, TauCeti.PrimePower.card_def, hp, hf]
        norm_num
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact GriessClassical.of_mulEquiv (e.trans b.symm)
        (row_of_card_prime (ℓ := 2) rfl rfl (hperf _ hK4) (hcard _ hK4))
    | _ => simp [CFSG.Models.NamesTag] at hd

theorem f4_two_row_of_card
    (hcard : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) = 2)
    (hperf : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      commutator (AdjointQuotient .F4 K) = ⊤)
    (hmodel : CFSG.Models.LieModel X .F4 0 2 1) : GriessAll.GriessRow X .F4 0 2 1 := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | F4 q =>
      have hp : q.p = 2 := by have := hd.1; omega
      have hf : q.exponent = 1 := by have := hd.2; omega
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact GaloisField.card _ _ q.exponent_pos.ne'
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv
        (GaloisField q.p q.exponent) hK
      have hK2 : Nat.card (GaloisField q.p q.exponent) = 2 := by
        rw [hK, TauCeti.PrimePower.card_def, hp, hf, pow_one]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact GriessClassical.of_mulEquiv (e.trans b.symm)
        (row_of_card_prime (ℓ := 2) rfl rfl (hperf _ hK2) (hcard _ hK2))
    | _ => simp [CFSG.Models.NamesTag] at hd

end TauCeti

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
