module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.List.GetD

public section

namespace CFSG.GroupTheory.WeirSylow

universe u

@[expose] def wreathTowerBundle (p : ℕ) (P : Type u) [Group P] : ℕ → Σ T : Type u, Group T
  | 0 => ⟨P, inferInstance⟩
  | i + 1 =>
    letI := (wreathTowerBundle p P i).2
    ⟨(wreathTowerBundle p P i).1 ≀ᵣ Multiplicative (ZMod p), inferInstance⟩

@[expose] def wreathTower (p : ℕ) (P : Type u) [Group P] (i : ℕ) : Type u :=
  (wreathTowerBundle p P i).1

instance instGroupWreathTower (p : ℕ) (P : Type u) [Group P] (i : ℕ) :
    Group (wreathTower p P i) :=
  (wreathTowerBundle p P i).2

theorem wreathTower_zero (p : ℕ) (P : Type u) [Group P] : wreathTower p P 0 = P :=
  rfl

theorem wreathTower_succ (p : ℕ) (P : Type u) [Group P] (i : ℕ) :
    wreathTower p P (i + 1) = (wreathTower p P i ≀ᵣ Multiplicative (ZMod p)) :=
  rfl

instance instFiniteWreathTower (p : ℕ) [NeZero p] (P : Type u) [Group P] [Finite P] :
    (i : ℕ) → Finite (wreathTower p P i)
  | 0 => inferInstanceAs (Finite P)
  | i + 1 =>
    letI := instFiniteWreathTower p P i
    inferInstanceAs (Finite (wreathTower p P i ≀ᵣ Multiplicative (ZMod p)))

@[expose] def towerExp (p a : ℕ) : ℕ → ℕ
  | 0 => a
  | i + 1 => p * towerExp p a i + 1

theorem towerExp_zero (p a : ℕ) : towerExp p a 0 = a :=
  rfl

theorem towerExp_succ (p a i : ℕ) : towerExp p a (i + 1) = p * towerExp p a i + 1 :=
  rfl

theorem towerExp_succ' (p a : ℕ) : ∀ i, towerExp p a (i + 1) = towerExp p (p * a + 1) i
  | 0 => rfl
  | i + 1 => by rw [towerExp_succ, towerExp_succ' p a i, towerExp_succ]

theorem card_wreathTower (p : ℕ) [NeZero p] (P : Type u) [Group P] [Finite P] {a : ℕ}
    (hP : Nat.card P = p ^ a) : ∀ i, Nat.card (wreathTower p P i) = p ^ towerExp p a i
  | 0 => hP
  | i + 1 => by
    change Nat.card (wreathTower p P i ≀ᵣ Multiplicative (ZMod p)) = _
    rw [RegularWreathProduct.card, card_wreathTower p P hP i, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card, towerExp_succ, ← pow_mul, pow_succ, mul_comm p]

@[expose] def sigmaModel (p e a N : ℕ) : Type :=
  (i : Fin (Nat.digits p (N / e)).length) →
    Fin (Nat.digits p (N / e))[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) i

instance instGroupSigmaModel (p e a N : ℕ) : Group (sigmaModel p e a N) :=
  inferInstanceAs (Group ((i : Fin (Nat.digits p (N / e)).length) →
    Fin (Nat.digits p (N / e))[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) i))

instance instFiniteSigmaModel (p : ℕ) [NeZero p] (e a N : ℕ) : Finite (sigmaModel p e a N) :=
  have : NeZero (p ^ a) := ⟨pow_ne_zero a (NeZero.ne p)⟩
  inferInstanceAs (Finite ((i : Fin (Nat.digits p (N / e)).length) →
    Fin (Nat.digits p (N / e))[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) i))

@[expose] def digitTowerSum (p : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | d :: L, a => d * a + digitTowerSum p L (p * a + 1)

theorem digitTowerSum_eq_sum (p : ℕ) : ∀ (L : List ℕ) (a : ℕ),
    digitTowerSum p L a = ∑ i ∈ Finset.range L.length, L.getD i 0 * towerExp p a i
  | [], _ => by simp [digitTowerSum]
  | d :: L, a => by
    rw [digitTowerSum, List.length_cons, Finset.sum_range_succ', digitTowerSum_eq_sum p L]
    simp only [List.getD_cons_zero, towerExp_zero, List.getD_cons_succ, towerExp_succ']
    rw [add_comm]

theorem mul_digitTowerSum_add_sum (k : ℕ) : ∀ (L : List ℕ) (a : ℕ),
    k * digitTowerSum (k + 1) L a + L.sum =
      k * a * Nat.ofDigits (k + 1) L + Nat.ofDigits (k + 1) L
  | [], _ => by simp [digitTowerSum]
  | d :: L, a => by
    have ih := mul_digitTowerSum_add_sum k L ((k + 1) * a + 1)
    rw [digitTowerSum, Nat.ofDigits_cons, List.sum_cons]
    have : ((k + 1 : ℕ) : ℕ) = k + 1 := rfl
    nlinarith [ih]

theorem digitTowerSum_digits (p : ℕ) [hp : Fact p.Prime] (a m : ℕ) :
    digitTowerSum p (Nat.digits p m) a = a * m + padicValNat p m.factorial := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have hk0 : 0 < k := by have := hp.out.one_lt; omega
  have h1 := mul_digitTowerSum_add_sum k (Nat.digits p m) a
  have h2 := sub_one_mul_padicValNat_factorial (p := p) m
  rw [← hk, Nat.ofDigits_digits] at h1
  rw [show p - 1 = k by omega] at h2
  have hle := Nat.digit_sum_le p m
  refine Nat.eq_of_mul_eq_mul_left hk0 ?_
  have h3 : k * (a * m + padicValNat p m.factorial) = k * a * m + (m - (Nat.digits p m).sum) := by
    rw [mul_add, ← h2, mul_assoc]
  rw [h3]
  omega

theorem card_sigmaModel (p : ℕ) [hp : Fact p.Prime] (e a N : ℕ) :
    Nat.card (sigmaModel p e a N) =
      p ^ (a * (N / e) + padicValNat p (N / e).factorial) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero a hp.out.ne_zero⟩
  have hC : Nat.card (Multiplicative (ZMod (p ^ a))) = p ^ a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  change Nat.card ((i : Fin (Nat.digits p (N / e)).length) →
    Fin (Nat.digits p (N / e))[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) i) = _
  rw [Nat.card_pi]
  simp only [Nat.card_fun, Nat.card_fin, card_wreathTower p _ hC]
  rw [← digitTowerSum_digits p a (N / e), digitTowerSum_eq_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_mul, mul_comm, List.getD_eq_getElem _ _ i.2]
  rfl

end CFSG.GroupTheory.WeirSylow
