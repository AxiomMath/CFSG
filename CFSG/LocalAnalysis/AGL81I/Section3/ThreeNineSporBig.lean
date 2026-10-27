module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicTable
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveSteps

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.AGLEmbeddingD2 (d2SporadicOrder)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def MaxOrdersFullP (L : Type) [Group L] (q a : ℕ) (ns : List ℕ) : Prop :=
  ∀ M : Subgroup L, IsCoatom M → q ^ a ∣ Nat.card M → Nat.card M ∈ ns

@[expose] def NormOrderInMax (L : Type) [Group L] (n d b : ℕ) : Prop :=
  ∀ M : Subgroup L, IsCoatom M → Nat.card M = n → ∀ D : Subgroup L, D ≤ M → Nat.card D = d →
    Nat.card ↥(Subgroup.normalizer (D : Set L) ⊓ M) = b

@[expose] def NormOrder (L : Type) [Group L] (d b : ℕ) : Prop :=
  ∀ D : Subgroup L, Nat.card D = d → Nat.card (Subgroup.normalizer (D : Set L)) = b

@[expose] def LyG2Five (L : Type) [Group L] : Prop :=
  ∀ M : Subgroup L, IsCoatom M → Nat.card M = 5859000000 →
    IsSimpleGroup ↥M ∧ ChevalleyExceptionalModel ↥M .G2 5 1 ∧
      ∀ Y : Subgroup L, Y < M → ¬ 5 ^ 6 * 31 ∣ Nat.card Y

@[expose] def SporBigLocal : Prop :=
  ∀ (L : Type) [Group L] [Finite L],
    (Nonempty (L ≃* Carrier .Co1) → MaxOrdersFullP L 5 4 [60000]) ∧
    (Nonempty (L ≃* Carrier .HN) → MaxOrdersFullP L 5 6 [2000000, 750000]) ∧
    (Nonempty (L ≃* Carrier .M) → MaxOrdersFullP L 7 6 [508243680, 33882912]) ∧
    (Nonempty (L ≃* Carrier .Ly) →
      MaxOrdersFullP L 5 6 [5859000000, 46500000, 9000000] ∧
      NormOrderInMax L 5859000000 7 126 ∧ NormOrderInMax L 46500000 31 93 ∧
      NormOrder L 7 1008 ∧ NormOrder L 31 186 ∧ LyG2Five L) ∧
    (Nonempty (L ≃* Carrier .B) →
      MaxOrdersFullP L 5 6 [546061824000000, 46500000, 24000000] ∧
      NormOrderInMax L 546061824000000 11 440 ∧ NormOrderInMax L 546061824000000 19 342 ∧
      NormOrderInMax L 46500000 31 93 ∧
      NormOrder L 11 13200 ∧ NormOrder L 19 684 ∧ NormOrder L 31 465)

theorem eq_or_dvd_of_dvd_pow_mul {d q e m : ℕ} (hd : d.Prime) (hq : q.Prime)
    (h : d ∣ q ^ e * m) : d = q ∨ d ∣ m := by
  rcases hd.dvd_mul.1 h with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hd hq).1 (hd.dvd_of_dvd_pow h1))
  · exact Or.inr h1

theorem pow_dvd_of_factorization {q k n m : ℕ} (hq : q.Prime) (hn : n ≠ 0) (hk : q ^ k ∣ n)
    (h : q ^ n.factorization q ∣ m) : q ^ k ∣ m :=
  (pow_dvd_pow q ((hq.pow_dvd_iff_le_factorization hn).1 hk)).trans h

theorem not_dvd_of_le_two {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hn0 : n ≠ 0) (hn : n ≤ 2) :
    ¬ q ∣ n := fun h => by
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h
  have := hq.two_le
  omega

theorem not_pow_dvd_of_factorization {q e N m : ℕ} (hq : q.Prime) (hN : N ≠ 0) (he : q ^ e ∣ N)
    (hm : ¬ q ^ e ∣ m) (h : q ^ N.factorization q ∣ m) : False :=
  hm (pow_dvd_of_factorization hq hN he h)

theorem false_of_normOrder {L : Type} [Group L] {M D' : Subgroup L} {n d b b' : ℕ}
    (hM : IsCoatom M) (hMc : Nat.card M = n) (hD' : Nat.card D' = d)
    (hnorm : Subgroup.normalizer (D' : Set L) ≤ M)
    (h1 : NormOrderInMax L n d b) (h2 : NormOrder L d b') (hb : b ≠ b') : False := by
  have e1 := h1 M hM hMc D' (Subgroup.le_normalizer.trans hnorm) hD'
  rw [inf_eq_left.mpr hnorm, h2 D' hD'] at e1
  exact hb e1.symm

section Core

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

theorem card_D_eq (h : ThreeNineHyp K E D X₁ p d) (hDK : D ≤ K) (hd2 : ¬ d ^ 2 ∣ Nat.card ↥K) :
    Nat.card D = d := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_D
  have hdvd : d ^ k ∣ Nat.card ↥K := hk ▸ Subgroup.card_dvd_of_le hDK
  have hk1 : k ≤ 1 := by
    by_contra hk2
    exact hd2 ((pow_dvd_pow d (by omega : 2 ≤ k)).trans hdvd)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h.D_ne_bot (Subgroup.eq_bot_of_card_eq D (by rw [hk, pow_zero]))
  rw [hk, show k = 1 by omega, pow_one]

end Core

theorem mem_of_prime_dvd {d : ℕ} (hd : d.Prime) :
    ∀ {qs : List (ℕ × ℕ)}, (∀ x ∈ qs, x.1.Prime) → d ∣ (qs.map fun x => x.1 ^ x.2).prod →
      d ∈ qs.map Prod.fst
  | [], _, h => by
    simp only [List.map_nil, List.prod_nil, Nat.dvd_one] at h
    exact absurd h hd.one_lt.ne'
  | x :: t, hq, h => by
    simp only [List.map_cons, List.prod_cons] at h
    simp only [List.map_cons, List.mem_cons]
    rcases eq_or_dvd_of_dvd_pow_mul hd (hq x List.mem_cons_self) h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (mem_of_prime_dvd hd (fun y hy => hq y (List.mem_cons_of_mem _ hy)) h1)

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
