module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBICover
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Blueprint.Multiplier
open scoped commutatorElement

theorem lbi_isPGroup_of_exp {G : Type} [Group G] (K : Subgroup G) (h3 : ∀ w ∈ K, w ^ 3 = 1) :
    IsPGroup 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (h3 g g.2))
  rcases (Nat.dvd_prime Nat.prime_three).1 hg with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem lbi_card_dvd_three {G : Type} [Group G] [Finite G] (K : Subgroup G) (hp : IsPGroup 3 K)
    (hd : Nat.card K ∣ 48) : Nat.card K ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  rw [hk] at hd ⊢
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> norm_num
  · exfalso
    have h9 : 9 ∣ 48 := (pow_dvd_pow 3 h : 3 ^ 2 ∣ 3 ^ k).trans hd
    omega

theorem lbi_bound_of_hopf {X : Type} [Group X] {A : Type} [Group A] [Finite A]
    (e : griessHopfMultiplier X ≃* A) (hA : Nat.card A ∣ 48) :
    ∀ (P : Type) [Group P] [Finite P] (η : P →* X), Function.Surjective η →
      η.ker ≤ Subgroup.center P → commutator P = ⊤ → IsPGroup 3 η.ker →
        Nat.card η.ker ∣ 3 := by
  intro P _ _ η hη hcen hperf hp
  exact lbi_card_dvd_three _ hp ((lbi_card_ker_dvd η hη hcen hperf e).trans hA)

theorem lbi_dichotomy {Y X S : Type} [Group Y] [Finite Y] [Group X] [Group S] [Finite S]
    (π : Y →* X) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center Y)
    (hperf : commutator Y = ⊤) (h3 : IsPGroup 3 π.ker)
    (θ : S →* X) (hθ : Function.Surjective θ) (hcenθ : θ.ker ≤ Subgroup.center S)
    (hperfS : commutator S = ⊤) (hθ3 : ∀ w ∈ θ.ker, w ^ 3 = 1) (hθne : ∃ w ∈ θ.ker, w ≠ 1)
    (hbound : ∀ (P : Type) [Group P] [Finite P] (η : P →* X), Function.Surjective η →
      η.ker ≤ Subgroup.center P → commutator P = ⊤ → IsPGroup 3 η.ker →
        Nat.card η.ker ∣ 3) :
    π.ker = ⊥ ∨ Nonempty (Y ≃* S) := by
  have hd : Nat.card π.ker ∣ 3 := hbound Y π hπ hcen hperf h3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · left
    have : Subsingleton π.ker := (Nat.card_eq_one_iff_unique.1 h).1
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    exact congrArg Subtype.val (Subsingleton.elim (⟨y, hy⟩ : π.ker) 1)
  · right
    exact lbi_cover_equiv π hπ hcen hperf h θ hθ hcenθ hperfS hθ3 hθne
      fun P _ _ η hη hc hp hexp => hbound P η hη hc hp (lbi_isPGroup_of_exp _ hexp)

section Table

theorem lbi_card_gen_exc (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (h1 : (genericOrders t n p f).1 ≠ 0) (h2 : (genericOrders t n p f).2 ≠ 0)
    (h3 : (exceptionalOrders t n p f).1 ≠ 0) (h4 : (exceptionalOrders t n p f).2 ≠ 0) :
    Nat.card (generic t n p f × exceptional t n p f) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  have a1 : NeZero (genericOrders t n p f).1 := ⟨h1⟩
  have a2 : NeZero (genericOrders t n p f).2 := ⟨h2⟩
  have a3 : NeZero (exceptionalOrders t n p f).1 := ⟨h3⟩
  have a4 : NeZero (exceptionalOrders t n p f).2 := ⟨h4⟩
  simp [generic, exceptional, mul_assoc]

theorem lbi_card_table_L3 (p f : ℕ) :
    Finite (generic .PSL 3 p f × exceptional .PSL 3 p f) ∧
      Nat.card (generic .PSL 3 p f × exceptional .PSL 3 p f) ∣ 48 := by
  have hg : genericOrders .PSL 3 p f = (Nat.gcd 3 (p ^ f - 1), 1) := by simp [genericOrders]
  have he : exceptionalOrders .PSL 3 p f =
      (if p = 2 ∧ f = 1 then (2, 1) else if p = 2 ∧ f = 2 then (4, 4) else (1, 1)) := by
    unfold exceptionalOrders
    split_ifs <;> simp_all
  have hgcd : Nat.gcd 3 (p ^ f - 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have hgpos : Nat.gcd 3 (p ^ f - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hexc : (exceptionalOrders .PSL 3 p f).1 ≠ 0 ∧ (exceptionalOrders .PSL 3 p f).2 ≠ 0 ∧
      (exceptionalOrders .PSL 3 p f).1 * (exceptionalOrders .PSL 3 p f).2 ∣ 16 := by
    rw [he]
    split_ifs <;> simp
  have hc := lbi_card_gen_exc .PSL 3 p f (by rw [hg]; exact hgpos) (by rw [hg]; simp) hexc.1 hexc.2.1
  refine ⟨?_, ?_⟩
  · refine Nat.finite_of_card_ne_zero ?_
    rw [hc, hg]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero hgpos one_ne_zero)
      (Nat.mul_ne_zero hexc.1 hexc.2.1)
  · rw [hc, hg]
    simp only [mul_one]
    exact (mul_dvd_mul hgcd hexc.2.2).trans (by norm_num)

theorem lbi_card_table_U3 (p f : ℕ) :
    Finite (generic .PSU 3 p f × exceptional .PSU 3 p f) ∧
      Nat.card (generic .PSU 3 p f × exceptional .PSU 3 p f) ∣ 48 := by
  have hg : genericOrders .PSU 3 p f = (Nat.gcd 3 (p ^ f + 1), 1) := by simp [genericOrders]
  have he : exceptionalOrders .PSU 3 p f = (1, 1) := by simp [exceptionalOrders]
  have hgcd : Nat.gcd 3 (p ^ f + 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have hgpos : Nat.gcd 3 (p ^ f + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hc := lbi_card_gen_exc .PSU 3 p f (by rw [hg]; exact hgpos) (by rw [hg]; simp)
    (by rw [he]; simp) (by rw [he]; simp)
  refine ⟨?_, ?_⟩
  · refine Nat.finite_of_card_ne_zero ?_
    rw [hc, hg, he]
    simp [hgpos]
  · rw [hc, hg, he]
    simp only [mul_one]
    exact hgcd.trans (by norm_num)

end Table

theorem lbi_main_aux {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (h3 : IsPGroup 3 (Subgroup.center Y))
    {S : Type} [Group S] [Finite S] (θ : S →* Y ⧸ Subgroup.center Y)
    (hθ : Function.Surjective θ) (hcenθ : θ.ker ≤ Subgroup.center S)
    (hperfS : commutator S = ⊤) (hθ3 : ∀ w ∈ θ.ker, w ^ 3 = 1) (hθne : ∃ w ∈ θ.ker, w ≠ 1)
    {A : Type} [Group A] [Finite A] (e : griessHopfMultiplier (Y ⧸ Subgroup.center Y) ≃* A)
    (hA : Nat.card A ∣ 48) :
    Subgroup.center Y = ⊥ ∨ Nonempty (Y ≃* S) := by
  have hker : (QuotientGroup.mk' (Subgroup.center Y)).ker = Subgroup.center Y :=
    QuotientGroup.ker_mk' _
  have h3' : IsPGroup 3 (QuotientGroup.mk' (Subgroup.center Y)).ker := by
    rw [hker]; exact h3
  have := lbi_dichotomy (QuotientGroup.mk' (Subgroup.center Y)) (QuotientGroup.mk'_surjective _)
    (by rw [hker]) hq.1 h3' θ hθ hcenθ hperfS hθ3 hθne (lbi_bound_of_hopf e hA)
  rwa [hker] at this

end CFSG.HardMathSupport.Solomon.Coordinator
