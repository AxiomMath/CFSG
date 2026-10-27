module

public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem card_generic_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  simp only [generic, exceptional, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _), Nat.card_zmod]

theorem card_center_dvd_card_hopfMultiplier {Q : Type} [Group Q] [Group.IsPerfect Q] :
    Nat.card (center Q) ∣
      Nat.card (RankThree.PerfectCover.hopfMultiplier (Q ⧸ center Q)) := by
  have hker : (QuotientGroup.mk' (center Q)).ker = center Q := QuotientGroup.ker_mk' _
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift (QuotientGroup.mk' (center Q))
    (QuotientGroup.mk'_surjective _) hker.le
  have h := Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier (Q ⧸ center Q))
    (RankThree.PerfectCover.hopfLift (QuotientGroup.mk' (center Q))
      (QuotientGroup.mk'_surjective _) hker.le)
  rw [hmap, hker] at h
  exact h

theorem card_center_dvd_table
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {t : StatedLieTag}
    {n ℓ f : ℕ} (hm : LieModel (K ⧸ center K) t n ℓ f) :
    Nat.card (center K) ∣ ((genericOrders t n ℓ f).1 * (genericOrders t n ℓ f).2) *
      ((exceptionalOrders t n ℓ f).1 * (exceptionalOrders t n ℓ f).2) := by
  have : Group.IsPerfect K := hK.1
  obtain ⟨-, ⟨e⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ t n ℓ f hm
  have h1 := card_center_dvd_card_hopfMultiplier (Q := K)
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
    Nat.card_congr e.toEquiv, card_generic_exceptional] at h1
  exact h1

theorem odd_prime_dvd_table {t : StatedLieTag} {n ℓ f r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hdvd : r ∣ ((genericOrders t n ℓ f).1 * (genericOrders t n ℓ f).2) *
      ((exceptionalOrders t n ℓ f).1 * (exceptionalOrders t n ℓ f).2)) :
    (t = .PSL ∧ r ∣ n ∧ r ∣ ℓ ^ f - 1) ∨ (t = .PSU ∧ r ∣ n ∧ r ∣ ℓ ^ f + 1) ∨
      (t = .E6 ∧ r = 3 ∧ 3 ∣ ℓ ^ f - 1) ∨ (t = .twistedE6 ∧ r = 3 ∧ 3 ∣ ℓ ^ f + 1) ∨
      (r = 3 ∧ ((t = .PSL ∧ n = 2 ∧ ℓ = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ ℓ = 3 ∧ f = 1) ∨
        (t = .G2 ∧ n = 0 ∧ ℓ = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ ℓ = 3 ∧ f = 1))) := by
  have hr1 : ¬ r ∣ 1 := hr.not_dvd_one
  have hr2' : ¬ r ∣ 2 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
  have hr4 : ¬ r ∣ 4 := fun h => hr2' (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 from h))
  have hgcd2 : ∀ x : ℕ, ¬ r ∣ Nat.gcd 2 x := fun x h => hr2' (h.trans (Nat.gcd_dvd_left 2 x))
  have hgcd4 : ∀ x : ℕ, ¬ r ∣ Nat.gcd 4 x := fun x h => hr4 (h.trans (Nat.gcd_dvd_left 4 x))
  have h3 : ∀ x : ℕ, r ∣ Nat.gcd 3 x → r = 3 ∧ 3 ∣ x := fun x h => by
    have e : r = 3 :=
      (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (h.trans (Nat.gcd_dvd_left 3 x))
    exact ⟨e, e ▸ h.trans (Nat.gcd_dvd_right 3 x)⟩
  have hr3 : r ∣ 3 → r = 3 := fun h => (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h
  rcases (Nat.Prime.dvd_mul hr).1 hdvd with hg | hex
  · rcases (Nat.Prime.dvd_mul hr).1 hg with hg | hg
    · unfold genericOrders at hg
      cases t <;> dsimp only at hg
      all_goals first
        | exact absurd hg hr1
        | exact absurd hg hr2'
        | exact absurd hg (hgcd2 _)
        | exact absurd hg (hgcd4 _)
        | exact Or.inl ⟨rfl, (Nat.dvd_gcd_iff.mp hg).1, (Nat.dvd_gcd_iff.mp hg).2⟩
        | exact Or.inr (Or.inl ⟨rfl, (Nat.dvd_gcd_iff.mp hg).1, (Nat.dvd_gcd_iff.mp hg).2⟩)
        | exact Or.inr (Or.inr (Or.inl ⟨rfl, (h3 _ hg).1, (h3 _ hg).2⟩))
        | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (h3 _ hg).1, (h3 _ hg).2⟩)))
        | (split_ifs at hg
           · exact absurd hg hr1
           · exact absurd hg hr2'
           · exact absurd hg (hgcd4 _))
    · unfold genericOrders at hg
      cases t <;> dsimp only at hg
      all_goals first
        | exact absurd hg hr1
        | (split_ifs at hg
           · exact absurd hg hr1
           · exact absurd hg hr2'
           · exact absurd hg hr1)
  · unfold exceptionalOrders at hex
    split at hex
    all_goals dsimp only at hex
    all_goals rcases (Nat.Prime.dvd_mul hr).1 hex with hx | hx
    all_goals first
      | exact absurd hx hr1
      | exact absurd hx hr2'
      | exact absurd hx hr4
      | (obtain rfl := hr3 hx; decide)

end CFSG.SectionRank.QTK.CoverB
