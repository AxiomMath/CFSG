module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenHypEx
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem four_le_card_hypPart [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (E H : Subgroup (MulAut V))
    [Fintype ↥E] (hoddE : Odd (Fintype.card ↥E)) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hHE : H ≤ E) (hne : hypPart E H ≠ ⊥) : 4 ≤ Nat.card (hypPart E H) := by
  classical
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hex : ∃ e ∈ E, e (w : V) ≠ w := by
    by_contra hcon
    push Not at hcon
    have hmem : (w : V) ∈ (normK E).ker ⊓ fixV E := ⟨w.2.2, fun e he => hcon e he⟩
    rw [normK_ker_inf_fixV E hoddE hV] at hmem
    exact hw1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
  obtain ⟨e, heE, hew⟩ := hex
  have hmem : e (w : V) ∈ hypPart E H := by
    refine ⟨fun h hh => ?_, ?_⟩
    · have h1 : h * e = e * h := hcomm h (hHE hh) e heE
      show (h * e) (w : V) = e (w : V)
      rw [h1]
      show e (h (w : V)) = e (w : V)
      rw [w.2.1 h hh]
    · show normK E (e (w : V)) = 1
      rw [normK_apply_mem E heE]
      exact w.2.2
  set w' : ↥(hypPart E H) := ⟨e (w : V), hmem⟩ with hw'
  have h1w' : w' ≠ 1 := fun h => hw1 (by
    have h2 : e (w : V) = 1 := congrArg Subtype.val h
    exact Subtype.ext ((MulEquiv.map_eq_one_iff e).mp h2))
  have hww' : w ≠ w' := fun h => hew (congrArg Subtype.val h).symm
  have hcard3 : 3 ≤ Nat.card (hypPart E H) := by
    have hs : ({1, w, w'} : Finset ↥(hypPart E H)).card = 3 :=
      Finset.card_eq_three.mpr ⟨1, w, w', hw1.symm, h1w'.symm, hww', rfl⟩
    have : Fintype ↥(hypPart E H) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, ← hs]
    exact Finset.card_le_univ _
  have hpg : IsPGroup 2 ↥(hypPart E H) := fun g => ⟨1, Subtype.ext (by
    simpa [Subgroup.coe_pow] using hV g.1)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  rw [hn] at hcard3 ⊢
  by_contra hlt
  push Not at hlt
  have hn1 : n ≤ 1 := by
    by_contra h
    push Not at h
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases n <;> omega

theorem exists_stable_hyperplane [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (E : Subgroup (MulAut V))
    [Fintype ↥E] (hoddE : Odd (Fintype.card ↥E)) {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ e ∈ E, e ^ p = 1) (hE : E ≠ ⊥)
    (S : Set (MulAut V)) (hSN : ∀ x ∈ S, x ∈ Subgroup.normalizer (E : Set (MulAut V)))
    (hS : ∀ x ∈ S, x ^ 5 = 1 ∧ Nat.card (commV (Subgroup.zpowers x)) ≤ 16) :
    ∃ H ≤ E, Nat.card E = p * Nat.card H ∧ ∀ x ∈ S, hypConj x H = H := by
  obtain ⟨H, hHE, hHc, hHne⟩ := exists_hyperplane_hypPart_ne_bot hV E hoddE hp hpodd hcomm hexp hE
  refine ⟨H, hHE, hHc, fun x hx => ?_⟩
  by_contra hne
  have hoddH : Odd (Nat.card ↥H) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le hHE)
    rwa [Nat.card_eq_fintype_card]
  have h1 := card_hypPart_pow_le hV E H hoddE hcomm hHE hp hHc hoddH (hSN x hx) Nat.prime_five
    (hS x hx).1 hne
  have h2 := four_le_card_hypPart hV E H hoddE hcomm hHE hHne
  have h3 := (hS x hx).2
  have h4 : 4 ^ 4 ≤ Nat.card (hypPart E H) ^ 4 := Nat.pow_le_pow_left h2 4
  norm_num at h1 h4
  omega

end CFSG.CGT.PushingUpLit.CGT6
