module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace Burnside.GroupEndgame

universe u

private theorem dvd_prime_pow_mul_prime_pow {p q a b d : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hd : d ∣ p ^ a * q ^ b) :
    ∃ c ≤ a, ∃ e ≤ b, d = p ^ c * q ^ e := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hdeq⟩ := (Nat.dvd_mul.mp hd)
  obtain ⟨c, hc, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd₁
  obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow hq).mp hd₂
  exact ⟨c, hc, e, he, hdeq.symm⟩

private theorem exists_nonidentity_conjClass_card_eq_prime_pow
    {H : Type u} [Group H] [Fintype H] {r s m e : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hm : 0 < m)
    (hcard : Nat.card H = r ^ m * s ^ e) :
    ∃ x : H, x ≠ 1 ∧ ∃ k ≤ e,
      Nat.card (ConjClasses.mk x).carrier = s ^ k := by
  let : Fact (Nat.Prime r) := ⟨hr⟩
  let P : Sylow r H := Classical.choice inferInstance
  have hrpow_dvd_H : r ^ m ∣ Nat.card H := ⟨s ^ e, hcard⟩
  have hrpow_dvd_P : r ^ m ∣ Nat.card P :=
    P.pow_dvd_card_of_pow_dvd_card hrpow_dvd_H
  have hPcard : 1 < Nat.card P :=
    lt_of_lt_of_le (Nat.one_lt_pow (Nat.ne_of_gt hm) hr.one_lt)
      (Nat.le_of_dvd Nat.card_pos hrpow_dvd_P)
  let : Nontrivial P := (Finite.one_lt_card_iff_nontrivial).mp hPcard
  let : Nontrivial (Subgroup.center P) := P.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  let x : H := z.1.1
  have hx : x ≠ 1 := by
    intro hx1
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact hx1
  have hP_le : (P : Subgroup H) ≤ Subgroup.centralizer {x} := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst w
    have hcomm := (Subgroup.mem_center_iff.mp z.property) ⟨y, hy⟩
    change z.1.1 * y = y * z.1.1
    exact (congrArg Subtype.val hcomm).symm
  have hrpow_dvd_centralizer :
      r ^ m ∣ Nat.card (Subgroup.centralizer {x}) :=
    hrpow_dvd_P.trans (Subgroup.card_dvd_of_le hP_le)
  have hrpow_dvd_stabilizer :
      r ^ m ∣ Nat.card (MulAction.stabilizer (ConjAct H) x) := by
    rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer x]
    exact hrpow_dvd_centralizer
  obtain ⟨t, ht⟩ := hrpow_dvd_stabilizer
  let : Fintype (MulAction.orbit (ConjAct H) x) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer (ConjAct H) x) := Fintype.ofFinite _
  have horbit_mul :
      Nat.card (MulAction.orbit (ConjAct H) x) *
        Nat.card (MulAction.stabilizer (ConjAct H) x) = Nat.card H := by
    simpa only [Nat.card_eq_fintype_card, ConjAct.card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct H) x
  have hcancel :
      r ^ m * (Nat.card (MulAction.orbit (ConjAct H) x) * t) =
        r ^ m * s ^ e := by
    calc
      r ^ m * (Nat.card (MulAction.orbit (ConjAct H) x) * t) =
          Nat.card (MulAction.orbit (ConjAct H) x) * (r ^ m * t) := by
            ac_rfl
      _ = Nat.card H := by rw [← ht]; exact horbit_mul
      _ = r ^ m * s ^ e := hcard
  have horbit_times_t :
      Nat.card (MulAction.orbit (ConjAct H) x) * t = s ^ e :=
    (Nat.mul_right_inj (pow_ne_zero m hr.ne_zero)).mp hcancel
  obtain ⟨k, hk, horbit⟩ := (Nat.dvd_prime_pow hs).mp
    (show Nat.card (MulAction.orbit (ConjAct H) x) ∣ s ^ e from
      ⟨t, horbit_times_t.symm⟩)
  refine ⟨x, hx, k, hk, ?_⟩
  rw [← ConjAct.orbit_eq_carrier_conjClasses x]
  exact horbit

theorem isSolvable_of_card_eq_prime_pow_mul_prime_pow_of_simple_case
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (simple_case : ∀ (H : Type u) [Group H] [Fintype H] (c e : ℕ),
      Nat.card H = p ^ c * q ^ e → IsSimpleGroup H → Group.IsSolvable H) :
    ∀ (G : Type u) [Group G] [Fintype G] (a b : ℕ),
      Nat.card G = p ^ a * q ^ b → Group.IsSolvable G := by
  intro G _ _ a b hcard
  let P : ℕ → Prop := fun n => ∀ (H : Type u) [Group H] [Fintype H] (c e : ℕ),
    Nat.card H = n → n = p ^ c * q ^ e → Group.IsSolvable H
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H _ _ c e hHcard hn
      by_cases hsimple : IsSimpleGroup H
      · exact simple_case H c e (hHcard.trans hn) hsimple
      · by_cases hnontrivial : Nontrivial H
        · rw [isSimpleGroup_iff] at hsimple
          simp only [hnontrivial, true_and] at hsimple
          push Not at hsimple
          obtain ⟨N, hNnormal, hNbot, hNtop⟩ := hsimple
          let : N.Normal := hNnormal
          let : Fintype N := Fintype.ofFinite N
          let : Fintype (H ⧸ N) := Fintype.ofFinite (H ⧸ N)
          have hNcard_lt : Nat.card N < n := by
            rw [← hHcard]
            exact lt_of_le_of_ne (N.card_le_card_group)
              (fun heq => hNtop (N.eq_top_of_le_card heq.ge))
          have hQcard_lt : Nat.card (H ⧸ N) < n := by
            rw [← hHcard]
            rw [N.card_eq_card_quotient_mul_card_subgroup]
            exact (Nat.lt_mul_iff_one_lt_right Nat.card_pos).2
              ((N.one_lt_card_iff_ne_bot).2 hNbot)
          obtain ⟨cN, -, eN, -, hNcard⟩ :=
            dvd_prime_pow_mul_prime_pow hp hq
              ((hHcard.trans hn) ▸ N.card_subgroup_dvd_card)
          obtain ⟨cQ, -, eQ, -, hQcard⟩ :=
            dvd_prime_pow_mul_prime_pow hp hq
              ((hHcard.trans hn) ▸ N.card_quotient_dvd_card)
          have hsN : Group.IsSolvable N :=
            ih (Nat.card N) hNcard_lt N cN eN rfl hNcard
          have hsQ : Group.IsSolvable (H ⧸ N) :=
            ih (Nat.card (H ⧸ N)) hQcard_lt (H ⧸ N) cQ eQ rfl hQcard
          exact (Group.isSolvable_iff_subgroup_quotient N).2 ⟨hsN, hsQ⟩
        · have : Subsingleton H := not_nontrivial_iff_subsingleton.mp hnontrivial
          exact Group.isSolvable_of_comm fun _ _ => Subsingleton.elim _ _
  exact hP (Nat.card G) G a b rfl hcard

theorem isSolvable_of_card_eq_prime_pow_mul_prime_pow_of_no_prime_pow_conjClass
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (no_prime_pow_conjClass :
      ∀ (H : Type u) [Group H] [Fintype H],
        IsSimpleGroup H →
        (¬ ∀ x y : H, x * y = y * x) →
        ∀ (x : H), x ≠ 1 → ∀ (r k : ℕ), Nat.Prime r →
          Nat.card (ConjClasses.mk x).carrier ≠ r ^ k) :
    ∀ (G : Type u) [Group G] [Fintype G] (a b : ℕ),
      Nat.card G = p ^ a * q ^ b → Group.IsSolvable G := by
  apply isSolvable_of_card_eq_prime_pow_mul_prime_pow_of_simple_case hp hq
  intro H _ _ c e hcard hsimple
  by_cases hcomm : ∀ x y : H, x * y = y * x
  · exact Group.isSolvable_of_comm hcomm
  · exfalso
    let : IsSimpleGroup H := hsimple
    have hcard_one_lt : 1 < Nat.card H :=
      (Finite.one_lt_card_iff_nontrivial).2 inferInstance
    by_cases hc : c = 0
    · have he : 0 < e := by
        by_contra he
        have he0 : e = 0 := Nat.eq_zero_of_not_pos he
        rw [hcard, hc, he0] at hcard_one_lt
        simp at hcard_one_lt
      obtain ⟨x, hx, k, -, hk⟩ :=
        exists_nonidentity_conjClass_card_eq_prime_pow hq hp he
          (hcard.trans (Nat.mul_comm _ _))
      exact (no_prime_pow_conjClass H hsimple hcomm x hx p k hp) hk
    · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
      obtain ⟨x, hx, k, -, hk⟩ :=
        exists_nonidentity_conjClass_card_eq_prime_pow hp hq hcpos hcard
      exact (no_prime_pow_conjClass H hsimple hcomm x hx q k hq) hk

end Burnside.GroupEndgame

end CFSG
