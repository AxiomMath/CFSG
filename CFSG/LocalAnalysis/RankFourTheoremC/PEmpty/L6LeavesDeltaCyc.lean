module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
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
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6Delta

theorem exists_coatom_not_mem_of_not_mem_frattini {G : Type} [Group G] {g : G}
    (hg : g ∉ frattini G) : ∃ D : Subgroup G, IsCoatom D ∧ g ∉ D := by
  by_contra hcon
  push Not at hcon
  apply hg
  unfold frattini Order.radical
  exact Subgroup.mem_iInf.mpr fun D => Subgroup.mem_iInf.mpr fun hD => hcon D hD

theorem card_inf_eq_prime {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (Bx D : Subgroup G) (hBx : Nat.card Bx = p ^ 2) (hDp : IsPGroup p D)
    (hDn : D ≠ ⊥) (hΩ : ∀ g ∈ D, g ^ p = 1 → g ∈ Bx) (hnot : ∃ b ∈ Bx, b ∉ D) :
    Nat.card ↥(Bx ⊓ D) = p := by
  have hD1 : Nat.card D ≠ 1 := fun h1 => hDn (Subgroup.card_eq_one.mp h1)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hDp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hD1 (by rw [hk, pow_zero])
  have hpd : p ∣ Nat.card D := by
    rw [hk]
    exact dvd_pow_self p hk0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := D) p hpd
  have hgD : (g : G) ∈ D := g.2
  have hgp : (g : G) ^ p = 1 := by
    have h1 : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    simpa using congrArg Subtype.val h1
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    exact hp.out.one_lt.ne' hg.symm
  have hWne : Bx ⊓ D ≠ ⊥ := by
    intro hbot
    have hmem : (g : G) ∈ Bx ⊓ D := ⟨hΩ _ hgD hgp, hgD⟩
    rw [hbot] at hmem
    exact hg1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
  have hdvd := Subgroup.card_dvd_of_le (inf_le_left : Bx ⊓ D ≤ Bx)
  rw [hBx] at hdvd
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
  have hne1 : Nat.card ↥(Bx ⊓ D) ≠ 1 := fun h1 => hWne (Subgroup.card_eq_one.mp h1)
  have hne2 : Nat.card ↥(Bx ⊓ D) ≠ p ^ 2 := by
    intro h2
    obtain ⟨b, hb, hbD⟩ := hnot
    apply hbD
    have heq : Bx ⊓ D = Bx :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hBx, h2]))
    have hb' : b ∈ Bx ⊓ D := by
      rw [heq]
      exact hb
    exact hb'.2
  interval_cases i
  · exact absurd (hcard.trans (pow_zero p)) hne1
  · rw [hcard, pow_one]
  · exact absurd hcard hne2

theorem isCyclic_of_pow_eq_one_mem {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hGp : IsPGroup p G) (U₀ : Subgroup G) (hU₀ : Nat.card U₀ = p)
    (hsub : ∀ g : G, g ^ p = 1 → g ∈ U₀) : IsCyclic G := by
  refine (CFSG.BenderSuzuki.External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
    hp.out hGp ⟨U₀, hU₀, ?_⟩).1 hp2
  intro V hV
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV
    exact hp.out.one_lt.ne' hV.symm
  obtain ⟨v, hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hordV : orderOf v = p := by
    have hd : orderOf v ∣ p := by
      have := orderOf_dvd_natCard v
      rwa [hV] at this
    rcases (Nat.dvd_prime hp.out).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hv
    · exact h1
  have hvp : (v : G) ^ p = 1 := by
    have h1 : v ^ p = 1 := by rw [← hordV]; exact pow_orderOf_eq_one v
    simpa using congrArg Subtype.val h1
  have hcardz : Nat.card (Subgroup.zpowers (v : G)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hordV]
  have hzV : Subgroup.zpowers (v : G) ≤ V := Subgroup.zpowers_le.mpr v.2
  have hzeq : Subgroup.zpowers (v : G) = V :=
    Subgroup.eq_of_le_of_card_ge hzV (le_of_eq (hV.trans hcardz.symm))
  have hVU : V ≤ U₀ := by
    rw [← hzeq]
    exact Subgroup.zpowers_le.mpr (hsub _ hvp)
  exact Subgroup.eq_of_le_of_card_ge hVU (le_of_eq (hU₀.trans hV.symm))

theorem comm_of_isCyclic {G : Type} [Group G] [IsCyclic G] (a b : G) : a * b = b * a := by
  letI : CommGroup G := IsCyclic.commGroup
  exact mul_comm a b

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6Delta
