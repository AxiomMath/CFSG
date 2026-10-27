module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GroupTheory.WeirSylow

theorem exists_units_orderOf_eq {L : Type*} [Field L] [Finite L] {d : ℕ}
    (hd : d ∣ Nat.card L - 1) : ∃ ζ : Lˣ, orderOf ζ = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Lˣ)
  rw [Nat.card_units] at hg
  have hpos : 0 < Nat.card L - 1 := by
    have := Finite.one_lt_card (α := L)
    omega
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hpos
  refine ⟨g ^ ((Nat.card L - 1) / d), ?_⟩
  rw [orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd hpos hd) hd0).ne'
    (by rw [hg]; exact Nat.div_dvd_of_dvd hd), hg, Nat.div_div_self hd hpos.ne']

theorem exists_injective_hom_of_orderOf_eq {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ H) {n : ℕ} [NeZero n] (hn : orderOf g = n) :
    ∃ ρ : Multiplicative (ZMod n) →* H, Function.Injective ρ := by
  have hcard : Nat.card (Multiplicative (ZMod n)) = Nat.card (Subgroup.zpowers g) := by
    rw [Nat.card_zpowers, hn, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let e := mulEquivOfCyclicCardEq hcard
  exact ⟨(Subgroup.inclusion (Subgroup.zpowers_le.2 hg)).comp e.toMonoidHom,
    (Subgroup.inclusion_injective (Subgroup.zpowers_le.2 hg)).comp e.injective⟩

theorem orderOf_toModuleAut (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (u : Lˣ) : orderOf (DistribMulAction.toModuleAut K L u) = orderOf u := by
  refine orderOf_injective _ (fun u v h => ?_) u
  have := LinearEquiv.congr_fun h 1
  change u • (1 : L) = v • (1 : L) at this
  rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at this
  exact Units.ext this

end CFSG.GroupTheory.WeirSylow
