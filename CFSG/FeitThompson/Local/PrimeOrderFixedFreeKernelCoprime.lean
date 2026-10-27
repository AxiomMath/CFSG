module

public import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.Group
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open MulAction Subgroup Pointwise

variable {G : Type*} [Group G] {H R : Subgroup G} {p : ℕ}

def toConjActSubgroup (R : Subgroup G) : Subgroup (ConjAct G) :=
  R.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom

theorem mem_toConjActSubgroup_iff {x : ConjAct G} :
    x ∈ toConjActSubgroup R ↔ ConjAct.ofConjAct x ∈ R :=
  ⟨by rintro ⟨r, hr, rfl⟩; simpa using hr, fun h => ⟨_, h, rfl⟩⟩

theorem toConjAct_mem_toConjActSubgroup {r : G} (hr : r ∈ R) :
    ConjAct.toConjAct r ∈ toConjActSubgroup R :=
  mem_toConjActSubgroup_iff.mpr (by simpa using hr)

theorem natCard_toConjActSubgroup (R : Subgroup G) :
    Nat.card (toConjActSubgroup R) = Nat.card R :=
  (Nat.card_congr (R.equivMapOfInjective (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
    ConjAct.toConjAct.injective).toEquiv).symm

theorem fixedPoints_toConjActSubgroup [H.Normal] :
    fixedPoints (toConjActSubgroup R) H = {x : H | (x : G) ∈ centralizer (R : Set G)} := by
  ext x
  rw [Set.mem_ofPred_eq, mem_fixedPoints]
  simp only [mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hx r hr
    have h2 := congrArg (Subtype.val (p := fun y : G => y ∈ H))
      (hx ⟨ConjAct.toConjAct r, toConjAct_mem_toConjActSubgroup hr⟩)
    rw [Submonoid.mk_smul, ConjAct.Subgroup.val_conj_smul, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct] at h2
    calc r * (x : G) = r * (x : G) * r⁻¹ * r := by group
      _ = (x : G) * r := by rw [h2]
  · intro hx s
    have h := hx _ (mem_toConjActSubgroup_iff.mp s.2)
    ext
    change ConjAct.ofConjAct (s : ConjAct G) * (x : G) * (ConjAct.ofConjAct (s : ConjAct G))⁻¹
      = (x : G)
    rw [h, mul_inv_cancel_right]

theorem natCard_fixedPoints_toConjActSubgroup_eq_one [H.Normal]
    (hCH : H ⊓ centralizer (R : Set G) = ⊥) :
    Nat.card (fixedPoints (toConjActSubgroup R) H) = 1 := by
  have hfix : fixedPoints (toConjActSubgroup R) H = {1} := by
    rw [fixedPoints_toConjActSubgroup]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun hx => ?_, fun hx => by simp [hx]⟩
    have hmem : (x : G) ∈ H ⊓ centralizer (R : Set G) := ⟨x.2, hx⟩
    rw [hCH] at hmem
    exact Subtype.ext (by simpa using hmem)
  rw [hfix]
  simp

theorem not_dvd_natCard_of_inf_centralizer_eq_bot [H.Normal] [Finite H] (hp : p.Prime)
    (hR : Nat.card R = p) (hCH : H ⊓ centralizer (R : Set G) = ⊥) : ¬ p ∣ Nat.card H := by
  have : Fact p.Prime := ⟨hp⟩
  have hcong : Nat.card H ≡ Nat.card (fixedPoints (toConjActSubgroup R) H) [MOD p] :=
    natCard_modEq_natCard_fixedPoints (a := 1)
      (by rw [natCard_toConjActSubgroup, hR, pow_one])
  rw [natCard_fixedPoints_toConjActSubgroup_eq_one hCH] at hcong
  intro hdvd
  have h0 : (0 : ℕ) ≡ 1 [MOD p] := (Nat.modEq_zero_iff_dvd.mpr hdvd).symm.trans hcong
  exact hp.one_lt.ne' (Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp h0.symm))

theorem zpowers_eq_of_natCard_eq_prime (hp : p.Prime) (hR : Nat.card R = p) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) : zpowers r = R := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_antisymm (zpowers_le.mpr hr) fun b hb => ?_
  obtain ⟨k, hk⟩ : (⟨b, hb⟩ : R) ∈ zpowers (⟨r, hr⟩ : R) :=
    mem_zpowers_of_prime_card hR (by simpa [Subtype.ext_iff] using hr1)
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem centralizer_singleton_eq_centralizer (hp : p.Prime) (hR : Nat.card R = p) {r : G}
    (hr : r ∈ R) (hr1 : r ≠ 1) : centralizer ({r} : Set G) = centralizer (R : Set G) := by
  rw [← centralizer_closure, ← zpowers_eq_closure, zpowers_eq_of_natCard_eq_prime hp hR hr hr1]

theorem inf_centralizer_singleton_eq_bot_of_natCard_eq_prime (hp : p.Prime) (hR : Nat.card R = p)
    (hCH : H ⊓ centralizer (R : Set G) = ⊥) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    H ⊓ centralizer ({r} : Set G) = ⊥ := by
  rw [centralizer_singleton_eq_centralizer hp hR hr hr1, hCH]

theorem not_dvd_natCard_and_inf_centralizer_singleton_eq_bot [Finite G] [H.Normal]
    (_hprod : (H : Set G) * (R : Set G) = Set.univ) (_hinf : H ⊓ R = ⊥)
    (hp : p.Prime) (hR : Nat.card R = p) (hCH : H ⊓ centralizer (R : Set G) = ⊥) :
    ¬ p ∣ Nat.card H ∧ ∀ r ∈ R, r ≠ 1 → H ⊓ centralizer ({r} : Set G) = ⊥ :=
  ⟨not_dvd_natCard_of_inf_centralizer_eq_bot hp hR hCH,
    fun _ hr hr1 => inf_centralizer_singleton_eq_bot_of_natCard_eq_prime hp hR hCH hr hr1⟩

end

end CFSG.FeitThompson
