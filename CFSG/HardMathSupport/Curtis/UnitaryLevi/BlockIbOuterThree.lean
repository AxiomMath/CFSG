module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftAct
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {Y : Type} [Group Y]

theorem exists_act_of_outer_dvd_two {Lb : Subgroup Y} (hOut : Nat.card (Outer ↥Lb) ∣ 2) {u : Y}
    (hu : u ∈ Subgroup.normalizer (Lb : Set Y)) {k : ℕ} (huk : u ^ 3 ^ k = 1) :
    ∃ ℓ ∈ Lb, Lift.Act Lb u ℓ := by
  set n : ↥(Subgroup.normalizer (Lb : Set Y)) := ⟨u, hu⟩ with hn
  set α : MulAut ↥Lb := Subgroup.normalizerMonoidHom Lb n with hα
  have hn1 : n ^ 3 ^ k = 1 := Subtype.ext (by simpa [hn] using huk)
  have hα1 : α ^ 3 ^ k = 1 := by
    rw [hα, ← map_pow, hn1, map_one]
  set o : Outer ↥Lb := QuotientGroup.mk α with ho
  have ho1 : o ^ 3 ^ k = 1 := by
    rw [ho, ← QuotientGroup.mk_pow, hα1, QuotientGroup.mk_one]
  have h1 : orderOf o ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one ho1
  have h2 : orderOf o ∣ 2 := (orderOf_dvd_natCard o).trans hOut
  have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left _ (by norm_num)
  have h3 : orderOf o ∣ Nat.gcd (3 ^ k) 2 := Nat.dvd_gcd h1 h2
  rw [hcop] at h3
  have hord : orderOf o = 1 := Nat.dvd_one.mp h3
  have hone : o = 1 := orderOf_eq_one_iff.mp hord
  have hinn : α ∈ inner ↥Lb := (QuotientGroup.eq_one_iff (N := inner ↥Lb) α).mp hone
  obtain ⟨ℓ, hℓ⟩ := hinn
  refine ⟨ℓ, ℓ.2, fun l hl => ?_⟩
  have := congrArg (fun f : MulAut ↥Lb => ((f ⟨l, hl⟩ : ↥Lb) : Y)) hℓ
  simpa [hα, hn, MulAut.conj_apply] using this.symm

end CFSG.HardMathSupport.Curtis.UnitaryLevi
