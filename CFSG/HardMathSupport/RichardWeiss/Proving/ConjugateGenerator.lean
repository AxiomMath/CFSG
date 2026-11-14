module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

theorem exists_gen_map_conj {S : Type} [Group S] {Y : Subgroup S} (hY : Nat.card Y = 3)
    (g : S) :
    ∃ a : S, orderOf a = 3 ∧ Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers a := by
  classical
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hcardH : Nat.card ↥(Y.map (MulAut.conj g).toMonoidHom) = 3 := by
    rw [← hY]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective Y _ hinj).toEquiv).symm
  haveI : Finite ↥(Y.map (MulAut.conj g).toMonoidHom) :=
    Nat.finite_of_card_ne_zero (by rw [hcardH]; norm_num)
  haveI : Nontrivial ↥(Y.map (MulAut.conj g).toMonoidHom) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardH]; norm_num)
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥(Y.map (MulAut.conj g).toMonoidHom))
  have hcard_zp : Nat.card (Subgroup.zpowers x) = 3 := by
    have hdvd : Nat.card (Subgroup.zpowers x) ∣ 3 := by
      rw [← hcardH]
      exact Subgroup.card_subgroup_dvd_card _
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd ((Subgroup.eq_bot_iff_card _).mpr h) (Subgroup.zpowers_ne_bot.mpr hx1)
    · exact h
  have htop : Subgroup.zpowers x = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hcard_zp, hcardH])
  have hx : ∀ y : ↥(Y.map (MulAut.conj g).toMonoidHom), y ∈ Subgroup.zpowers x :=
    fun y => htop ▸ Subgroup.mem_top y
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := by
      rw [← hcardH]
      exact orderOf_dvd_natCard x
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  refine ⟨(x : S), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe (G := S) (H := Y.map (MulAut.conj g).toMonoidHom) x, hxord]
  · apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx ⟨y, hy⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h2 : (x : S) ^ k = ((x ^ k : ↥(Y.map (MulAut.conj g).toMonoidHom)) : S) := rfl
      exact h2.trans (congrArg Subtype.val hk)
    · exact Subgroup.zpowers_le.mpr x.2

end CFSG.HardMathSupport.RichardWeiss.Proving

end
