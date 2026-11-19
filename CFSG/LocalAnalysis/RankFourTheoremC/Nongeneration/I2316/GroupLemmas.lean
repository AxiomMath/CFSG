module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

theorem exists_ne_one_mem_ker_of_cyclic {G H : Type*} [Group G] [Group H] [Finite H] [IsCyclic H]
    (f : G →* H) {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) : ∃ x ∈ E, x ≠ 1 ∧ f x = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype H := Fintype.ofFinite H
  let g : E → {h : H // h ^ p = 1} := fun x =>
    ⟨f x, by rw [← map_pow]; simp [hE x x.2]⟩
  have hg : Function.Injective g := by
    intro x y hxy
    have h1 : f (x : G) = f (y : G) := congrArg Subtype.val hxy
    have h2 : f ((x : G) * (y : G)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    by_contra hne
    have hne' : (x : G) * (y : G)⁻¹ ≠ 1 := by
      intro h
      exact hne (Subtype.ext (mul_inv_eq_one.mp h))
    exact hcon _ (E.mul_mem x.2 (E.inv_mem y.2)) hne' h2
  have hle : Nat.card E ≤ Nat.card {h : H // h ^ p = 1} := Nat.card_le_card_of_injective g hg
  have hle2 : Nat.card {h : H // h ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    obtain ⟨g, hg'⟩ := exists_zpow_surjective H
    have hg : ∀ x : H, x ∈ Subgroup.zpowers g := fun x => by
      obtain ⟨k, rfl⟩ := hg' x
      exact Subgroup.zpow_mem_zpowers g k
    have hord : orderOf g = Nat.card H := by
      have h1 : Nat.card ↥(Subgroup.zpowers g) = orderOf g := by
        rw [Nat.card_eq_fintype_card, Fintype.card_zpowers]
      have h2 : Nat.card ↥(Subgroup.zpowers g) = Nat.card H := by
        rw [(Subgroup.eq_top_iff' _).mpr hg, Subgroup.card_top]
      exact h1.symm.trans h2
    calc (Finset.univ.filter fun a : H => a ^ p = 1).card
        ≤ (Subgroup.zpowers (g ^ (Fintype.card H / Nat.gcd p (Fintype.card H))) :
            Set H).toFinset.card := by
          gcongr
          intro x hx
          let ⟨m, hm⟩ := show x ∈ Submonoid.powers g from
            mem_powers_iff_mem_zpowers.2 <| hg x
          refine Set.mem_toFinset.2
            ⟨((m / (Fintype.card H / Nat.gcd p (Fintype.card H)) : ℕ) : ℤ), ?_⟩
          dsimp only at ⊢ hm
          rw [zpow_natCast, ← pow_mul, Nat.mul_div_cancel_left', hm]
          refine Nat.dvd_of_mul_dvd_mul_right
            (Nat.gcd_pos_of_pos_left (Fintype.card H) hp.pos) ?_
          conv_lhs =>
            rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), ← Nat.card_eq_fintype_card,
              ← hord]
          exact orderOf_dvd_of_pow_eq_one <| by
            simpa [pow_mul, hm] using (Finset.mem_filter.1 hx).2
      _ ≤ p := by
          let ⟨m, hm⟩ := Nat.gcd_dvd_right p (Fintype.card H)
          have hm0 : 0 < m :=
            Nat.pos_of_ne_zero fun hm0 => by
              rw [hm0, mul_zero, Fintype.card_eq_zero_iff] at hm
              exact hm.elim' 1
          simp only [Set.toFinset_card, SetLike.coe_sort_coe]
          rw [Fintype.card_zpowers, orderOf_pow, hord, Nat.card_eq_fintype_card]
          nth_rw 2 [hm]; nth_rw 3 [hm]
          rw [Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left _ hp.pos),
            Nat.gcd_mul_left_left, hm, Nat.mul_div_cancel _ hm0]
          exact Nat.le_of_dvd hp.pos (Nat.gcd_dvd_left _ _)
  have hp1 := hp.one_lt
  have h2 : p ^ 2 ≤ p := hcard ▸ hle.trans hle2
  have h3 : p * p ≤ p * 1 := by simpa [pow_two] using h2
  have := Nat.le_of_mul_le_mul_left h3 hp.pos
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
