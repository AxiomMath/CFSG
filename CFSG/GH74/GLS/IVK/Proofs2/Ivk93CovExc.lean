module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovArith
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
open scoped MatrixGroups

theorem ivk93cov_false_of_shape {J : Type} [Group J] [Finite J] {x : J} {n : ℕ} {B : Subgroup J}
    (h : Ivk93Cov x n B) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂)) (h₁ : 5 ≤ Nat.card F₁)
    (h₂ : 3 ≤ Nat.card F₂) (S : Ivk47ab.Shape ↥(centralizer ({x} : Set J)) F₁ F₂) : False := by
  have hq₁ : CFSG.IsQuasisimple ↥S.I₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₁.symm (GHInv.isQuasisimple_sl2 (by omega))
  by_cases h3 : Nat.card F₂ = 3
  · have hsolv : Group.IsSolvable ↥S.I₂ := by
      have := GHInv.isSolvable_sl2_of_card_three h3
      exact Group.isSolvable_of_isSolvable_injective (f := S.e₂.toMonoidHom) S.e₂.injective
    have h1 := Ivk93Exc.pComponent_eq_I₁_of_solvable_I₂ S hq₁ hsolv h.comp.2
    exact h.false_of_equiv_sl2 hodd₁ h₁
      (S.e₁.symm.trans ((MulEquiv.subgroupCongr h1.symm).trans (Subgroup.subgroupOfEquivOfLe h.le)))
  · have h5₂ : 5 ≤ Nat.card F₂ := by
      obtain ⟨m, hm⟩ := hodd₂
      omega
    have hq₂ : CFSG.IsQuasisimple ↥S.I₂ :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₂.symm (GHInv.isQuasisimple_sl2 (by omega))
    have hb₁ := Ivk93Exc.pPrimeCore_eq_bot_of_equiv_sl2 hodd₁ (by omega) S.e₁
    have hb₂ := Ivk93Exc.pPrimeCore_eq_bot_of_equiv_sl2 hodd₂ (by omega) S.e₂
    rcases Ivk93Exc.pComponent_eq_I S hq₁ hq₂ hb₁ hb₂ h.comp.2 with h1 | h1
    · exact h.false_of_equiv_sl2 hodd₁ h₁
        (S.e₁.symm.trans ((MulEquiv.subgroupCongr h1.symm).trans (Subgroup.subgroupOfEquivOfLe h.le)))
    · exact h.false_of_equiv_sl2 hodd₂ h5₂
        (S.e₂.symm.trans ((MulEquiv.subgroupCongr h1.symm).trans (Subgroup.subgroupOfEquivOfLe h.le)))

theorem ivk93cov_g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93CovEmpty (fun X _ => LieModel X .G2 0 p f) := by
  intro p f hp hp2 hf
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  obtain ⟨F, hF, hFin, S, hcard, -⟩ := GHInv.exists_shape_G2 hp hp2 hJ x hc.ord
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  by_cases h3 : Nat.card F = 3
  · have := GHInv.isSolvable_sl2_of_card_three h3
    have hs₁ : Group.IsSolvable ↥S.I₁ :=
      Group.isSolvable_of_isSolvable_injective (f := S.e₁.toMonoidHom) S.e₁.injective
    have hs₂ : Group.IsSolvable ↥S.I₂ :=
      Group.isSolvable_of_isSolvable_injective (f := S.e₂.toMonoidHom) S.e₂.injective
    exact hc.false_of_solvable (Ivk93Exc.isSolvable_of_solvable_factors S hs₁ hs₂)
  · have h5 : 5 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      obtain ⟨m, hm⟩ := hodd
      omega
    exact ivk93cov_false_of_shape hc hodd hodd h5 (by omega) S

theorem ivk93cov_five_le_cube {n : ℕ} (h : 3 ≤ n) : 5 ≤ n ^ 3 := by
  have h1 : n ^ 3 = n * n * n := by ring
  rw [h1]
  nlinarith

theorem ivk93cov_d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93CovEmpty (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro p f hp hp2 hf
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, -⟩ :=
    GHInv.exists_shape_D4 hp hp2 hJ x hc.ord
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hn3 : 3 ≤ p ^ f := by
    have h2 := hp.two_le
    have h3 := Nat.le_self_pow (show f ≠ 0 by omega) p
    omega
  have hodd₁ : Odd (Nat.card F₁) := by
    rw [hc₁]
    exact hodd.pow
  have hodd₂ : Odd (Nat.card F₂) := by
    rw [hc₂]
    exact hodd
  have h₁ : 5 ≤ Nat.card F₁ := by
    rw [hc₁]
    exact ivk93cov_five_le_cube hn3
  exact ivk93cov_false_of_shape hc hodd₁ hodd₂ h₁ (by rw [hc₂]; exact hn3) S

end CFSG.GH74.GLS.IVK.Proofs2
