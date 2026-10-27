module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
open scoped MatrixGroups

theorem ivk93_shape {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {L₁ L₂ : Subgroup J}
    (h : Ivk93Cfg x q L₁ L₂) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂)) (h₁ : 5 ≤ Nat.card F₁)
    (h₂ : 3 ≤ Nat.card F₂) (S : Ivk47ab.Shape ↥(centralizer ({x} : Set J)) F₁ F₂) :
    Nat.card F₁ = q ∧ Nat.card F₂ = q := by
  have hq₁ : CFSG.IsQuasisimple ↥S.I₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₁.symm (GHInv.isQuasisimple_sl2 (by omega))
  have hne : (L₁.subgroupOf (centralizer ({x} : Set J))) ≠ L₂.subgroupOf (centralizer ({x} : Set J)) := by
    intro heq
    apply h.ne
    have := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr h.le₁, inf_eq_left.mpr h.le₂] at this
  by_cases h3 : Nat.card F₂ = 3
  · exfalso
    have hsolv : Group.IsSolvable ↥S.I₂ := by
      have := GHInv.isSolvable_sl2_of_card_three h3
      exact Group.isSolvable_of_isSolvable_injective (f := S.e₂.toMonoidHom) S.e₂.injective
    exact hne ((Ivk93Exc.pComponent_eq_I₁_of_solvable_I₂ S hq₁ hsolv h.comp₁.2).trans
      (Ivk93Exc.pComponent_eq_I₁_of_solvable_I₂ S hq₁ hsolv h.comp₂.2).symm)
  · have h5₂ : 5 ≤ Nat.card F₂ := by
      obtain ⟨m, hm⟩ := hodd₂
      omega
    have hq₂ : CFSG.IsQuasisimple ↥S.I₂ :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₂.symm (GHInv.isQuasisimple_sl2 (by omega))
    have hb₁ := Ivk93Exc.pPrimeCore_eq_bot_of_equiv_sl2 hodd₁ (by omega) S.e₁
    have hb₂ := Ivk93Exc.pPrimeCore_eq_bot_of_equiv_sl2 hodd₂ (by omega) S.e₂
    have e1 := Ivk93Exc.pComponent_eq_I S hq₁ hq₂ hb₁ hb₂ h.comp₁.2
    have e2 := Ivk93Exc.pComponent_eq_I S hq₁ hq₂ hb₁ hb₂ h.comp₂.2
    have key₁ : ∀ (hh : Ivk93Cfg x q L₁ L₂) {F : Type} [Field F] [Finite F] {I : Subgroup _},
        Odd (Nat.card F) → 5 ≤ Nat.card F → (e : SL(2, F) ≃* ↥I) →
        L₁.subgroupOf (centralizer ({x} : Set J)) = I → Nat.card F = q := by
      intro hh F _ _ I hodd h5 e hI
      exact hh.q_eq_of_equiv_sl2 hodd h5
        (e.trans ((MulEquiv.subgroupCongr hI.symm).trans (Subgroup.subgroupOfEquivOfLe hh.le₁)))
    have key₂ : ∀ (hh : Ivk93Cfg x q L₁ L₂) {F : Type} [Field F] [Finite F] {I : Subgroup _},
        Odd (Nat.card F) → 5 ≤ Nat.card F → (e : SL(2, F) ≃* ↥I) →
        L₂.subgroupOf (centralizer ({x} : Set J)) = I → Nat.card F = q := by
      intro hh F _ _ I hodd h5 e hI
      exact hh.symm.q_eq_of_equiv_sl2 hodd h5
        (e.trans ((MulEquiv.subgroupCongr hI.symm).trans (Subgroup.subgroupOfEquivOfLe hh.le₂)))
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact (hne (e1.trans e2.symm)).elim
    · exact ⟨key₁ h hodd₁ h₁ S.e₁.symm e1, key₂ h hodd₂ h5₂ S.e₂.symm e2⟩
    · exact ⟨key₂ h hodd₁ h₁ S.e₁.symm e2, key₁ h hodd₂ h5₂ S.e₂.symm e1⟩
    · exact (hne (e1.trans e2.symm)).elim

theorem ivk93_g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93Eq (fun X _ => LieModel X .G2 0 p f) (p ^ f) := by
  intro p f hp hp2 hf J _ _ hJ x hx q L₁ L₂ h
  obtain ⟨F, hF, hFin, S, hcard, -⟩ := GHInv.exists_shape_G2 hp hp2 hJ x h.ord
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  by_cases h3 : Nat.card F = 3
  · exfalso
    have := GHInv.isSolvable_sl2_of_card_three h3
    have hs₁ : Group.IsSolvable ↥S.I₁ :=
      Group.isSolvable_of_isSolvable_injective (f := S.e₁.toMonoidHom) S.e₁.injective
    have hs₂ : Group.IsSolvable ↥S.I₂ :=
      Group.isSolvable_of_isSolvable_injective (f := S.e₂.toMonoidHom) S.e₂.injective
    exact h.false_of_solvable (Ivk93Exc.isSolvable_of_solvable_factors S hs₁ hs₂)
  · have h5 : 5 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      obtain ⟨m, hm⟩ := hodd
      omega
    obtain ⟨h1, -⟩ := ivk93_shape h hodd hodd h5 (by omega) S
    rw [← hcard]
    exact h1

theorem three_le_pow_three {n : ℕ} (h : 3 ≤ n) : 5 ≤ n ^ 3 ∧ n ^ 3 ≠ n := by
  have h1 : n ^ 3 = n * n * n := by ring
  refine ⟨?_, ?_⟩
  · rw [h1]
    nlinarith
  · intro h2
    rw [h1] at h2
    nlinarith

theorem ivk93_d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93Empty (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro p f hp hp2 hf J _ _ hJ x hx q L₁ L₂ h
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, -⟩ :=
    GHInv.exists_shape_D4 hp hp2 hJ x h.ord
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
    exact (three_le_pow_three hn3).1
  obtain ⟨e1, e2⟩ := ivk93_shape h hodd₁ hodd₂ h₁ (by rw [hc₂]; exact hn3) S
  rw [hc₁] at e1
  rw [hc₂] at e2
  exact (three_le_pow_three hn3).2 (e1.trans e2.symm)

end CFSG.GH74.GLS.IVK.Proofs2
