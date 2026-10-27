module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WPGU
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.ComponentClassification
open scoped MatrixGroups

namespace Ivk93W

variable {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {B : Subgroup J}

theorem false_of_two_pComponents (h : Ivk93W x q B)
    {I₁ I₂ : Subgroup ↥(centralizer ({x} : Set J))} (h₁ : IsPComponent 2 I₁)
    (h₂ : IsPComponent 2 I₂) (hne : I₁ ≠ I₂) : False := by
  have key : ∀ I : Subgroup ↥(centralizer ({x} : Set J)), IsPComponent 2 I →
      I.map (centralizer ({x} : Set J)).subtype = B := by
    intro I hI
    refine h.uniq _ ⟨?_, ?_⟩
    · rintro _ ⟨u, -, rfl⟩
      exact u.2
    · rwa [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  exact hne (Subgroup.map_injective (Subgroup.subtype_injective _)
    ((key I₁ h₁).trans (key I₂ h₂).symm))

theorem false_of_shape (h : Ivk93W x q B) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] (h₁ : 4 ≤ Nat.card F₁) (h₂ : 4 ≤ Nat.card F₂)
    (S : Ivk47ab.Shape ↥(centralizer ({x} : Set J)) F₁ F₂) : False := by
  have hq₁ : CFSG.IsQuasisimple ↥S.I₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₁.symm (GHInv.isQuasisimple_sl2 h₁)
  have hq₂ : CFSG.IsQuasisimple ↥S.I₂ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₂.symm (GHInv.isQuasisimple_sl2 h₂)
  have c₁ : IsPComponent 2 S.I₁ :=
    LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent
      ⟨hq₁, (Ivk93Exc.instNormalI₁ S).isSubnormal⟩
  have c₂ : IsPComponent 2 S.I₂ :=
    LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent
      ⟨hq₂, (Ivk93Exc.instNormalI₂ S).isSubnormal⟩
  refine h.false_of_two_pComponents c₁ c₂ fun heq => ?_
  exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq₁
    (Group.isSolvable_of_comm fun a b => Subtype.ext (S.comm _ a.2 _ (heq ▸ b.2)))

end Ivk93W

theorem ivk93w_g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93WEmpty (fun X _ => LieModel X .G2 0 p f) := by
  intro p f hp hp2 hf J _ _ hJ x q B h _
  obtain ⟨F, hF, hFin, S, hcard, -⟩ := GHInv.exists_shape_G2 hp hp2 hJ x h.ord
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  by_cases h3 : Nat.card F = 3
  · have := GHInv.isSolvable_sl2_of_card_three h3
    have hs₁ : Group.IsSolvable ↥S.I₁ :=
      Group.isSolvable_of_isSolvable_injective (f := S.e₁.toMonoidHom) S.e₁.injective
    have hs₂ : Group.IsSolvable ↥S.I₂ :=
      Group.isSolvable_of_isSolvable_injective (f := S.e₂.toMonoidHom) S.e₂.injective
    exact h.false_of_solvable (Ivk93Exc.isSolvable_of_solvable_factors S hs₁ hs₂)
  · have h4 : 4 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      obtain ⟨m, hm⟩ := hodd
      omega
    exact h.false_of_shape h4 h4 S

theorem ivk93w_d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93WD4 (p ^ f) := by
  intro p f hp hp2 hf J _ _ hJ x q B h _
  obtain ⟨p', f', hpf, hJ'⟩ := hJ
  obtain ⟨hp', hf'⟩ : p'.Prime ∧ 1 ≤ f' := by
    rcases hJ' with ⟨h', -⟩ | ⟨-, -, h'⟩ | ⟨-, h', -⟩ | ⟨-, h', -⟩
    · exact absurd h' (by decide)
    · exact ⟨h'.1.1, h'.1.2.1⟩
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  obtain ⟨hpp, hff⟩ := Nat.Prime.pow_inj' hp' hp (by omega) (by omega) hpf
  rw [hpp, hff] at hJ'
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, -⟩ :=
    GHInv.exists_shape_D4 hp hp2 hJ' x h.ord
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hn3 : 3 ≤ p ^ f := three_le_pow hp hp2 hf
  have hodd₁ : Odd (Nat.card F₁) := by
    rw [hc₁]
    exact hodd.pow
  have h₁ : 5 ≤ Nat.card F₁ := by
    rw [hc₁]
    calc 5 ≤ 3 ^ 3 := by norm_num
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hn3 3
  by_cases h3 : p ^ f = 3
  · refine ⟨h3, ?_⟩
    have hq₁ : CFSG.IsQuasisimple ↥S.I₁ :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₁.symm (GHInv.isQuasisimple_sl2 (by omega))
    have hs₂ : Group.IsSolvable ↥S.I₂ := by
      have := GHInv.isSolvable_sl2_of_card_three (K := F₂) (hc₂.trans h3)
      exact Group.isSolvable_of_isSolvable_injective (f := S.e₂.toMonoidHom) S.e₂.injective
    have hBI : B.subgroupOf (centralizer ({x} : Set J)) = S.I₁ :=
      Ivk93Exc.pComponent_eq_I₁_of_solvable_I₂ S hq₁ hs₂ h.comp.2
    have e : SL(2, F₁) ≃* ↥B :=
      S.e₁.symm.trans ((MulEquiv.subgroupCongr hBI.symm).trans (Subgroup.subgroupOfEquivOfLe h.le))
    have hq := h.q_eq_of_equiv_sl2 hodd₁ h₁ e
    rw [hc₁, h3] at hq
    omega
  · exfalso
    have h4₂ : 4 ≤ Nat.card F₂ := by
      rw [hc₂]
      obtain ⟨m, hm⟩ := hodd
      omega
    exact h.false_of_shape (by omega) h4₂ S

end CFSG.GH74.GLS.IVK.Proofs2
