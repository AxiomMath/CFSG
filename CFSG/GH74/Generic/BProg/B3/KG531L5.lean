module

public import CFSG.GH74.Generic.BProg.B3.KG531Defs
public import CFSG.GH74.Generic.S45.LLinSel

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RestrictedStd
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OutcomeLocal

namespace KG531L5

theorem centralizer_top_eq_bot {S : Type} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) :
    centralizer (((⊤ : Subgroup S) : Subgroup S) : Set S) = ⊥ := by
  rw [← CFSG.ComponentClassification.OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab]
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.coe_top, Set.mem_univ, forall_const,
    Subgroup.mem_center_iff]

section Config

variable {S : Type} [Group S] {t : S} {B₁ B₂ : Subgroup S} {p f : ℕ}

theorem isComponentOf₁ (h : KG531Cfg t B₁ B₂ p f) :
    CFSG.Assembly.IsComponentOf B₁ (centralizer ({t} : Set S)) :=
  (isComponentOf_iff_isComponent_subgroupOf h.comp₁.1).2 h.comp₁.2

theorem odd_card_center₁ (h : KG531Cfg t B₁ B₂ p f) : Odd (Nat.card ↥(center ↥B₁)) := by
  rw [h.center₁, Subgroup.card_bot]
  exact odd_one

theorem smallSource₁ (h : KG531Cfg t B₁ B₂ p f) : SmallSource B₁ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := h.five
      simp at this
    · exact hf
  exact Or.inl ⟨p, f, h.prime, h.odd, hf, h.five,
    Or.inl ⟨by decide, h.model₁⟩, odd_card_center₁ h⟩

end Config

theorem ne_two {p f : ℕ} (hf : 1 ≤ f) {r : ℕ} (hmod : p ^ f % 4 = r) (hr : r % 2 = 1) :
    p ≠ 2 := by
  rintro rfl
  have h2 : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have := Nat.even_iff.1 h2
  omega

end KG531L5

theorem kg531_l5 (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hmod : p ^ f % 4 = 3) :
    KG531Empty (fun X _ => LieModel X .PSL 5 p f) := by
  intro S _ _ hS hnab hL t B₁ B₂ p' f' h
  classical
  have hp2 : p ≠ 2 := KG531L5.ne_two hf hmod rfl
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := CFSG.GH74.Generic.S45.LQ.stated_of_lieModel_PSL hL
  let φ : (⊤ : Subgroup S) ≃* projectiveSL 5 F :=
    Subgroup.topEquiv.trans (e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 5 F).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F)))
  exact CFSG.GH74.Generic.S45.linear_selector_five_false (W := ⊤)
    (KG531L5.centralizer_top_eq_bot hnab) h.t_ord le_top (KG531L5.isComponentOf₁ h) h.odd h.model₁
    (KG531L5.odd_card_center₁ h) (le_refl 5) hp hp2 hf hF φ

theorem kg531_u5 (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hmod : p ^ f % 4 = 1) :
    KG531Empty (fun X _ => LieModel X .PSU 5 p f) := by
  intro S _ _ hS hnab hU t B₁ B₂ p' f' h
  have hp2 : p ≠ 2 := KG531L5.ne_two hf hmod rfl
  have hWs : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup
  have hWnab : ∃ x y : ↥(⊤ : Subgroup S), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩, fun hc => hab (congrArg Subtype.val hc)⟩
  have hM : LieModel ↥(⊤ : Subgroup S) .PSU 5 p f :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv Subgroup.topEquiv.symm hU
  exact CFSG.ComponentClassification.OddClassSelector.su_family_false (W := ⊤) hWs hWnab
    (KG531L5.centralizer_top_eq_bot hnab) h.t_ord le_top (KG531L5.isComponentOf₁ h)
    (KG531L5.smallSource₁ h) hp hp2 hf (le_refl 5) hM

end CFSG.GH74.Generic.BProg.B3
