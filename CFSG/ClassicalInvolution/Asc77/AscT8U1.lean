module

public import CFSG.ClassicalInvolution.Asc77.AscT8T3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.Theorem5

namespace T8U

section LinkAlpha

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian2_of_le {B F : Subgroup G} (hB : IsElemAbelian 2 B) (hFB : F ≤ B)
    (hF4 : Nat.card F = 4) : IsElemAbelian2 F 2 :=
  ⟨by rw [hF4]; norm_num, fun x hx => by rw [← pow_two]; exact hB.2 x (hFB hx)⟩

theorem alphaOf_eq_of_shareFour {A B : Subgroup G} (hA : RankThreeBalance A)
    (hB : RankThreeBalance B) (hAB : ShareFour A B) {F₁ F₂ : Subgroup G} (h₁ : F₁ ≤ A)
    (h₁4 : Nat.card F₁ = 4) (h₂ : F₂ ≤ B) (h₂4 : Nat.card F₂ = 4) :
    alphaOf F₁ = alphaOf F₂ := by
  obtain ⟨F, hFA, hFB⟩ := hAB
  have hF4 : Nat.card F = 4 := by rw [hFA.2]; norm_num
  exact (alphaOf_eq_alphaOf_of_rankThreeBalance hA h₁ hFA.1 h₁4 hF4).trans
    (alphaOf_eq_alphaOf_of_rankThreeBalance hB hFB.1 h₂ hF4 h₂4)

theorem exists_le_conj {B F₂ : Subgroup G} {y : G} (h₂ : F₂ ≤ B.map (MulAut.conj y).toMonoidHom)
    (h₂4 : Nat.card F₂ = 4) :
    ∃ F : Subgroup G, F ≤ B ∧ Nat.card F = 4 ∧ conjSub y F = F₂ := by
  refine ⟨conjSub y⁻¹ F₂, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : y * x * y⁻¹ ∈ F₂ := by
      have := mem_conjSub_iff.mp hx
      simpa using this
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp (h₂ hx')
    have h1 : y * w * y⁻¹ = y * x * y⁻¹ := hwe
    have : w = x := mul_left_cancel (mul_right_cancel h1)
    exact this ▸ hw
  · show Nat.card (F₂.map (MulAut.conj y⁻¹).toMonoidHom) = 4
    exact (Nat.card_congr (Subgroup.equivMapOfInjective F₂ (MulAut.conj y⁻¹).toMonoidHom
      (MulAut.conj y⁻¹).injective).toEquiv).symm.trans h₂4
  · rw [← conjSub_mul]
    simp

theorem alphaOf_eq_of_oddCore_conj {B : Subgroup G} (hB : RankThreeBalance B) {a y : G}
    (haB : a ∈ B) (hy : y ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)))
    {F₁ F₂ : Subgroup G} (h₁ : F₁ ≤ B) (h₁4 : Nat.card F₁ = 4)
    (h₂ : F₂ ≤ B.map (MulAut.conj y).toMonoidHom) (h₂4 : Nat.card F₂ = 4) :
    alphaOf F₁ = alphaOf F₂ := by
  obtain ⟨F, hFB, hF4, hFconj⟩ := exists_le_conj h₂ h₂4
  have hnorm : y ∈ Subgroup.normalizer (alphaOf F : Set G) := by
    have hBC := T8T.oddCoreOf_centralizer_le_normalizer (B := B) (α₀ := alphaOf F) hB.elem
      hB.card haB (fun A hAB hA => alphaOf_eq_alphaOf_of_rankThreeBalance hB hAB hFB
        (by rw [hA.1]; norm_num) hF4)
    exact hBC hy
  have h1 : alphaOf F₂ = alphaOf F := by
    rw [← hFconj, alphaOf_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mp hnorm
  rw [h1]
  exact alphaOf_eq_alphaOf_of_rankThreeBalance hB h₁ hFB h₁4 hF4

theorem alphaOf_eq_of_reflTransGen_linkMove {𝒯 : Set (Subgroup G)} {cl : Subgroup G → Set G}
    {a : G} (hbal : ∀ A ∈ 𝒯, RankThreeBalance A) (hcl : ∀ A ∈ 𝒯, ∀ z ∈ cl A, z ∈ A)
    {A B : Subgroup G} (hA : A ∈ 𝒯) (h : Relation.ReflTransGen (LinkMove 𝒯 cl a) A B)
    {F₁ F₂ : Subgroup G} (h₁ : F₁ ≤ A) (h₁4 : Nat.card F₁ = 4) (h₂ : F₂ ≤ B)
    (h₂4 : Nat.card F₂ = 4) : alphaOf F₁ = alphaOf F₂ := by
  induction h generalizing F₂ with
  | refl => exact alphaOf_eq_alphaOf_of_rankThreeBalance (hbal A hA) h₁ h₂ h₁4 h₂4
  | @tail b c _ hbc ih =>
    obtain ⟨hb𝒯, hc𝒯, hab, hac, hmove⟩ := hbc
    rcases hmove with hsf | ⟨y, hy, hc⟩
    ·
      obtain ⟨F, hFb, hFc⟩ := hsf
      have hF4 : Nat.card F = 4 := by rw [hFb.2]; norm_num
      rw [ih hFb.1 hF4]
      exact alphaOf_eq_alphaOf_of_rankThreeBalance (hbal c hc𝒯) hFc.1 h₂ hF4 h₂4
    ·
      subst hc
      obtain ⟨F, hFb, hF4, -⟩ := exists_le_conj h₂ h₂4
      rw [ih hFb hF4]
      exact alphaOf_eq_of_oddCore_conj (hbal b hb𝒯) (hcl b hb𝒯 a hab) hy hFb hF4 h₂ h₂4

end LinkAlpha

end T8U

end CFSG.ClassicalInvolution.Asc77
