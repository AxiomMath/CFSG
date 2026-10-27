module

public import CFSG.LargeExtraspecial.S12Five
public import CFSG.LargeExtraspecial.S12Gen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem s12_finrank_sup_le_three {A B : Submodule (ZMod 2) S.Qt} (hA : finrank (ZMod 2) A = 2)
    (hB : finrank (ZMod 2) B = 2) (hAB : A ⊓ B ≠ ⊥) :
    finrank (ZMod 2) (A ⊔ B : Submodule _ _) ≤ 3 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  have h1 : 0 < finrank (ZMod 2) (A ⊓ B : Submodule (ZMod 2) S.Qt) :=
    Nat.pos_of_ne_zero fun h => hAB (Submodule.finrank_eq_zero.mp h)
  omega

theorem timmesfeld_12_5 (hRI : RootInvolutionComponentsInput.{u}) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) {t : S.O}
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨ ∀ τ ∈ S.Ebar12 g, ∃ x ∈ S.Xbar12 g, τ = x * t * x⁻¹ := by
  have htE : t ∈ S.Ebar12 g := mem_Ebar12_of_mem_Lbar ht htA
  have hn3 : 3 ≤ S.width := by omega
  by_cases hF : (compl12 g t).Nonempty
  · left
    obtain ⟨⟨f₁, hf₁, f₂, hf₂, hsub⟩, -⟩ := S.s12_lemma_S5 haQ hne hn3 htE hF
    have hF₁ : (compl12 g f₁).Nonempty := ⟨t, htE, fun h => hf₁.2 (comp12_symm h)⟩
    obtain ⟨⟨e₁, he₁, e₂, he₂, hsub'⟩, hmeet⟩ := S.s12_lemma_S5 haQ hne hn3 hf₁.1 hF₁
    have hcover : ∀ x ∈ S.Ebar12 g, x ∈ closure ({f₁, f₂} : Set S.O) ∨
        x ∈ closure ({e₁, e₂} : Set S.O) := by
      intro x hx
      by_cases hxc : x ∈ S.comp12 f₁
      · left
        refine hsub ⟨hx, fun hxt => hf₁.2 ?_⟩
        exact comp12_trans hxt (comp12_symm hxc)
      · right
        exact hsub' ⟨hx, hxc⟩
    set U := (commSpace (e₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊔
      (commSpace (e₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt)) with hU
    have hpair : ∀ {a b : S.O}, commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ U →
        commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ U → ∀ x ∈ closure ({a, b} : Set S.O),
          commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ U := by
      intro a b ha hb x hx
      refine (commSpace_le_commSub12 hx).trans ((commSub12_closure_le _).trans
        (commSubSet12_le fun y hy => ?_))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    have hle : S.commSub12 (S.Xbar12 g) ≤ U := by
      refine (commSub12_closure_le _).trans (commSubSet12_le fun x hx => ?_)
      rcases hcover x hx with h | h
      · exact hpair (le_sup_of_le_left le_sup_right) (le_sup_of_le_right le_sup_right) x h
      · exact hpair (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left) x h
    have hdim : finrank (ZMod 2) (S.commSub12 (S.Xbar12 g)) ≤ 7 := by
      refine (Submodule.finrank_mono hle).trans ?_
      refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
      have h1 := S.s12_finrank_sup_le_three (isTypeA_of_mem_Ebar12 he₁.1).2.2.2.1
        (isTypeA_of_mem_Ebar12 hf₁.1).2.2.2.1 (hmeet e₁ he₁)
      have h2 := Submodule.finrank_add_le_finrank_add_finrank
        (commSpace (e₂ : S.Qt ≃ₗ[ZMod 2] S.Qt)) (commSpace (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt))
      have h3 := (isTypeA_of_mem_Ebar12 he₂.1).2.2.2.1
      have h4 := (isTypeA_of_mem_Ebar12 hf₂.1).2.2.2.1
      omega
    have ht1 : t ≠ 1 := fun e => htA.2.1 (by rw [e]; rfl)
    refine S.s12_isReducible12_of_finrank_lt Mbar_le_normalizer_Xbar12 (subset_Xbar12 htE) ht1 ?_
    rw [S.finrank_Qt_eq_two_mul_width]
    omega
  · right
    have hEc : S.Ebar12 g = S.comp12 t := by
      refine le_antisymm (fun x hx => ?_) (comp12_subset_Ebar12 hRI htE)
      by_contra hxc
      exact hF ⟨x, hx, hxc⟩
    obtain ⟨X, hX, hconj⟩ := comp12_conj_of_mem hRI htE
    intro τ hτ
    obtain ⟨x, hx, rfl⟩ := hconj τ (hEc ▸ hτ)
    refine ⟨x, ?_, rfl⟩
    rw [hX, ← hEc] at hx
    exact hx

end Setting

end CFSG.LargeExtraspecial
