module

public import CFSG.Goldschmidt75.Sec45c

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

theorem thmAFor
    (G : Type) [Group G] [Finite G] : ThmAFor G := by
  suffices key : ∀ n, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → ThmAFor G from
    key _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro G _ _ hn
  suffices key : ∀ m, ∀ (T : Sylow 2 G) (S₁ S₂ : Subgroup G),
      Nat.card S₁ * Nat.card S₂ = m → S₁ ≤ T → S₂ ≤ T →
      fusionStronglyClosed (S₁ : Set G) T → fusionStronglyClosed (S₂ : Set G) T →
      S₁ ≤ centralizer (S₂ : Set G) → S₁ ⊓ S₂ = ⊥ →
      ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤ goldschmidtOddCore G from
    fun T S₁ S₂ => key _ T S₁ S₂ rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro T S₁ S₂ hm h₁ h₂ hc₁ hc₂ hc hd
  by_contra hfail
  exact MinCE.false (T := T) (S₁ := S₁) (S₂ := S₂)
    { le₁ := h₁
      le₂ := h₂
      sc₁ := hc₁
      sc₂ := hc₂
      comm := hc
      disj := hd
      ihG := fun H _ _ hH => ihn _ (hn ▸ hH) H rfl
      ihS := fun T' R₁ R₂ hR₁ hR₂ hcR₁ hcR₂ hcR hdR hlt =>
        ihm _ (hm ▸ hlt) T' R₁ R₂ rfl hR₁ hR₂ hcR₁ hcR₂ hcR hdR
      fail := hfail }

theorem theoremA
    {G : Type} [Group G] [Finite G] {S₁ S₂ : Subgroup G} (T₁ T₂ : Sylow 2 G)
    (h₁ : S₁ ≤ T₁) (h₂ : S₂ ≤ T₂) (hS₁ : fusionStronglyClosed (S₁ : Set G) T₁)
    (hS₂ : fusionStronglyClosed (S₂ : Set G) T₂) (hcomm : ⁅S₁, S₂⁆ = ⊥) (hdisj : S₁ ⊓ S₂ = ⊥) :
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤ goldschmidtOddCore G := by
  have hc : S₁ ≤ centralizer (S₂ : Set G) := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hp : IsPGroup 2 (S₁ ⊔ S₂ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (T₁.isPGroup'.to_le h₁) (T₂.isPGroup'.to_le h₂)
      (hc.trans (centralizer_le_normalizer _))
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have h₁T : S₁ ≤ T := le_sup_left.trans hT
  have h₂T : S₂ ≤ T := le_sup_right.trans hT
  exact thmAFor G T S₁ S₂ h₁T h₂T (stronglyClosed_of_le_sylow T₁ T hS₁ h₁T)
    (stronglyClosed_of_le_sylow T₂ T hS₂ h₂T) hc hdisj

end CFSG.Goldschmidt75
