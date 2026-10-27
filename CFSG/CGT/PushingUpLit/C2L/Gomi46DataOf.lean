module

public import CFSG.CGT.PushingUpLit.C2L.PhaseLGlue
public import CFSG.CGT.PushingUpLit.C2L.Gomi47
import CFSG.CGT.PushingUpLit.C2L.Gomi46

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW

variable {G : Type} [Group G] [Finite G]

theorem gomi46Facts_of_ambient (hA : GomiAmbient G) : Gomi46Facts G where
  l45_three := fun P D₁ D₂ Q₁ Q₂ hP hE hQ₁ hQ₂ => by
    obtain ⟨P₁, hP₁, hQP₁⟩ := exists_isSylowOf_ge (le_top : Q₁ ≤ ⊤) hQ₁.1.isPGroup
    obtain ⟨P₂, hP₂, hQP₂⟩ := exists_isSylowOf_ge (le_top : Q₂ ≤ ⊤) hQ₂.1.isPGroup
    exact Hyp42.lemma45_three hA ⟨hP, hE, hQ₁, hQ₂, hP₁, hQP₁, hP₂, hQP₂⟩
  l46_two := fun _ _ _ _ hP hE hQ₁ => GomiE'.two₁ hA hP hE hQ₁
  l46_four := fun _ _ _ _ hP hE hB hel =>
    GomiE'.four hA hP hE hB fun b hb => by simpa [pow_two] using hel.2 b hb

theorem gomi46Data_of_ambient (hA : GomiAmbient G)
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) : Gomi46Data G where
  l47 := fun _ _ _ hP hE => gomiE'_of_gomiE hA (gomi46Facts_of_ambient hA) hO hO2 hP hE
  l46_one := fun _ _ _ hP hE => GomiE'.isElemAbelian₁ hA hP hE
  l46_two := fun _ _ _ _ hP hE hQ₁ => GomiE'.two₁ hA hP hE hQ₁
  l46_sup := fun _ _ _ hP hE => GomiE'.sup_eq hA hP hE
  l46_index := fun _ _ _ _ hP hE hQ₁ => GomiE'.relIndex₁ hA hP hE hQ₁

end CFSG.CGT.PushingUpLit.C2L
