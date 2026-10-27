module

public import CFSG.ClassicalInvolution.Q3.Q3NMAut
public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance

theorem oddCoreOf_eq_oddCoreIn {G : Type} [Group G] (H : Subgroup G) :
    oddCoreOf H = oddCoreIn H :=
  rfl

theorem alphaOf_eq_bot_of_oddCore {G : Type} [Group G] {A : Subgroup G} (hne : ∃ a ∈ A, a ≠ 1)
    (h : ∀ a ∈ A, a ≠ 1 → oddCoreOf (Subgroup.centralizer ({a} : Set G)) = ⊥) :
    alphaOf A = ⊥ := by
  unfold alphaOf
  have h1 : (⨆ a ∈ A, ⨆ (_ : a ≠ 1), ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) =
      ⊥ := by
    simp only [iSup_eq_bot]
    intro a ha ha1
    rw [h a ha ha1, Subgroup.commutator_bot_left]
  have h2 : (⨅ a ∈ A, ⨅ (_ : a ≠ 1), oddCoreOf (Subgroup.centralizer ({a} : Set G))) = ⊥ := by
    obtain ⟨a, ha, ha1⟩ := hne
    exact le_bot_iff.mp (((iInf₂_le a ha).trans (iInf_le _ ha1)).trans (h a ha ha1).le)
  rw [h1, h2, sup_bot_eq]

section Induced

variable {H : Type} [Group H]

theorem innSubgroup_le_inducedAutOn (L : Subgroup H) : innSubgroup ↥L ≤ inducedAutOn L := by
  rintro _ ⟨l, rfl⟩
  refine ⟨⟨(l : H), Subgroup.le_normalizer l.2⟩, ?_⟩
  ext y
  rfl

theorem alphaOf_inducedImage_eq_bot (L B : Subgroup H) (hL : AutOddFree ↥L)
    (h2 : ∀ x ∈ inducedImage L B, x * x = 1) (hne : ∃ x ∈ inducedImage L B, x ≠ 1) :
    alphaOf (inducedImage L B) = ⊥ := by
  refine alphaOf_eq_bot_of_oddCore hne fun a ha ha1 => ?_
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact h2 a ha) ha1
  exact hL (inducedAutOn L) (innSubgroup_le_inducedAutOn L) a ha2

theorem alphaOf_inducedImage_eq_bot_of_inner (L B : Subgroup H) (hL : AutOddFreeInner ↥L)
    (h2 : ∀ x ∈ inducedImage L B, x * x = 1) (hne : ∃ x ∈ inducedImage L B, x ≠ 1)
    (hinn : ∀ x ∈ inducedImage L B, ((x : ↥(inducedAutOn L)) : MulAut ↥L) ∈ innSubgroup ↥L) :
    alphaOf (inducedImage L B) = ⊥ := by
  refine alphaOf_eq_bot_of_oddCore hne fun a ha ha1 => ?_
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact h2 a ha) ha1
  exact hL (inducedAutOn L) (innSubgroup_le_inducedAutOn L) a (hinn a ha) ha2

end Induced

end CFSG.ClassicalInvolution.Q3.Q3NM
