module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3GSidePlane

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open Subgroup CFSG.Sporadic.Schreier.Co3

theorem nonempty_mulEquiv_co3_of_centralizer
    {G : Type*} [Group G] {s : G}
    (θ : co3M ≃* centralizer ({s} : Set G)) (hθ : (θ co3ZM : G) = s)
    (hH2 : ∀ x : co3M, orderOf x = 2 → (IsConj s (θ x : G) ↔ x = co3ZM ∨ x ∈ classA))
    (hH3 : Nat.card G = 495766656000) :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Co3) := by
  obtain ⟨g, h1, h2⟩ := exists_edge_swap θ hθ hH2
  obtain ⟨sG, hsG, hψ⟩ := exists_edge_involution θ hθ h1 h2
  have hrels : ∀ r ∈ relsV, FreeGroup.lift (letterImg θ sG) (FreeGroup.mk r) = 1 := by
    rw [lift_rels_iff]
    refine ⟨relsC0_letterImg θ sG, ?_, edge_letterImg θ hsG hψ, ?_⟩
    · rw [letterImg_three]
      exact hsG
    · rw [bcb_letterImg, letterImg_three, plane_relator θ hθ hsG hψ,
        wordOf_letterImg θ sG kpWord_letters]
  obtain ⟨e⟩ := vEquivNative
  have : IsSimpleGroup V :=
    @MulEquiv.isSimpleGroup V _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 e.symm
  have hφ4 : vLift (letterImg θ sG) hrels (PresentedGroup.of 4) = s := by
    rw [vLift_of, letterImg_of_ne θ sG (by decide), thetaHom_apply]
    exact theta_me θ hθ
  have hinj : Function.Injective (vLift (letterImg θ sG) hrels) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (vLift (letterImg θ sG) hrels).ker with h | h
    · exact h
    · have h4 : (PresentedGroup.of 4 : V) ∈ (vLift (letterImg θ sG) hrels).ker :=
        h ▸ mem_top _
      rw [MonoidHom.mem_ker, hφ4] at h4
      exact (s_ne_one θ hθ h4).elim
  have hV : Nat.card V = 495766656000 := by
    rw [← Nat.card_congr e.toEquiv, CFSG.Sporadic.Co3.card_Co3]
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hH3]; norm_num)
  have hbij := hinj.bijective_of_nat_card_le (by rw [hH3, hV])
  exact ⟨(MulEquiv.ofBijective _ hbij).symm.trans e.symm⟩

theorem isSporadic_co3_of_centralizer
    {G : Type} [Group G] {s : G}
    (θ : co3M ≃* centralizer ({s} : Set G)) (hθ : (θ co3ZM : G) = s)
    (hH2 : ∀ x : co3M, orderOf x = 2 → (IsConj s (θ x : G) ↔ x = co3ZM ∨ x ∈ classA))
    (hH3 : Nat.card G = 495766656000) : CFSG.Blueprint.NativeSporadic.IsSporadic G .Co3 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3_of_centralizer θ hθ hH2 hH3
  exact ⟨e⟩

end CFSG.EvenSmallLie.SympSix.Co3Ident
