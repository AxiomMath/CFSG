module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265EModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ESetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section Main


set_option linter.unusedSectionVars false

theorem s265e_core {X : Type} [Group X] [Finite X]
    (hXd : ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (X ≃* d.Group))
    {A : Subgroup (MulAut X)} (hA : IsElemAbelian 5 A) (hA3 : 5 ^ 3 ≤ Nat.card A)
    (hAd : A ≤ innAutDerived X) {β : MulAut X} (hβA : β ∈ A) (hβ1 : β ≠ 1) {J : Subgroup X}
    (hJ : IsComponentOf J (fixSubgroup β))
    (hQ : LieModel (↥J ⧸ Subgroup.center ↥J) .twistedB2 0 2 5 ∨
      LieModel (↥J ⧸ Subgroup.center ↥J) .Tits 0 2 1) : False := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hXd
  have hβp : β ^ 5 = 1 := hA.2 β hβA
  have hβ : β ∈ innAutDerived X := hAd hβA
  have hrank : ∀ h : Nat.card A ≤ 5 ^ 2, False := fun h =>
    absurd (hA3.trans h) (by norm_num)
  rcases hQ with hSz | hTi
  · rcases s265e_ident_sz d hd e hβ hβp hβ1 hJ hSz with hS | hF | hT
    · exact hrank (s265e_fin_sz hS hA)
    · exact hrank (s265e_fin_f4 hF hA hAd)
    · exact s265e_order_contra (le_of_eq (s265e_card_tits hT)) hβ1 hJ (Or.inl hSz)
  · exact s265e_order_contra (le_of_eq (s265e_card_tits (s265e_ident_tits d hd e hβ hβp hβ1 hJ hTi)))
      hβ1 hJ (Or.inr hTi)

theorem s265e_false {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 5 S B T x D K) (hE : catalogIs (PSimple 5 K) tyE) : False := by
  obtain ⟨X, _, _, A, β, J, hd, hA, hA3, hAd, hβA, hβ1, hJ, hQ⟩ := s265e_data h hE
  exact s265e_core hd hA hA3 hAd hβA hβ1 hJ hQ

theorem qsFamE_holds : QSFamE := by
  intro p Ω _ _ S B T x D K hN hp5 hE
  subst hp5
  exact (s265e_false hN hE).elim

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end
