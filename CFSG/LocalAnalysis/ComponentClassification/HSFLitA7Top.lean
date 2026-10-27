module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Full
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGen4
public import CFSG.LocalAnalysis.ComponentClassification.GSLitTripleBranch

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv Blueprint Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer

theorem gen4_of_alternating_seven (hH : HaradaInput) (h48 : FritzA7Sections4to8)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    {t : X} {L : Subgroup X} (h : Config t L)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) : SectRank4 X := by
  by_contra hnot
  obtain ⟨S, -, -⟩ := h.exists_a7Base e hH hnot
  exact hnot (h48 hH X hnonab S)

theorem harris_solomon_fritz_A7_of_parts
    (hGH : UFrontier.GH74ModelsInput)
    (hEven : ∀ (Y : Type) [Group Y] [Finite Y], (LieModel Y .PSL 2 2 3 ∨ LieModel Y .PSL 2 2 4 ∨
      LieModel Y .PSL 3 2 2 ∨ LieModel Y .twistedB2 0 2 3) → ∀ y : Y, orderOf y = 2 → Excluded y)
    (hSpor : ∀ s : TauCeti.SporadicName, (s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1 ∨ s = .J2 ∨
      s = .J3 ∨ s = .McL ∨ s = .Ly) →
      ∀ y : NativeSporadic.Carrier s, orderOf y = 2 → Excluded y)
    (hH : HaradaInput) (h48 : FritzA7Sections4to8) : GSLit.HarrisSolomonFritzA7Input := by
  intro X _ _ _ hnonab t ht L hLt hL ⟨e7⟩ hcyc
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
  obtain ⟨S⟩ : Nonempty (Sylow 2 (L ⧸ pPrimeCore 2 L)) := inferInstance
  have h : Config t L := ⟨ht, hLt, hL, e7.isSimpleGroup,
    GSLit.pRank_two_of_mulEquiv_alternating_seven e7,
    ⟨S, GSLit.card_sylow_two_of_card_eq_2520
      (by rw [Nat.card_congr e7.toEquiv, GSLit.card_alternating_seven]) S⟩, hcyc⟩
  exact Or.inl (oddLieType_of_gen4 hGH hEven hSpor hnonab h
    (gen4_of_alternating_seven hH h48 hnonab h e7))

end CFSG.ComponentClassification.HSFLit
