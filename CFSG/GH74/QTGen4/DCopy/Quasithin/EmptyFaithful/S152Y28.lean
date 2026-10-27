module

public import CFSG.Quasithin.EmptyFaithful.S152Y28
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Y27

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement

namespace S152Y

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M : Subgroup G}

theorem isUniqueM_Y_of_five_F4 (hs : Setting152 T Mc M) (h : Data T Mc M) (h5 : StageLemma15205_F4)
    (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥) {n : ℕ} (hn : Odd n)
    (hex : ∀ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M), a ^ n = 1)
    (hact : ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M),
      r * a * r⁻¹ ≠ a) : IsUniqueM (yOf152 T Mc M ⊔ T) M :=
  isUniqueM_of_five_F4 h h5 hs h.yOf_le_M
    (not_le_Mc (h.rc_le_T.trans (T_le_normalizer_yOf T Mc M))
      (odd_orderOf_of_inf_ker_bot h h.yOf_le_M hn hK hex)
      (exists_nontrivial_action h h.yOf_le_M hact))

theorem exists_Y1_iii_F4 (hs : Setting152 T Mc M) (h : Data T Mc M) (h5 : StageLemma15205_F4)
    (c3 : Lemma15203Concl T Mc M) (hiii : Case15203iii T Mc M) : ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁ := by
  obtain ⟨-, hRc2, -, hcard3, hcent, -⟩ := hiii
  have hK := imageOTwoQuot_inf_ker_eq_bot h hcent
  have hex : ∀ a ∈ autOn (yOf152 T Mc M) (V154 T Mc M), a ^ 3 = 1 := fun a ha => by
    have := pow_card_eq_one' (G := ↥(autOn (yOf152 T Mc M) (V154 T Mc M))) (x := ⟨a, ha⟩)
    rw [hcard3] at this
    simpa using congrArg Subtype.val this
  have hact := exists_nontrivial_action_of_comm_eq c3
  exact ⟨yOf152 T Mc M, isY1_Y h hK (by decide) hex
    (isSmallQuot_of_Y_three h hK hcard3 (mul_self_eq_one_of_card_two hRc2) hact)
    (isUniqueM_Y_of_five_F4 hs h h5 hK (by decide) hex hact)⟩

end S152Y

end CFSG.Quasithin
