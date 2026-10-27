module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Glue
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.SmallOddCore.HSMcL
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67J1Red

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem no911_mathieu
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (h : Nonempty (Y ≃* NativeSporadic.M11) ∨ Nonempty (Y ≃* NativeSporadic.M12) ∨
      Nonempty (Y ≃* NativeSporadic.M22) ∨ Nonempty (Y ≃* NativeSporadic.M23)) : No911 Y := by
  refine no911_of_oddCore hs hna fun X _ _ S _ hSY hC t ht => ?_
  obtain ⟨ψ⟩ := hSY
  refine Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
    S ?_ hC t ht
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨ψ.trans e⟩
  · exact Or.inr (Or.inl ⟨ψ.trans e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ψ.trans e⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ.trans e⟩)))

theorem no911_j2
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (h : Nonempty (Y ≃* NativeSporadic.J2)) : No911 Y := by
  refine no911_of_oddCore hs hna fun X _ _ S _ hSY hC t ht => ?_
  obtain ⟨ψ⟩ := hSY
  obtain ⟨e⟩ := h
  exact Sporadic.SmallOddCore.ctuc_j2_almost_simple_involution_centralizer_odd_core_trivial
    S ⟨ψ.trans e⟩ hC t ht

theorem no911_j3
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (h : Nonempty (Y ≃* NativeSporadic.J3)) : No911 Y := by
  refine no911_of_oddCore hs hna fun X _ _ S _ hSY hC t ht => ?_
  obtain ⟨ψ⟩ := hSY
  obtain ⟨e⟩ := h
  exact Sporadic.SmallOddCore.ctuc_j3_almost_simple_involution_centralizer_odd_core_trivial
    S ⟨ψ.trans e⟩ hC t ht

theorem no911_mcl
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (h : Nonempty (Y ≃* NativeSporadic.McL)) : No911 Y := by
  refine no911_of_oddCore hs hna fun X _ _ S _ hSY hC t ht => ?_
  obtain ⟨ψ⟩ := hSY
  obtain ⟨e⟩ := h
  exact Sporadic.SmallOddCore.ctuc_hs_mcl_almost_simple_involution_centralizer_odd_core_trivial S
    (Or.inr ⟨ψ.trans e⟩) hC t ht

theorem no911_j1
    {Y : Type} [Group Y] [Finite Y] (h : Nonempty (Y ≃* NativeSporadic.J1)) : No911 Y := by
  rintro p V z ⟨hp, hpodd, -, hVc, -⟩
  obtain ⟨e⟩ := h
  have hsurj : Function.Surjective
      (MulAut.conj : NativeSporadic.J1 →* MulAut NativeSporadic.J1) :=
    fun φ => (Sporadic.Schreier.at_j1_schreier.2.1 φ).imp fun g hg => hg.symm
  have h1 : Nat.card ↥V ∣ Nat.card (MulAut Y) := Subgroup.card_subgroup_dvd_card V
  have h2 : Nat.card (MulAut Y) = Nat.card (MulAut NativeSporadic.J1) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have h3 : Nat.card (MulAut NativeSporadic.J1) ∣ Nat.card NativeSporadic.J1 :=
    Subgroup.card_dvd_of_surjective hsurj
  rw [Sporadic.J1.card_J1] at h3
  rw [hVc, h2] at h1
  exact Thm1.not_sq_dvd_card_J1 p hp hpodd (h1.trans h3)

theorem core911_spor
    : Core911Spor := by
  intro Y _ _ hs hna h
  rcases h with h | h | h | h | h | h | h
  · exact no911_mathieu hs hna (Or.inl h)
  · exact no911_mathieu hs hna (Or.inr (Or.inl h))
  · exact no911_mathieu hs hna (Or.inr (Or.inr (Or.inl h)))
  · exact no911_mathieu hs hna (Or.inr (Or.inr (Or.inr h)))
  · exact no911_j1 h
  · exact no911_j2 hs hna h
  · exact no911_j3 hs hna h

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
