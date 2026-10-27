module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Thm21Lemma15
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Lemma15Guarded
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Sol78LitHered

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open CFSG.EvenSporadicStandard.Induction

theorem sol78Thm21At_of_lemma15At {G : Type} [Group G] [Finite G] (h15 : FS79Lemma15At G) :
    Sol78Thm21At G :=
  fun hkp hO _ _ hS hT hST _ hK =>
    ⟨layerIn_inf_le_of_lemma15At h15 hkp hO hS hT hST hK,
      fun hTK => exists_isCompIn_of_lemma15At h15 hkp hO hS hT hST hK hTK⟩

theorem sol78Thm21Hered_of_lemma15 (h15 : FS79Lemma15Hered) : Sol78Thm21Hered :=
  fun G _ _ hG => sol78Thm21At_of_lemma15At (h15 G hG)

end CFSG.EvenSporadicStandard.Induction.Junction
