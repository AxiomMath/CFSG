module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM23

public section

namespace CFSG.QuasithinUnique

open CFSG.Blueprint CFSG.Quasithin Unc25G2.M2x

theorem m22m23Excluded
    : M22M23Excluded := by
  intro G _ _ L S₀ ML hL hMLL hS₀2 hS₀N hsyl hS₀ML hall
  have h6s : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have h7s : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hn6 : ¬ IsPGroup 2 (alternatingGroup (Fin 6)) := not_isPGroup_alternatingGroup 6 (Or.inl (by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide))
  have hn7 : ¬ IsPGroup 2 (alternatingGroup (Fin 7)) := not_isPGroup_alternatingGroup 7 (Or.inr (by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide))
  rcases hL with ⟨⟨ε⟩, hAlt⟩ | ⟨⟨ε⟩, hAlt⟩
  · have : Finite (NativeSporadic.Carrier .M22) := Finite.of_equiv _ ε.toEquiv
    exact m2x_excluded twoE_M22 L S₀ ML ε h6s hn6 hAlt hMLL hS₀2 hS₀N hsyl hS₀ML hall
  · have : Finite (NativeSporadic.Carrier .M23) := Finite.of_equiv _ ε.toEquiv
    exact m2x_excluded twoE_M23 L S₀ ML ε h7s hn7 hAlt hMLL hS₀2 hS₀N hsyl hS₀ML hall

end CFSG.QuasithinUnique
