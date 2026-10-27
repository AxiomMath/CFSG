module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLiftClasses

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

open CFSG CFSG.Blueprint CFSG.ComponentClassification.M12Cover

theorem m12_three_involutions
    (a b c : NativeSporadic.M12) (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hc : orderOf c = 2) : IsConj a b ∨ IsConj a c ∨ IsConj b c := by
  have key : ∀ u : NativeSporadic.M12, orderOf u = 2 → IsConj elemR u ∨ IsConj elemZ u := by
    intro u hu
    rcases m12_involution_conj_elemR_or_elemZ u hu with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact Or.inl (isConj_iff.2 ⟨g, hg⟩)
    · exact Or.inr (isConj_iff.2 ⟨g, hg⟩)
  rcases key a ha with h1 | h1
  · rcases key b hb with h2 | h2
    · exact Or.inl (h1.symm.trans h2)
    · rcases key c hc with h3 | h3
      · exact Or.inr (Or.inl (h1.symm.trans h3))
      · exact Or.inr (Or.inr (h2.symm.trans h3))
  · rcases key b hb with h2 | h2
    · rcases key c hc with h3 | h3
      · exact Or.inr (Or.inr (h2.symm.trans h3))
      · exact Or.inr (Or.inl (h1.symm.trans h3))
    · exact Or.inl (h1.symm.trans h2)

theorem isConj_of_equiv' {A B : Type*} [Group A] [Group B] (φ : A ≃* B) {x y : A}
    (h : IsConj (φ x) (φ y)) : IsConj x y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨φ.symm c, φ.injective ?_⟩
  simpa [map_mul, map_inv] using hc

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
