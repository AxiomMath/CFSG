module

public import CFSG.CGT.Stroth77.Extension218Final

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S]

theorem hasStrothType_t121_or_t131_of_noInvolutionsCentralizing
    [Finite S] {B C S' : Subgroup S} {s : ℕ} {hs : 1 ≤ s}
    (hB : HasStrothType B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothType C (StrothTypeIndex.t121 (s + 3) (by omega)) ∨
    HasStrothType C (StrothTypeIndex.t131 (s + 3) (by omega)) := by
  classical
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c_t221 hB.data hBC hC hrel (hL hB.data.ρ_mem_L) hH hcS
  obtain ⟨d', hd'C, hd'B, hd'2, ε, hε, ⟨bU, hbU, hU⟩, ⟨bR, hbR, hR⟩, ⟨bT, hbT, hT⟩,
      ⟨bV, hbV, hV⟩⟩ := exists_normal_form_t221 hB.data hBC hC hrel hL hdC hdB hd2
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · exact Or.inl (hasStrothType_t121_of_normal_form_t221 hB.data hBC hC hrel hL hd'C hd'B hd'2
      hbU hU hbR hR hbT hT hbV hV)
  · exact Or.inr (hasStrothType_t131_of_normal_form_t221 hB.data hBC hC hrel hL hd'C hd'B hd'2
      hbU hU hbR hR hbT hT hbV hV)

theorem hasStrothTypeOver_t121_or_t131_of_noInvolutionsCentralizing
    [Finite S] {B C S' : Subgroup S} {s : ℕ} {hs : 1 ≤ s}
    (D : StrothTypeData B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t121 (s + 3) (by omega)) ∨
    HasStrothTypeOver D C (StrothTypeIndex.t131 (s + 3) (by omega)) := by
  classical
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c_t221 D hBC hC hrel (hL D.ρ_mem_L) hH hcS
  obtain ⟨d', hd'C, hd'B, hd'2, ε, hε, ⟨bU, hbU, hU⟩, ⟨bR, hbR, hR⟩, ⟨bT, hbT, hT⟩,
      ⟨bV, hbV, hV⟩⟩ := exists_normal_form_t221 D hBC hC hrel hL hdC hdB hd2
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · exact Or.inl (hasStrothTypeOver_t121_of_normal_form_t221 D hBC hC hrel hL hd'C hd'B hd'2
      hbU hU hbR hR hbT hT hbV hV)
  · exact Or.inr (hasStrothTypeOver_t131_of_normal_form_t221 D hBC hC hrel hL hd'C hd'B hd'2
      hbU hU hbR hR hbT hT hbV hV)

end CFSG.CGT.Stroth77
