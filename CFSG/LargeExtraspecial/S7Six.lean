module

public import CFSG.LargeExtraspecial.S7One
public import CFSG.LargeExtraspecial.S7Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.Open

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem timmesfeld_7_6 (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hR : Rbar S g t ≠ S.Lbar g) (hN : Nbar S g t = zpowers t) (hn : 5 ≤ S.width) :
    ∃ hVQ : ¬ V S g t ≤ S.Qa g, OmegaCase H C ht ht1 hVQ ∧
      S.width = finrank (ZMod 2) (Vt S g t) ∧
      (S.width = 6 ∨
        (8 ≤ S.width ∧ (∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) ∧
          (∀ y : S.Mbar, y * ⟨t, S.Lbar_le_Mbar g ht⟩ * y⁻¹ *
            (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar)⁻¹ ∈ timmesfeldOddCore S.Mbar) ∧
          timmesfeldOddCore S.Mbar ≠ ⊥)) := by
  rcases timmesfeld_4_5 H hNo C ht ht1 with h | hL | ⟨hVQ, hSp | hA | hΩ | hP⟩
  · exact absurd h hR
  · exact (timmesfeld_7_1 H hNo C ht ht1 hN hL).elim
  · exact (not_spCase H hNo C ht ht1 hN hCE hSp).elim
  · have := timmesfeld_7_5 H C ht ht1 hN hA
    omega
  · have hw := width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ
    obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
    have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by omega
    refine ⟨hVQ, hΩ, hw, ?_⟩
    rcases (timmesfeld_7_3 hCE H hNo C ht ht1 hVQ hΩ hN h6).2 with h | ⟨h8, hSC⟩
    · exact Or.inl (by omega)
    · obtain ⟨hZ, hO⟩ := timmesfeld_7_4 hCE H hNo C ht ht1 hVQ hΩ hN h8
      exact Or.inr ⟨by omega, hSC, hZ, hO⟩
  · have := width_eq_four_of_pgl25Case H C ht ht1 hN hP
    omega

end CFSG.LargeExtraspecial.S7
