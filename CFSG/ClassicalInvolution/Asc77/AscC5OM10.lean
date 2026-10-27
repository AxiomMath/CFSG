module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM3
public import CFSG.ClassicalInvolution.Asc77.AscC5OM5
public import CFSG.ClassicalInvolution.Asc77.AscC5OM8
public import CFSG.ClassicalInvolution.Asc77.AscC5OM9

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem odd_card_gf (hp : p ≠ 2) (hq : 5 ≤ p ^ f) : Odd (Nat.card (GaloisField p f)) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow

theorem sl2PerfectAut_proved : SL2PerfectAut p f := by
  intro hp hq P hP
  have h5 := M.five_le_card_gf hq
  exact M.two_mul_card_le_of_perfect (odd_card_gf hp hq) (by omega) P hP


theorem om5Centerless_proved : Om5Centerless p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD y hy
  obtain ⟨fr⟩ := M.exists_frame hD
  have h5 := M.five_le_card_gf hD.five
  exact fr.centerless (by omega) hy

theorem om5InvFixFour_proved : Om5InvFixFour p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD y hy2 _
  obtain ⟨fr⟩ := M.exists_frame hD
  exact fr.invFixFour (M.two_ne_zero_gf f hD.odd) hy2

theorem om5InnerOfTwin_proved : Om5InnerOfTwin p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD β _ _ hin
  obtain ⟨fr⟩ := M.exists_frame hD
  have h5 := M.five_le_card_gf hD.five
  exact fr.innerOfTwin (M.two_ne_zero_gf f hD.odd) (by omega) β hin

theorem om5TwinOfInner_proved : Om5TwinOfInner p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD y hy
  obtain ⟨fr⟩ := M.exists_frame hD
  exact fr.twinOfInner (M.two_ne_zero_gf f hD.odd) hD.twin.ne hD.twin.hzA hy

theorem om5Interchange_proved : Om5Interchange p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD β t' ht' hne hcomm
  obtain ⟨fr⟩ := M.exists_frame hD
  exact fr.interchange (M.two_ne_zero_gf f hD.odd) (odd_card_gf hD.odd hD.five) hD.twin.hzA
    hD.twin.ha₀ hD.twin.hb₀ hD.twin.ha₀sq hD.twin.hb₀sq β t' ht' hne hcomm

theorem om5ZSwap_proved : Om5ZSwap p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD
  obtain ⟨fr⟩ := M.exists_frame hD
  exact fr.zSwap (M.two_ne_zero_gf f hD.odd)

theorem om5USwapNotZ_proved : Om5USwapNotZ p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD s hs hsz β
  obtain ⟨fr⟩ := M.exists_frame hD
  exact fr.uSwapNotZ (M.two_ne_zero_gf f hD.odd) hD.twin.ne hD.twin.hzA hD.twin.hzA' hs hsz β

end CFSG.ClassicalInvolution.Asc77.C5O
