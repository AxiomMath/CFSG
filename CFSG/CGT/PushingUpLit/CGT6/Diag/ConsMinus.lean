module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsPair
public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsRestrict

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6.Diag.Cons

theorem diagModMinus_of (hsel : DiagMod_sel) (hs2 : DiagMod_s2) (hb : DiagBoundMinus) :
    DiagMod_minus := by
  intro V _ _ hV K K' Y t h n hn hsec
  have hsec' := hsec
  obtain ⟨-, θY, -⟩ := hsec'
  obtain ⟨⟨θK⟩, -⟩ := hs2 V hV K K' Y t h (2 * n) (by omega) ⟨θY⟩
  obtain ⟨y₀, hy₀Y, hy₀1, hy₀odd, hy₀lt⟩ := hb V hV Y n hn hsec
  let S : Set (MulAut V) := {y | y ∈ Y ∧ y ≠ 1 ∧ Odd (orderOf y) ∧
    Nat.card ↥(commV (Subgroup.zpowers y)) < 2 ^ (4 * n)}
  have hSY : S ⊆ (Y : Set (MulAut V)) := fun y hy => hy.1
  have hgen : Subgroup.closure S = Y := by
    refine closure_eq_of_conj_invariant h.simpleY hSY
      ⟨y₀, ⟨hy₀Y, hy₀1, hy₀odd, hy₀lt⟩, hy₀1⟩ ?_
    rintro s ⟨hsY, hs1, hsodd, hslt⟩ g hg
    refine ⟨Y.mul_mem (Y.mul_mem hg hsY) (Y.inv_mem hg), ?_, ?_, ?_⟩
    · intro h1
      apply hs1
      have : s = g⁻¹ * (g * s * g⁻¹) * g := by group
      rw [this, h1]
      group
    · rw [orderOf_conj_eq]
      exact hsodd
    · exact lt_of_le_of_lt (card_commV_zpowers_conj_le s g) hslt
  obtain ⟨W, hW⟩ := exists_minInv K (top_ne_bot h.toDiagPre)
  obtain ⟨y, ⟨hyY, hy1, hyodd, hylt⟩, w, hwW, hyw⟩ :=
    (hsel V hV K K' Y t h W hW).1 S hSY hgen
  have hcard := ((hsel V hV K K' Y t h W hW).2 y hyY ⟨w, hwW, hyw⟩).2
  have hlow := two_pow_le_card_of_minInv hV h.quasi (fixV_eq_bot h) (f := 2 * n) (by omega) θK hW
  have h4 : 2 ^ (2 * (2 * n)) = 2 ^ (4 * n) := by
    congr 1
    omega
  omega

end CFSG.CGT.PushingUpLit.CGT6
