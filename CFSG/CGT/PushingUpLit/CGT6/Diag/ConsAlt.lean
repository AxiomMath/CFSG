module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsAltNat
public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsPair
public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsRestrict

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6.Diag.Cons

theorem diagModAlt_of (hsel : DiagMod_sel) (hb : DiagBoundAlt) : DiagMod_alt := by
  intro V _ _ hV K K' Y t h hcases
  obtain ⟨m, hm5, hmodd, hsec⟩ : ∃ m : ℕ, 5 ≤ m ∧ Odd m ∧
      IsNatSectionBy (altAct m) Y (commV Y) (commV Y ⊓ fixV Y) := by
    rcases hcases with ⟨m, hm5, hmo, hs⟩ | ⟨hX, m, hm7, hmo, ⟨eY⟩⟩
    · exact ⟨m, hm5, hmo, hs⟩
    · exact ⟨m, by omega, hmo, natSection_alt_of_classX hV h.perfY h.centerY hX hm7 eY⟩
  obtain ⟨y₀, hy₀Y, hy₀3, hy₀4⟩ := hb V hV Y m hm5 hmodd hsec
  let S : Set (MulAut V) :=
    {y | y ∈ Y ∧ y ≠ 1 ∧ Nat.card ↥(commV (Subgroup.zpowers y)) ≤ 4}
  have hSY : S ⊆ (Y : Set (MulAut V)) := fun y hy => hy.1
  have hy₀1 : y₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy₀3
    omega
  have hgen : Subgroup.closure S = Y := by
    refine closure_eq_of_conj_invariant h.simpleY hSY ⟨y₀, ⟨hy₀Y, hy₀1, hy₀4⟩, hy₀1⟩ ?_
    rintro s ⟨hsY, hs1, hs4⟩ g hg
    refine ⟨Y.mul_mem (Y.mul_mem hg hsY) (Y.inv_mem hg), ?_, ?_⟩
    · intro h1
      apply hs1
      have : s = g⁻¹ * (g * s * g⁻¹) * g := by group
      rw [this, h1]
      group
    · exact (card_commV_zpowers_conj_le s g).trans hs4
  obtain ⟨W, hW⟩ := exists_minInv K (top_ne_bot h.toDiagPre)
  obtain ⟨y, ⟨hyY, hy1, hy4⟩, w, hwW, hyw⟩ := (hsel V hV K K' Y t h W hW).1 S hSY hgen
  have hcard := ((hsel V hV K K' Y t h W hW).2 y hyY ⟨w, hwW, hyw⟩).2
  have hW4 : Nat.card ↥W ≤ 4 := hcard.trans hy4
  have htriv := apply_eq_of_card_le_four (isPerfect_K h.toDiagPre) hW.2.1 hW4
  obtain ⟨k, hk, w', hw', hne⟩ := exists_move h hW.1
  exact hne (htriv k hk w' hw')

end CFSG.CGT.PushingUpLit.CGT6
