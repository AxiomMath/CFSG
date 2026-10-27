module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagUnitary

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem not_seven_dvd_two_pow_add_one (f : ℕ) : ¬ 7 ∣ 2 ^ f + 1 := by
  have h2 : ∀ k : ℕ, 2 ^ k % 7 = 1 ∨ 2 ^ k % 7 = 2 ∨ 2 ^ k % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h | h <;> rw [h] <;> norm_num
  intro h7
  have := h2 f
  omega

theorem kFactLieOutDiagLevi_of_bad (hdich : LieOutDich) (hbad : DiagLeviBad) :
    KFactLieOutDiagLevi := by
  intro Y _ _ L J hL hcl hpar hne hnB p hp57 x hx hxp hxo hN hfix
  have hpp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp57 with rfl | rfl <;> norm_num
  rcases hdich Y L hL hcl p hpp hp5 x hx hxp hxo with hdiag | ⟨hconcl, -⟩
  · rcases hdiag with ⟨n, f, hmodel, hpg⟩ | ⟨n, f, hmodel, hpg⟩
    · exact exists_quasisimple_of_model_psl hp57 hmodel (hpg.trans (Nat.gcd_dvd_right _ _))
        hpar hnB
    · have hp : p = 5 := by
        rcases hp57 with rfl | rfl
        · rfl
        · exact absurd (hpg.trans (Nat.gcd_dvd_right _ _)) (not_seven_dvd_two_pow_add_one f)
      subst hp
      exact exists_quasisimple_of_model_psu hbad hL hcl hpar hne hnB hmodel hpg hx hxp hxo hN hfix
  · exact absurd (hconcl J hpar hfix) hne

end CFSG.AGLEmbedding.LieOut
