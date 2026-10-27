module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem i167CS_size_aux1 {N : ℕ} (hN : 0 < N) (hv : 10 ≤ padicValNat 2 N) : 720 < N := by
  have h1 : 2 ^ padicValNat 2 N ∣ N := pow_padicValNat_dvd
  have h2 : 2 ^ padicValNat 2 N ≤ N := Nat.le_of_dvd hN h1
  have h3 : 2 ^ 10 ≤ 2 ^ padicValNat 2 N := Nat.pow_le_pow_right (by norm_num) hv
  norm_num at h3
  omega

theorem i167CS_card_gt (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S] {p : ℕ}
    {J : Subgroup S} (h : Type167J p J) : 720 < Nat.card (PSimple p J) := by
  have hpos : 0 < Nat.card (PSimple p J) := Nat.card_pos
  rcases h with ⟨h3, n, -, hn5, h⟩ | ⟨h3, n, -, hn6, h⟩ | ⟨n, k, -, hn3, hnk, hk, -, h⟩
  · subst h3
    obtain ⟨-, -, hv⟩ := S172.v2_isLnA hb (f := 1) le_rfl (by rw [pow_one]; exact h)
    have h20 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hn5 (by omega)
    exact i167CS_size_aux1 hpos (by omega)
  · subst h3
    obtain ⟨-, hv⟩ := S172.v2_isOmMA hb (f := 1) le_rfl (by rw [pow_one]; exact h)
    have h30 : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul hn6 (by omega)
    exact i167CS_size_aux1 hpos (by omega)
  · obtain ⟨-, hv⟩ := S172.v2_isOmPA hb hk h
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · obtain rfl : k = 1 := by omega
      have h20 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (hnk rfl) (by have := hnk rfl; omega)
      exact i167CS_size_aux1 hpos (by omega)
    · have h6 : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn3 (by omega)
      have h12 : 2 * (3 * 2) ≤ k * (n * (n - 1)) := Nat.mul_le_mul hk2 h6
      exact i167CS_size_aux1 hpos (by omega)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
