module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1RedQuot
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kFactRankTwoUniqueness_of_core (h : K1Core) : KFactRankTwoUniqueness := by
  intro A _ _ X Q B U hK hrk hQX hQp hQs hZc hBQ hBel hBc hUQ hUel hUc hBU hw
    ⟨Y, hYX, hYne, hΓU, hΓ2⟩ W hWX hBUW hcop
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBX : B ≤ X := hBQ.trans hQX
  have hUX : U ≤ X := hUQ.trans hQX
  have hB9 : Nat.card B = 3 ^ 2 := by rw [hBc]; norm_num
  obtain ⟨Qb, hQb⟩ := P64Asm.XBar.exists_sylow hQp.comap_subtype hQs
  have hBpl := P64Asm.XBar.plane hp hQX hQp hBQ hBel hB9
  have hBW : B ≤ normalizer (W : Set A) := le_sup_left.trans hBUW
  have hUW : U ≤ normalizer (W : Set A) := le_sup_right.trans hBUW
  have hcop' : Nat.Coprime (Nat.card W) (2 * 3) := hcop
  have hWb := h (P64Asm.XBar 3 X) Qb _ _ _ (hK.quotient _)
    (K1Red.reduced hrk hQX hQp hUQ hUel hUc hYX hYne hΓU hΓ2 Qb hQb)
    (P64Asm.XBar.cyclic_center hp hQX hQp hZc Qb hQb)
    (by rw [hQb]; exact hBpl.1) hBpl.2.1 (by rw [hBpl.2.2]; norm_num)
    (P64Asm.XBar.not_conj hp hBX hUX (hQp.to_le hBQ) (hQp.to_le hUQ) hBU)
    (P64Asm.XBar.weak_closed hp hQX hQp hBQ hBel hw Qb hQb)
    _ (sup_le (P64Asm.XBar.normalizer_map hBW) (P64Asm.XBar.normalizer_map hUW))
    (P64Asm.XBar.coprime_map hWX hcop')
  exact P64Asm.XBar.le_of_map_eq_bot hWX hWb

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
