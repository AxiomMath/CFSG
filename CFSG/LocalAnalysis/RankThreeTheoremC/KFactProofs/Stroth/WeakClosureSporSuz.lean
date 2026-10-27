module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporModule
public import Certificates.Certificate9594
import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open

theorem wcOn_Suz_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.Suz] : WCOn 3 CFSG.Blueprint.NativeSporadic.Suz := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Nat.card CFSG.Blueprint.NativeSporadic.Suz = 448345497600 :=
    CFSG.Sporadic.Suz.card_Suz
  have hf : (Nat.card CFSG.Blueprint.NativeSporadic.Suz).factorization 3 = 7 := by
    rw [hN]
    exact factorization_eq_of_dvd Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
  have h := CFSG.HardMathSupport.Timmesfeld.SporadicRank.sylowData_of_modCheckE
    (CFSG.SectionRank.spec3 64) Nat.prime_three hN
    (by show 3 ^ 7 ∣ 448345497600 ∧ ¬ 3 ^ 8 ∣ 448345497600; norm_num)
    (by show 3 ^ 7 ≤ 9 * 3 ^ 5; norm_num) Certificates.certificate9594
  exact wcOn_of_sylowModuleData h (by rw [hf]; decide)

theorem wcOn_Suz_three
    [Finite (Carrier .Suz)] : WCOn 3 (Carrier .Suz) :=
  wcOn_Suz_three_aux

theorem wcSporadicAt_Suz_of_five
    [Finite (Carrier .Suz)] (h5 : WCOn 5 (Carrier .Suz)) : WCSporadicAt .Suz := by
  refine wcSporadicAt_of_card .Suz (N := 448345497600) CFSG.Sporadic.Suz.card_Suz ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 448345497600 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_Suz_three
  · exact h5
  all_goals (exfalso; norm_num at hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
