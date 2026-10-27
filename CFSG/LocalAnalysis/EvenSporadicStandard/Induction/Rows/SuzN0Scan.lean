module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Data
public import CFSG.Sporadic.SuzOddCore.InvCentralizers
public import CFSG.Certificates.NativeSchreierEnum

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.SuzN0

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

section Scan


theorem invD1_prod3 {G : Equiv.Perm (Fin 1782)} (hG : G ∈ invD 1) :
    ∃ a b c : ℕ, ∃ A B C : Equiv.Perm (Fin 1782),
      a < (levD1 ())[0]!.pts.size ∧ b < (levD1 ())[1]!.pts.size ∧ c < (levD1 ())[2]!.pts.size ∧
      Rep 1782 (levD1 ())[0]!.tr[a]! A ∧ Rep 1782 (levD1 ())[1]!.tr[b]! B ∧
      Rep 1782 (levD1 ())[2]!.tr[c]! C ∧ G = A * B * C := by
  have hA := invFullChain_arrays (i := 1) (by norm_num)
  have hcheck := (invChain_check (i := 1) (by norm_num)).1
  have hF := chainCheckFacts hcheck
  have hb : (invFullChain 1).baseCount = 3 := by
    rw [← hA.base_size]
    rfl
  obtain ⟨a, ha, b, hb', c, hc, hprod⟩ := hA.exists_prod3 (by norm_num) hcheck (by omega)
    (fun i hi hi' => by omega) hG
  exact ⟨a, b, c, _, _, _, ha, hb', hc, hA.rep_levT hF (by omega) ha, hA.rep_levT hF (by omega) hb',
    hA.rep_levT hF (by omega) hc, hprod.symm⟩

end Scan

end CFSG.EvenSporadicStandard.SuzN0
