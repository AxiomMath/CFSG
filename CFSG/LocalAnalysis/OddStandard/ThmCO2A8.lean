module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8Odd
public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8Trans
public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8Split
public import CFSG.LocalAnalysis.OddStandard.ThmCO2Defs

public section

namespace CFSG.OddStandard.ThmC.O2.A8

open CFSG Subgroup

theorem a8Fact : A8Fact := by
  intro K _ _ A _ _ hcomm hsq hA ρ hρ _ V hV4 hVsq Z hZ4 hfix hnot
  have h : Hyp ρ V Z := ⟨hcomm, hsq, hA, hρ, hV4, hVsq, hZ4, hfix, hnot⟩
  refine ⟨?_, h.transitive⟩
  obtain ⟨e, f, hf, hodd, -, hker⟩ := h.quot_A5
  obtain ⟨hM, h3⟩ := h.odd_core
  have hpc : f.ker = pPrimeCore 2 K := by
    apply le_antisymm
    · have hn : f.ker.Normal := f.normal_ker
      exact le_sSup ⟨hn, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by simpa [← even_iff_two_dvd, Nat.not_even_iff_odd] using hodd)⟩
    · intro k hk
      exact (hker k).2 fun W => hM W hk
  exact a5_or_z3a5 f hf (hpc ▸ h3)

end CFSG.OddStandard.ThmC.O2.A8
