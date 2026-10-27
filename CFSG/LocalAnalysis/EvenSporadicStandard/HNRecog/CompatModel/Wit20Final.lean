module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.WitTransport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.CompatModel

section Cert


theorem wit20_holds : Wit20 := by
  intro G _ a z h b hb t ht hta htb htab
  have hba : b * a = a * b := (mem_Gx.1 (h.mem_Gx_of_orb2A (IsConj.refl a) hb)).symm
  have hab : a ∈ orb2A a b := ⟨IsConj.refl a, by rw [hba]; exact hb.2⟩
  obtain ⟨w, hw1, hw2, hw3, -, -⟩ := exists_vertex_in_Gx h hb.1 hab ht htb hta htab
  exact ⟨w, hw2, hw1, hw3⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section4
