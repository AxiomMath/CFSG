module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16Sigma
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate27805

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Monster.B.Co2 CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

theorem elAb16_j3R :
    ElAb16 ↥j3R := by
  obtain ⟨-, -, -, -, -, -, -, -, hcard, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  have hC : TS8EA16.checkEA16 6156 (j3StrongArrs[0]!) (j3StrongArrs[1]!) (natArr j3OuterTbl)
      TS8D8.j3SylowWords = true := Certificates.certificate27805.2
  have hRA : permOfArr 6156 (j3StrongArrs[0]!) ∈ j3R :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl rfl))
  have hRB : permOfArr 6156 (j3StrongArrs[1]!) ∈ j3R :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr rfl))
  have hRU : permOfArr 6156 (natArr j3OuterTbl) ∈ j3R :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers j3u)
  have hG : Nat.card j3R = 256 * 392445 := hcard.trans (by norm_num)
  exact TS8EA16.elAb16_of_table hG (by norm_num) hC hRA hRB hRU

theorem elAb16_mulAut_j3P :
    ElAb16 (MulAut ↥j3P) := by
  obtain ⟨e, -⟩ := ctuc_j3_full_automorphism_permutation_model
  exact ElAb16.of_mulEquiv e.symm elAb16_j3R

end CFSG.EvenSporadicStandard.Fin76b
