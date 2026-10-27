module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16Sigma
public import CFSG.Sporadic.SmallOddCore.J2
public import Certificates.Certificate27805

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Monster.B.Co2 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem elAb16_j2R :
    ElAb16 ↥j2R := by
  obtain ⟨-, -, -, -, -, -, -, -, hcard, -⟩ := ctuc_j2_normalizing_involution_permutation_model
  have hC : TS8EA16.checkEA16 315 (j2StrongArrs[0]!) (j2StrongArrs[1]!) (natArr j2OuterTbl)
      TS8D8.j2SylowWords = true := Certificates.certificate27805.1
  have hRA : permOfArr 315 (j2StrongArrs[0]!) ∈ j2R :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl rfl))
  have hRB : permOfArr 315 (j2StrongArrs[1]!) ∈ j2R :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr rfl))
  have hRU : permOfArr 315 (natArr j2OuterTbl) ∈ j2R :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers j2u)
  have hG : Nat.card j2R = 256 * 4725 := hcard.trans (by norm_num)
  exact TS8EA16.elAb16_of_table hG (by norm_num) hC hRA hRB hRU

theorem elAb16_mulAut_j2P :
    ElAb16 (MulAut ↥j2P) := by
  obtain ⟨e, -⟩ := ctuc_j2_full_automorphism_permutation_model
  exact ElAb16.of_mulEquiv e.symm elAb16_j2R

end CFSG.EvenSporadicStandard.Fin76b
