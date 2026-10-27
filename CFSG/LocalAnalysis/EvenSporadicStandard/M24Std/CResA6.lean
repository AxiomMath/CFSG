module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResWeakA6
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ResidueDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank

theorem residue_cA6_of_table
    (hG : Goldschmidt74Cor4) (hA6 : AutA6Table) :
    Ega81Sit fun _ _ _ _ _ _ _ C _ =>
      Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃* alternatingGroup (Fin 6)) →
        False := by
  intro G _ _ L z _ _ hs A B C D hF he
  have h : CSide.Setup L A C z := ⟨hs, hF.pair.1, hF.sextet, hF.cData, hF.c_elem⟩
  have hty : SextetType L A := hF.pair.sextet
  obtain ⟨hAL, e0, hA⟩ := id hty
  have hσs := Sym6.tetE_surjective hA hAL
  have hσA := Sym6.le_ker_tetE hA
  have hσk := Sym6.card_ker_tetE hA hAL
  obtain ⟨φ, hφ, -⟩ := CSide.exists_hom_centralizer h (Sym6.tetE hA) hσs hσA hσk
  obtain ⟨-, -, hP, -⟩ := CSide.exists_sigma_centralizer h (Sym6.tetE hA) hσs hσA hσk
  have hφk : Nat.card φ.ker = 3 := by
    have c := natCard_eq_of_surjective φ hφ
    rw [hP, Nat.card_prod] at c
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card 2
    have h6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    rw [h2, h6] at c
    omega
  have hStepA := central_of_layer_alt6 (CSide.zt_mul_self h) φ hφ hφk hA6 he
  exact CSide.false_of_stepA hG h hty hStepA

theorem residue_cA6
    (hG : Goldschmidt74Cor4) :
    Ega81Sit fun _ _ _ _ _ _ _ C _ =>
      Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃* alternatingGroup (Fin 6)) →
        False :=
  residue_cA6_of_table hG fun e₀ α hα => DRes.card_fix_involution_alt6 e₀ α hα

end CFSG.EvenSporadicStandard.M24Std
