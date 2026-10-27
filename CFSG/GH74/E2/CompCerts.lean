module

public import CFSG.GH74.Generic.Certificates
import CFSG.GH74.E2.CompCertsBasic
import CFSG.GH74.E2.CompCertsJ2
import CFSG.GH74.E2.CompCertsJ3
import CFSG.GH74.E2.CompCertsMathieu
import CFSG.GH74.E2.CompCertsU33
import CFSG.GH74.E2.CompCertsU34
import CFSG.GH74.E2.CompCertsU42
import CFSG.GH74.Generic.AltCerts
import CFSG.GH74.Generic.ExceptionalRank

public section

namespace CFSG.GH74.E2

open CFSG.GH74.Generic CFSG.Blueprint

section Level3

variable {S : Type} [Group S]

theorem rank3_L2_16 (h : LieModel S .PSL 2 2 4) : RankCertified S 3 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data h
  exact (rankCertified_psl_even hF le_rfl (by norm_num)).of_mulEquiv e.symm

theorem rank3_L3_4 (h : LieModel S .PSL 3 2 2) : RankCertified S 3 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data h
  exact (rankCertified_psl_even hF (by norm_num) (by norm_num)).of_mulEquiv e.symm

theorem rank3_U3_4 (h : LieModel S .PSU 3 2 2) : RankCertified S 3 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data h
  exact (rankCertified_SU3_four (q := 2 ^ 2) (by norm_num) hF).of_mulEquiv e.symm

theorem rank3_L4_2 (h : LieModel S .PSL 4 2 1) : RankCertified S 3 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data h
  exact (rankCertified_psl_even hF (by norm_num) (by norm_num)).of_mulEquiv e.symm

theorem rank3_A8 (e : S ≃* alternatingGroup (Fin 8)) : RankCertified S 3 :=
  rankCertified_alternating_eight.of_mulEquiv e.symm

theorem rank3_U4_2 (h : LieModel S .PSU 4 2 1) : RankCertified S 3 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data h
  exact (rankCertified_SU4_two (q := 2 ^ 1) (by norm_num) hF).of_mulEquiv e.symm

theorem rank3_PSp4_3 (h : LieModel S .PSp 2 3 1) : RankCertified S 3 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psp_data h
  exact (rankCertified_PSp4
    (ringChar_ne_two_of_card_eq Nat.prime_three (by norm_num) hF)).of_mulEquiv e.symm

theorem rank3_L4_3 (h : LieModel S .PSL 4 3 1) : RankCertified S 3 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data h
  exact (rankCertified_PSL4
    (ringChar_ne_two_of_card_eq Nat.prime_three (by norm_num) hF)).of_mulEquiv e.symm

theorem rank3_U4_3 (h : LieModel S .PSU 4 3 1) : RankCertified S 3 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data h
  exact (rankCertified_PSU4 hF (by norm_num)).of_mulEquiv e.symm

theorem rank3_G2_3
    (h : LieModel S .G2 0 3 1) : RankCertified S 3 :=
  rankCertified_of_lieModel_G2 Nat.prime_three (by norm_num) h

theorem rank3_M12 (h : NativeSporadic.IsSporadic S .M12) : RankCertified S 3 :=
  rankCertified_of_isSporadic_M12 h

theorem rank3_M22 (h : NativeSporadic.IsSporadic S .M22) : RankCertified S 3 :=
  rankCertified_of_isSporadic_M22 h

theorem rank3_M23 (h : NativeSporadic.IsSporadic S .M23) : RankCertified S 3 :=
  rankCertified_of_isSporadic_M23 h

theorem rank3_J2
    (h : NativeSporadic.IsSporadic S .J2) : RankCertified S 3 :=
  rankCertified_of_isSporadic_J2 h

theorem rank3_J3
    (h : NativeSporadic.IsSporadic S .J3) : RankCertified S 3 :=
  rankCertified_of_isSporadic_J3 h

end Level3

section Level2

variable {S : Type} [Group S]

theorem rank2_L2_8 (h : LieModel S .PSL 2 2 3) : RankCertified S 2 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data h
  exact (rankCertified_psl_even hF le_rfl (by norm_num)).of_mulEquiv e.symm

theorem rank2_U3_3 (h : LieModel S .PSU 3 3 1) : RankCertified S 2 := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data h
  exact (rankCertified_SU3_mod_four hF (by norm_num)).of_mulEquiv e.symm

theorem rank2_Sz8
    (h : LieModel S .twistedB2 0 2 3) : RankCertified S 2 := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hmodel⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := hmodel
    have ha : a = 1 := by omega
    subst ha
    exact (rankCertified_suzukiGroup (by simpa using hK) (by norm_num)).of_mulEquiv e.symm

end Level2

end CFSG.GH74.E2
