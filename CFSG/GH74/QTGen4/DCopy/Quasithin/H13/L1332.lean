module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L1332Modules
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.H13.L1332Local
public import CFSG.Quasithin.H13.StatementsL4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem stmt13_3_2_of_inputs_F4
    (hD : LocalDoubleEmbeddingExclusion) (h137 : Stmt13_1_7_F4)
    (h1312 : Stmt13_1_2_three_F4) (h323 : Stmt3_2_3) (h1222 : Stmt12_2_2_F4) (h1242 : Stmt12_4_2_F4)
    (h1271 : Stmt12_7_1_F4) (hodd : FiveQuotientOddIndexSolvable) (hL32 : L32NoIrrFour) :
    Stmt13_3_2_F4 := by
  intro G _ _ T L hH K hK
  obtain ⟨hs, hnab, hQ, hT, -, hexcl, ha5⟩ := hH
  obtain ⟨I, ⟨hImax, hIf⟩, hKI⟩ := faithful_maximal_local_exists hD hs hnab hQ hT hK
  have hIq := h137 G T hs hnab hQ hT hexcl I hIf
  have hI5 := h1312 G T I hs hnab hQ hT hexcl hImax hIf hIq
  have hnalt : ¬ Alt12_2_2 G := fun h => hexcl (qt13Excluded_of_alt12_2_2 h)
  obtain ⟨hTI, hIex, hIall⟩ := ((h1222 G T hs hnab hQ hT).resolve_left hnalt) I hImax hIf hIq
  have hKeq : K = I :=
    eq_of_faithfulLocal_le hD hodd hs hnab hQ hT hK hImax hIf hKI hTI hIq hI5
  subst hKeq
  obtain ⟨⟨hM, -⟩, ⟨-, huniq⟩, -⟩ := h323 G T K hs hnab hQ hT hImax hIf hIq
  rw [conjClosure_eq_self_of_normalizes hTI] at hM huniq
  refine ⟨hI5, ⟨hTI, hImax, hM, huniq⟩, ⟨hIex, fun V hV => ?_⟩, fun h => ?_⟩
  · obtain ⟨⟨hVT, hTV, hred, hfsu⟩, -, -, hcomm, hmod⟩ := hIall V hV
    have hH' : Hyp1223 G T K V := ⟨hs, hnab, hQ, hT, hnalt, hImax, hIf, hIq, hTI, hV⟩
    exact ⟨hVT, hTV, hfsu, hcomm,
      modules13_3_2_of_modules12_2_2_F4 h1242 h1271 hL32 hH' hexcl hI5 hred hVT hmod⟩
  · exact
      { simple := hs
        nonabelian := hnab
        qtke := hQ
        sylow := hT
        faithful := hK
        not_excluded := hexcl
        a5 := fun hKa5 => ha5 (h.resolve_left fun hn => hn hKa5) }

theorem stmt13_3_2_two_of_F4 (h : Stmt13_3_2_F4) : Stmt13_3_2_two_F4 :=
  fun G _ _ T L hH K hK => (h G T L hH K hK).2.1

theorem stmt13_3_2_three_fsu_of_F4 (h : Stmt13_3_2_F4) : Stmt13_3_2_three_fsu_F4 := by
  intro G _ _ T L hH K hK
  refine ⟨(h G T L hH K hK).2.2.1.1, fun V hV => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := (h G T L hH K hK).2.2.1.2 V hV
  exact ⟨h1, h2, h3⟩

end CFSG.Quasithin.H13
