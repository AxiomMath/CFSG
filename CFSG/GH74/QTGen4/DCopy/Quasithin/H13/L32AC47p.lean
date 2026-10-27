module

public import CFSG.Quasithin.H13.L32AC47p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC47o
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

theorem lemma14_7_47_l32Mod_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hA21 : AsA21SQTKSection) (hD310 : D310) (hD391 : D391)
    (hI4 : Insp4) (h30 : Lemma14_7_30_F4) (h32 : Lemma14_7_32_F4) : Lemma14_7_47_L32Mod_F4 := by
  intro G _ _ T L V H S K hK hHeq hP _ hcomm t ht hout
  obtain ⟨-, -, -, hF⟩ := h30 G T L V H S K hK
  have hTK := h32 G T L V H S K hK
  have hK₀ : conjClosure K T = K :=
    le_antisymm
      (conjClosure_le fun _ ht k hk => (Subgroup.mem_normalizer_iff.mp (hTK ht) k).mp hk)
      (le_conjClosure K T)
  rw [hK₀, ← hHeq] at hF
  have hSQ := sqtkGroup_of_setting S
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have := factElem hF hIU
  have h4 := (F918_4' hF hSQ hK₀ hV₁I hIU W hW hirrU hD310 hD391 hI4).2
  rcases h4 with hHI | (⟨hVT, -⟩ | h3)
  ·
    exact false_of_T_le_normalizer_I hA21 S hF hK₀ hP hV₁I hIU hirrT
      (hF.T_le_H.trans hHI) ht hout
  ·
    have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
      intro t' ht'
      have hst := mem_stabSub_of_eq_orbSup_T hVT
        (actH_mem_autIH_of_mem (I := I) hF hF.T_le_H ht')
      exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
        (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
        (le_conjClosure I H) ⟨t', hF.T_le_H ht'⟩).mp hst
    exact false_of_T_le_normalizer_I hA21 S hF hK₀ hP hV₁I hIU hirrT hTI ht hout
  ·
    exact false_of_d310Two_F4 h1222 h1332 h1334 S hF hK₀ hHeq hP hcomm hV₁I hIU hirrT h3

end CFSG.Quasithin.H13.L32A.C
