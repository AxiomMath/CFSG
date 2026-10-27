module

public import CFSG.Quasithin.H13.A5S136r
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136q

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

attribute [local instance] commGroupOfFact

theorem false_of_L34_F4
    (h1323 : Input1323Two_F4) (h1336 : Input1336_F4)
    (h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥)
    (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley) (h42 : AsB42) (h45 : AsB45) (hD310 : D310)
    {K : Subgroup G} (hK : K ∈ cComp S.G1) (hKn : S.G1 ≤ Subgroup.normalizer (K : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) (hL : IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    False := by
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := isSimpleGroup_of_isPSL34 hL
  have hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := (isQuasisimple_of_isPSL34 hL).1
  have hF := S.hypF918_sup_F4 h1323 h1336 h24 hK hKn hKM (L1295B.isQuasisimple_of_simple hperf hS)
  have hHz := S.sup_mem_Hz_F4 h1336 hK hKM
  have hTK := S.T_le_normalizer_of_G1_F4 h1336 hKn
  have hSQ : SQTKGroup ↥(K ⊔ (S.L1 ⊔ T)) := by
    obtain ⟨hk, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian
      (T := T) ⟨le_sup_right.trans le_sup_right, hHz.1.2⟩
    exact ⟨hq, hk⟩
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirr := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFe := factElem hF hIU
  have hirr' : subM S.V1 (conjClosure I (K ⊔ (S.L1 ⊔ T))) I ∈
      IrrPlusOn (autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) (conjClosure K T))
        (orbSup (autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) T)
          (subM S.V1 (conjClosure I (K ⊔ (S.L1 ⊔ T))) I))
        (autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) T) := hirr
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
  have hMp : autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) (conjClosure K T) =
      autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) K := by
    rw [L1295B.conjClosure_eq hTK]
  have hqM := hA.qhat_M hD.sylow.1
  have hne : autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) K ≠ ⊥ := by
    rw [autIH_eq_map hF (le_of_mem_cComp hF.K_cComp)]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨eI⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS hne
  exact false_of_insp4_L34 hA21 hG2 h42 h45 hD310 ⟨hD, hA.qhat_VT hD.exp, hirr'⟩ hMp hqM
    (hA.qOf_VT hD.exp) (isPSL_of_mulEquiv eI.symm hL)

end Setting

theorem endL34K_of_F4
    (h1323 : Input1323Two_F4) (h1336 : Input1336_F4) (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley)
    (h42 : AsB42) (h45 : AsB45) (hD310 : D310) : EndL34K_F4 := by
  intro G _ _ T L V S hC K hK hKn hKM hL
  exact S.false_of_L34_F4 h1323 h1336 (fun g hg hne => (hC.h24 g hg hne).2) hA21 hG2 h42 h45 hD310
    hK hKn hKM hL

end CFSG.Quasithin.H13.A5
