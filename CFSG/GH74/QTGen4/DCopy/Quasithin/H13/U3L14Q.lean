module

public import CFSG.Quasithin.H13.U3L14Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14J

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem kData_of_F4 (h1332 : Stmt13_3_2_F4) (h1336 : A6.Stmt13_3_6_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) {K : Subgroup G}
    (hK : K ∈ cComp (A6.g1 T V))
    (hc : CFSG.IsComponent ((K.subgroupOf (A6.g1 T V)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)))))
    (hKA : ¬ ⁅K, pCoreOf 2 Lp⁆ ≤ pCoreOf 2 (A6.g1 T V)) : KData14 T L V V₂ Lp K := by
  obtain ⟨hΩ, hfK, hTK, hHK, hLK, hKM⟩ := S.stepE_F4 h1332 h1336 h37 h38 h39 hQ hK
  have hLpK : Lp ≤ normalizer (K : Set G) := S.Lp_G1.trans hHK
  exact
    { mem := hK
      comp := hc
      quasi := isQuasisimple_quot_of_isComponent hK hc
      comm := hKA
      omega := hΩ
      faithful := hfK
      T_K := hTK
      G1_K := hHK
      L_K := hLK
      K_M := hKM
      L2_K := S.stepF hHK hLK
      Lp_K := hLpK
      eqLp := commutator_eq_of_isComponent_of_le hK hc S.Lp_G1 hLpK
        (LieType.BorelTits.pCoreOf_le 2 Lp) hKA }

theorem exists_kData_F4 (h1332 : Stmt13_3_2_F4) (h1336 : A6.Stmt13_3_6_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) (hd : StepD T V Lp) :
    ∃ K : Subgroup G, KData14 T L V V₂ Lp K := by
  obtain ⟨K, hK, hc, hKA⟩ := S.exists_K hQ hd
  exact ⟨K, S.kData_of_F4 h1332 h1336 h37 h38 h39 hQ hK hc hKA⟩

theorem K_eq_comm_J_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow)
    {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) : ⁅K, thompsonJ T⁆ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hKH : K ≤ A6.g1 T V := le_of_mem_cComp hD.mem
  refine commutator_eq_of_isComponent_of_le hD.mem hD.comp (hJT.trans S.T_G1)
    (hJT.trans hD.T_K) le_rfl fun hle => ?_
  apply (S.ff_K_F4 h1332 hC58 h317 hD.faithful hD.quasi hD.G1_K hD.L2_K).1
  rw [(S.reduced_K_F4 h1332 hD.faithful hD.quasi).2]

  have hcomm : ⁅K, thompsonJ T⁆ ≤ pCoreOf 2 K := by
    refine le_trans (le_inf (commutator_le_of_le_normalizer (hJT.trans hD.T_K)) hle) ?_
    refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ K
      inf_le_left ?_ ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun k hk => ?_
    exact mem_normalizer_inf (le_normalizer hk)
      (LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hKH hk))

  have hKT : (K.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hD.T_K)
  have hO2K : pCoreOf 2 K ≤ T :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K (K ⊔ T)
      le_sup_left hKT).trans (pCoreOf_two_le_of_isSylowTwoOf (S.syl le_sup_right))

  set P := pCoreOf 2 K ⊔ thompsonJ T with hP
  have hPT : P ≤ T := sup_le hO2K hJT
  have hkey : ∀ g ∈ K, P ≤ P.comap (MulAut.conj g).toMonoidHom := by
    intro g hg
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact le_sup_left (a := pCoreOf 2 K)
        ((mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 K hg) a).mp ha)
    · show g * b * g⁻¹ ∈ P
      have h1 : g * b * g⁻¹ * b⁻¹ ∈ pCoreOf 2 K :=
        hcomm (commutator_mem_commutator hg hb)
      have : g * b * g⁻¹ = (g * b * g⁻¹ * b⁻¹) * b := by group
      rw [this]
      exact mul_mem (le_sup_left (a := pCoreOf 2 K) h1) (le_sup_right (b := thompsonJ T) hb)
  have hKP : K ≤ normalizer (P : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hkey g hg hx, fun hx => ?_⟩
    have := hkey g⁻¹ (inv_mem hg) hx
    simpa [mul_assoc] using this
  have hTP : T ≤ normalizer (P : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    have hsub : ∀ s ∈ T, P ≤ P.comap (MulAut.conj s).toMonoidHom := by
      intro s hs
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact le_sup_left (a := pCoreOf 2 K)
          ((mem_normalizer_iff.mp ((hD.T_K.trans
            (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)) hs) a).mp ha)
      · exact le_sup_right (b := thompsonJ T)
          ((mem_normalizer_iff.mp (normalizer_le_normalizer_thompsonJ T (le_normalizer hs)) b).mp
            hb)
    refine ⟨fun hx => hsub t ht hx, fun hx => ?_⟩
    have := hsub t⁻¹ (inv_mem ht) hx
    simpa [mul_assoc] using this
  have hPn : (P.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hPT.trans le_sup_right)).2 (sup_le hKP hTP)
  exact (le_sup_right (a := pCoreOf 2 K)).trans
    (CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 P (K ⊔ T)
      (hPT.trans le_sup_right) hPn (S.isP_T.to_le hPT))

end Set14

end CFSG.Quasithin.H13.U3
