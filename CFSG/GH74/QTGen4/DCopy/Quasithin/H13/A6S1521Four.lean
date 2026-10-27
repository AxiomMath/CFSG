module

public import CFSG.Quasithin.H13.A6S1521Four
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1512

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem input13521Four_of_cent_F4
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (h38 : A38ForSQTK)
    (hF : A5.Facts1321) (hR : A5.FactRankRows1321) (hA7 : A5.FactA7Grp1321)
    (hL3 : A5.FactL3Grp1321) (hO : A5.FactOutRows1321) (hC : FactCentRows1321) :
    Input13521Four_F4 := by
  intro G _ _ T L V S hNS hna hhat
  have hG1 := S.G1_mem_Hz_of_nonabelian hna
  have hVG1 : V ≤ S.G1 := (S.toA5Sit_F4 hNS h13315 h1356two hG1 hna).V_le_H
  obtain ⟨v, hv, hvQ⟩ : ∃ v ∈ V, v ∉ pCoreOf 2 S.G1 :=
    Set.not_subset.mp (S.toA5Sit_F4 hNS h13315 h1356two hG1 hna).not_V_le
  obtain ⟨K, hK, hKb⟩ := (S.toA5Sit_F4 hNS h13315 h1356two hG1 hna).exists_component
    VolI.stmtF956i (S.toA5SitY_L0_F4 hNS h13315 h1356two hG1 hna hhat)
    (S.lemma13_5_19_two_l0 hhat hVG1) hv hvQ
  set P := (S.toA5Sit_F4 hNS h13315 h1356two hG1 hna).toHyp1321 VolI.stmtF956i hv hvQ K hK hKb
    with hP
  set QL := (S.toA5Sit_F4 hNS h13315 h1356two hG1 hna).toHypL1 VolI.stmtF956i h38 hv hvQ K hK hKb
    (fun _ hl => S.cube_mem_pCoreOf_L1_hat hhat hl) with hQL
  obtain ⟨-, hLK, U1, U2, h1, h2, -, -, -, -, hB4, hcond, hinj, -, -, hrk, A, hA⟩ :=
    A5.lemma_13_5_21_main P
      ((S.toA5Sit_F4 hNS h13315 h1356two hG1 hna).toHypY VolI.stmtF956i h38 hv hvQ K hK hKb
        (S.toA5SitY_L0_F4 hNS h13315 h1356two hG1 hna hhat) (S.lemma13_5_19_two_l0 hhat hVG1))
      QL hF hR hA7 hL3 hO
  refine hC _ (A5.Hyp1321.chiefSec_sq P U1 U2) _ _ A hB4 hA _ hcond hrk ?_

  set ψ := A5.secAct P.ρ _ h1 h2 with hψ
  set f : ↥P.K →* MulAut (A5.ChiefSec U1 U2) :=
    ψ.comp (Subgroup.inclusion le_sup_left : ↥P.K →* ↥(P.K ⊔ Subgroup.zpowers P.b)) with hf
  have hle : (QL.L.subgroupOf P.K).map f ≤
      (P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ ⊓
        Subgroup.centralizer {ψ ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩} := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨Subgroup.inclusion le_sup_left k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hkb : (Subgroup.inclusion le_sup_left k : ↥(P.K ⊔ Subgroup.zpowers P.b)) *
        ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩ =
        ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩ *
          Subgroup.inclusion le_sup_left k :=
      Subtype.ext (QL.comm _ (Subgroup.mem_subgroupOf.mp hk))
    rw [hf, MonoidHom.comp_apply, ← map_mul, hkb, map_mul]
  have hcard : Nat.card ((QL.L.subgroupOf P.K).map f) = Nat.card QL.L := by
    rw [Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv
  have h9 : 9 ∣ Nat.card QL.L :=
    S.nine_dvd_card_imQ_L1_hat hhat (H := S.G1) (le_sup_left.trans hG1.1.1)
  rw [← hcard] at h9
  exact h9.trans (Subgroup.card_dvd_of_le hle)

end CFSG.Quasithin.H13.A6
