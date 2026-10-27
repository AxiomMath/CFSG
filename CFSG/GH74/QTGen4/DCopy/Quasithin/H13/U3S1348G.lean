module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S13227
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1344
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1348E
public import CFSG.Quasithin.H13.U3S1348A
public import CFSG.Quasithin.H13.U3S1348F

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s134_claim1348_F4 (hC137 : C137StatementFiveZ_F4)
    (h1332 : Stmt13_3_2_F4) (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V)
    {z : G} {H VH : Subgroup G} (hHz : InHz T L V z H) (hsolv : Group.IsSolvable ↥H)
    (hred : IsTwoReducedIn H VH)
    (h44 : (oTwoRes (H ⊓ centralizer (VH : Set G)) = ⊥ ∧
        H ⊓ centralizer (VH : Set G) = pCoreOf 2 H ∧
        pCoreOf 2 H ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧
        pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ r1Of T L V) ∨
      ∃ Lp : Subgroup G,
        (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) →
          Lp = L₁Of L (fsuV1 T V)) ∧
        (IsHatA6 L → Lp = l1plus T L V) ∧
        Lp = oTwoRes (H ⊓ centralizer (VH : Set G)) ∧ H ≤ normalizer (Lp : Set G) ∧
        (centralizerMod (pCoreOf 2 Lp) H Lp).relIndex H = 2 ∧
        IsSylowTwoOf (r1Of T L V) (centralizerMod (pCoreOf 2 Lp) H Lp)) :
    ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJ
  have hcR := s134_r1Of_inf_centralizer S hHz hred h44
  obtain ⟨hTsyl, hL1TH, -, hO2H, hHM⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hL1H : L₁Of L (fsuV1 T V) ≤ H := le_sup_left.trans hL1TH
  have hJR : thompsonJ (r1Of T L V) ≤ r1Of T L V := iSup₂_le fun _ hA => hA.1
  have hJO : thompsonJ (r1Of T L V) ≤ pCoreOf 2 H := hcR ▸ le_inf hJR hJ
  have hOR : pCoreOf 2 H ≤ r1Of T L V := hcR.symm.le.trans inf_le_left
  have hOT : pCoreOf 2 H ≤ T := hOR.trans (r1Of_le_T T L V)
  have hVHO : VH ≤ pCoreOf 2 H := (s134_VH_le_r1Of hred hcR).1
  rcases s134_lemma13_2_2_seven_F4 hC137 h1332 S with ⟨C, hCB, hC1, hCchar, hCN⟩ | hblk
  ·
    have hB : baum (r1Of T L V) = baum (pCoreOf 2 H) := by
      rw [← hcR]
      exact baum_eq_baum_centralizer hred.2.2.1 (hVHO.trans hOR) (le_inf hJR hJ)
    have hHC : H ≤ normalizer (C : Set G) := by
      refine (le_normalizer_pCoreOf 2 H).trans ((normalizer_le_normalizer_baum _).trans ?_)
      rw [← hB]
      exact normalizer_le_normalizer_of_characteristic hCB hCchar
    have hC2 : IsPGroup 2 ↥C :=
      S.h13.sylow.1.to_le (hCB.trans (inf_le_left.trans (r1Of_le_T T L V)))
    exact hHM (hHC.trans (s134_normalizer_le_M S hC1 hC2 hCN))
  ·
    have hL := hblk.1
    have he := hblk.2.1
    have hVO : V ≤ pCoreOf 2 H := (s134_lemma13_2_2_six S).2.2.trans hJO
    by_cases hN : H ≤ normalizer (L₁Of L (fsuV1 T V) : Set G)
    · obtain ⟨h, hh, hnot⟩ := s134_exists_conj_not_le S hL hTH hHM hVO hOT
      exact s134_false_of_normal_F4 h331 h1222 S hL he hN hL1H hVO hOR hh hnot
    · have hC : H ⊓ centralizer (VH : Set G) = pCoreOf 2 H := by
        rcases h44 with ⟨-, hC, -⟩ | ⟨Lp, hLp, -, -, hHLp, -⟩
        · exact hC
        · exact absurd (hLp he ▸ hHLp) hN
      have hVHQ : VH ≤ pCoreOf 2 (L ⊔ T) := by
        rw [← s134_cT S]
        refine le_inf (hVHO.trans hOT) fun u hu => mem_centralizer_iff.2 fun v hv => ?_
        exact (mem_centralizer_iff.1 (hJ ((s134_lemma13_2_2_six S).2.2 hv)) u hu).symm
      exact s134_false_of_not_normal S hL he hsolv hL1H hO2H hred.2.1 hVHQ hC

theorem claim1348_of_F4 (hC137 : C137StatementFiveZ_F4)
    (h1332 : Stmt13_3_2_F4) (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h44 : Stmt13_4_4_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (_ : A6.Setting134 G T L V) (z : G),
      z ∈ fsuV1 T V → z ∉ centralizer (L : Set G) →
      ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) →
      ∀ H VH : Subgroup G, InHz T L V z H → Group.IsSolvable ↥H → IsTwoReducedIn H VH →
        V ⊓ centralizer (L : Set G) ≤ VH →
        ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G) := by
  intro G _ _ T L V S z hz hzL _ H VH hHz hsolv hred hZ
  have hzV : S.zV ∈ quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ (VH ⊔ zpowers z) := by
    refine ⟨⟨mem_quasithinOmegaOneCenter_iff.2 ⟨S.V_le_T S.zV_mem_V, ?_, S.zV_sq⟩,
      (S.mem_ZV_iff.2 (Or.inr rfl)).2⟩, mem_sup_left (hZ (S.mem_ZV_iff.2 (Or.inr rfl)))⟩
    refine mem_centralizer_iff.2 fun t ht => ?_
    have h1 := S.conj_zV ⟨t, S.frame.T_le ht⟩
    calc t * S.zV = (t * S.zV * t⁻¹) * t := by group
      _ = S.zV * t := by rw [h1]
  have hX : quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ (VH ⊔ zpowers z) ≠ ⊥ :=
    fun h => S.zV_ne_one ((mem_bot).1 (h ▸ hzV))
  exact s134_claim1348_F4 hC137 h1332 h331 h1222 S hHz hsolv hred
    (h44 G T L V S z hz hzL H VH hHz hred hX).2.1

end CFSG.Quasithin.H13.U3
