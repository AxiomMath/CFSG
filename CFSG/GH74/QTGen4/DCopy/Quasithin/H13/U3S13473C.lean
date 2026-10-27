module

public import CFSG.Quasithin.H13.U3S13473C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_Y_cent_F4 (h139 : A6.Stmt13_3_9_F4) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {Y Y₂ : Subgroup G}
    (hY : InH T Y) (hYM : ¬ Y ≤ normalizer (L : Set G)) (hY₂Y : Y₂ ≤ Y)
    (hY₂ : oTwoRes Y₂ = Y₂)
    (hnc : ¬ ∀ y ∈ Y₂, ∀ l ∈ L₁Of L (fsuV1 T V),
      y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V))) :
    IsTwoReducedIn Y (VZ T Y) ∧ Y ⊓ centralizer (VZ T Y : Set G) = pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred : IsTwoReducedIn Y (VZ T Y) :=
    C1GN.isTwoReducedIn_VZ (s134_charTwo_of_inH S hY) (A5.isSylowTwoOf_of_le S.h13.sylow hY.1)
  refine ⟨hred, le_antisymm ?_ (le_inf (pCoreOf_le 2 Y) (pCoreOf_le_centralizer_of_reduced' hred))⟩
  have hCN : Y ≤ normalizer ((Y ⊓ centralizer (VZ T Y : Set G) : Subgroup G) : Set G) :=
    fun g hg =>
      mem_normalizer_inf_of (le_normalizer hg) (mem_normalizer_centralizer_of_mem (hred.2.1 hg))
  have hYN : Y ≤ normalizer (oTwoRes (Y ⊓ centralizer (VZ T Y : Set G)) : Set G) :=
    hCN.trans (normalizer_le_normalizer_oTwoRes _)

  have hvV1 := s134_e45_mem_V1 S
  have hZY : quasithinOmegaOneCenter T ≤ VZ T Y := le_conjClosure _ _
  have hZV : V ⊓ centralizer (L : Set G) ≤ VZ T Y := by
    rw [S.ZV_eq_zpowers, zpowers_le]
    refine hZY (subset_closure
      ⟨⟨S.V_le_T S.zV_mem_V, mem_centralizer_iff.2 fun t ht => ?_⟩, S.zV_sq⟩)
    have h1 := S.conj_zV ⟨t, S.frame.T_le ht⟩
    calc t * S.zV = t * S.zV * t⁻¹ * t := by group
      _ = S.zV * t := by rw [h1]
  have hCle : oTwoRes (Y ⊓ centralizer (VZ T Y : Set G)) ≤ normalizer (L : Set G) ⊓
      centralizer ({((S.frame.ψ.symm ⟨e45, e45_mem⟩ : ↥V) : G)} : Set G) := by
    refine (oTwoRes_le _).trans (inf_le_right.trans (le_inf ?_ ?_))
    · exact (centralizer_le (SetLike.coe_subset_coe.2 hZV)).trans S.centralizer_ZV_le
    · exact centralizer_le (Set.singleton_subset_iff.2 (hZY (mem_inf.1 hvV1).2))
  rcases h139 G T L V Y _ _ S.h13 S.irr (s134_isA6On S) hY hYM (S14.oTwoRes_idem _)
      ((oTwoRes_le _).trans inf_le_left) hYN hvV1 (s134_e45_not_mem_centralizer S) hCle with
    hbot | ⟨-, hL1, -⟩
  · exact le_pCoreOf_of_le_normalizer 2 inf_le_left hCN (isPGroup_of_oTwoRes_eq_bot hbot)
  · exfalso
    obtain ⟨h3, hO, -⟩ := s134_L1T_a6 S he
    have hYL : Y₂ ≤ normalizer (L₁Of L (fsuV1 T V) : Set G) := by
      have := hY₂Y.trans hYN
      rwa [hL1 he] at this
    exact hnc (comm_mem_of_oTwoRes (by rw [← hO]; exact h3) hY₂ hYL)

end CFSG.Quasithin.H13.U3
