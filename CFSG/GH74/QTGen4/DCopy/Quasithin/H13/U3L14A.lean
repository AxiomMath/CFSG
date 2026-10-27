module

public import CFSG.Quasithin.H13.U3L14A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem K_A5_or_L32_F4
    (h1332 : Stmt13_3_2_F4) (hF : A318Facts) (h38 : A38ForSQTK) {K : Subgroup G}
    (hD : KData14 T L V V₂ Lp K) (hg : ¬ Lp ≤ K) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h5, -⟩ := h1332 G T L S.h13 K hD.faithful
  have hKH : K ≤ A6.g1 T V := le_of_mem_cComp hD.mem
  have hKn : (K.subgroupOf (A6.g1 T V)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKH).2 hD.G1_K
  have hQne : pCoreOf 2 (A6.g1 T V) ≠ ⊥ := fun h =>
    S.V1_ne (le_bot_iff.1 (h ▸ S.ash.V₁_le_pCoreOf))
  have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)).symm
      (A3.isQuasisimple_iff_open.2 hD.quasi)
  have htheta : ∀ (_ : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      alternatingGroup (Fin 6))), Lp ≤ K := fun hA6 =>
    (S.Lp_le_thetaOf S.Lp_G1).trans (A7.thetaOf_le_of_A6 hF h38 S.h13.qtke S.h13.simple
      S.h13.nonabelian hQne hD.mem hKn hKq hA6)
  rcases h5 with h | h | ⟨⟨e⟩⟩ | ⟨-, -, hA6⟩ | h
  · exact Or.inl h
  · exact Or.inr h
  ·
    exfalso
    have hZ : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : e z ∈ center (alternatingGroup (Fin 6)) := by
        rw [mem_center_iff] at hz ⊢
        intro g
        obtain ⟨g', rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, hz g']
      rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h1
      rw [mem_bot]
      exact e.injective (h1.trans (map_one e).symm)
    exact hg (htheta ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).trans e⟩)
  ·
    exact (hg (htheta hA6)).elim
  ·
    exfalso
    have hpsu : IsPSU 3 3 1 (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact hc
      all_goals exact absurd h0 (by norm_num)
    have hS := a318Exclusion_u33 (fun _ _ _ hX => two_le_pRank_of_isPSU_three_three1515e hX) hpsu
    have hSQ : SQTKGroup ↥(A6.g1 T V) :=
      sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hQne
    have heq := eq_oPrimeResidualOf_three_of_exclusion hF VolI.a36ForSQTK_holds h38 hSQ hD.mem
      hKq (MulEquiv.refl _) hS
    exact hg (heq ▸ S.Lp_le_oPrimeResidualOf S.Lp_G1)

end Set14

end CFSG.Quasithin.H13.U3
