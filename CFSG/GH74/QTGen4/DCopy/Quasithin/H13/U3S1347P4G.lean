module

public import CFSG.Quasithin.H13.U3S1347P4G
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S132210B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347I
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347P4A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347P4F

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_not_II_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (h1345 : NQS134.Stmt13_4_5_F4) (hF : F6.TheoremF618Cat)
    (hBig : A5.FactF618Big) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hK₂L : oTwoRes H₂ = l2Of S)
    (hJ : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G)) (hns : ¬ Group.IsSolvable ↥(H₁ ⊔ H₂)) :
    ¬ (H13.IsA6Block L ∧ ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 (L ⊔ T)) A →
      IsMaxElemAbelian T A) := by
  rintro ⟨hB, hII⟩
  obtain ⟨hH₀, hH₀M, hZV1, -⟩ := s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  obtain ⟨K₀, hK₀, hN, -, hcases, hK₁, hK₂, hsup, hcentK⟩ :=
    s1347_K0_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S h hns
  have hKH := le_of_mem_cComp hK₀
  obtain ⟨c, hcL2, hcN, hcρ, hc3⟩ := s134_exists_c2_three S h hK₂L
  have hcK : c ∈ K₀ := by rw [← hK₂L] at hcL2; exact hK₂ hcL2

  have hcC : c ∉ centralizer (v0Of T H₁ H₂ : Set G) := by
    intro hcC
    set w : ↥V := S.frame.ψ.symm ⟨e45, e45_mem⟩ with hw
    have hwZ : (w : G) ∈ quasithinOmegaOneCenter T := by rw [hZV1]; exact s134_e45_mem_V1 S
    have hcw : c * (w : G) * c⁻¹ = w := by
      rw [← mem_centralizer_iff.1 hcC w (s1347_Z_le_V0 hwZ), mul_inv_cancel_right]
    have h1 := congrArg Subtype.val ((S.conj_eq_iff ⟨c, hcN⟩ w).1 hcw)
    rw [G6.coreAct_coe, hcρ, hw, MulEquiv.apply_symm_apply] at h1
    revert h1
    decide
  have hperf := perfect_of_mem_cComp hK₀
  rcases hcases with hLie | hA6
  · have h16 := s1347_L32_relIndex_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h hN
      (quotIso_of_lieModel hLie) hsup (hKH hcK) hc3 hcC
    exact s1347_four_II S he hB hII h hH₀ hH₀M hJ hKH hsup hperf
      (simple_of_cases (Or.inr (Or.inl hLie))).1 hK₂ hK₂L hcL2 hcN hcρ hc3 h16
  · have h16 := s1347_A6_relIndex_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1345 S h hns hK₀ hN hA6
      hK₁ hK₂ hsup hcentK hcK hc3 hcC
    exact s1347_four_II S he hB hII h hH₀ hH₀M hJ hKH hsup hperf
      (simple_of_cases (Or.inr (Or.inr hA6))).1 hK₂ hK₂L hcL2 hcN hcρ hc3 h16

theorem s1347_four_F4 (hC137 : C137StatementFiveZ_F4)
    (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h135 : A6.Stmt13_3_5_F4)
    (h1345 : NQS134.Stmt13_4_5_F4) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hK₂L : oTwoRes H₂ = l2Of S) :
    ¬ Concl1347iv T H₁ H₂ ∧ (Concl1347ii T H₁ H₂ → ⁅oTwoRes H₂, thompsonJi T 1⁆ = oTwoRes H₂) := by
  obtain ⟨hH₀, hH₀M, -⟩ := s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  have he := s1347_a6_of_K2_F4 h1332 S h hK₂L
  constructor
  · rintro ⟨K₀, -, hK₀, -, hJ0, hJ1⟩
    have hJ : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G) := by
      rw [thompsonJ_eq_thompsonJi_zero]
      exact hJ0
    have hns := s1347_not_solvable_of_cComp hK₀
    rcases s134_lemma13_2_2_ten_F4 hC137 S he with hI | hII | hIII
    · exact s1347_not_charNormal S h hH₀ hH₀M hJ hI
    · exact s1347_not_II_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S he h hK₂L hJ hns hII
    · exact hIII (s1347_J1_le_centralizer_V2 S he h hK₂L hJ1)
  · rintro ⟨K₀, -, hK₀, -, -, -, hJ, -⟩
    have hns := s1347_not_solvable_of_cComp hK₀
    rcases s134_lemma13_2_2_ten_F4 hC137 S he with hI | hII | hIII
    · exact absurd hI (s1347_not_charNormal S h hH₀ hH₀M hJ)
    · exact absurd hII
        (s1347_not_II_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S he h hK₂L hJ hns)
    · exact s1347_comm_J1 S h hK₂L hIII

end CFSG.Quasithin.H13.U3
