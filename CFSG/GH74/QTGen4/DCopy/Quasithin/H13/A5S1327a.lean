module

public import CFSG.Quasithin.H13.A5S1327a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1328
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Assembly.LowTwoRank

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem isSolvable_of_hStar_ofNoN_F4
    (h331 : Stmt3_3_1_F4) (h523 : Stmt5_2_3_F4) (h1222 : Stmt12_2_2_F4) (hE22 : E2.E22StatementNoN)
    (hRes : Res1328a_F4) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    Group.IsSolvable ↥H := by
  set M := Subgroup.normalizer (L : Set G) with hM
  obtain ⟨hMP, -⟩ := S.hyp501.minParabolic_of_isHStar_F4 h331 hH
  by_contra hns
  have hSQ : SQTKGroup ↥H := by
    obtain ⟨hk, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    exact ⟨hq, hk⟩
  obtain ⟨⟨K, hKc, hHK, -, -⟩, -⟩ := hE22 G H T (H ⊓ M) hMP hSQ hns
  have hTZ := T_le_centralizer_omegaOneCenter T

  have hZK : ⁅quasithinOmegaOneCenter T, K⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    rw [hHK]
    refine sup_le ?_ hTZ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)

  have hTH : T ≤ H := hH.1.1
  have hKl : K ∈ lFamily T := cComp_subset_lFamily hTH hKc
  have hKloc : quasithinIsLocal T K :=
    ⟨S.isPGroup_T, hKl, (isSylowTwoOf_of_le S.h13.sylow le_sup_right).2.2,
      by rw [← hHK]; exact hH.1.2⟩
  have hKf : quasithinIsFaithfulLocal T K :=
    Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hKloc hZK
  have hA5 := (quasithinO2QuotientIso_iff K _).1 (S.h13.a5 S.a5 K hKf)

  have hTK : T ≤ Subgroup.normalizer (K : Set G) := S.le_normalizer_of_cComp_F4 h1222 hH hKc hHK hZK
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hn : 1 < E1.nParam H :=
    E1.LiftS5.one_lt_nParam_of_rootFourLiftQuot hHN (le_of_mem_cComp hKc) hA5
      (isSylowTwoOf_of_le S.h13.sylow hTH) (hRes G T L V S H K hH hHZ hKc hHK hTK hA5)

  have hV := S.isCh5Module
  rcases h523 G T M L H V 2 S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow S.uniqueM.1.1
      S.T_le_NL S.maximal S.h13.faithful Subgroup.le_normalizer le_rfl le_rfl S.lieModel_L hH
      hn hV.1 hV.2.1 hV.2.2 with ⟨-, -, KZ, hKZ, hHKZ, -⟩ | hM23 | hLie
  · apply hHZ
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_le S.h13.sylow hTH)]
    exact sup_le (hHKZ.trans (le_of_mem_cComp hKZ)) hTZ
  · exact S.h13.not_excluded (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM23)))))
  · apply S.h13.not_excluded
    rcases hLie with ⟨t, n, f, hf, -, hadm, hlie⟩ | hlie
    · exact Or.inl ⟨t, n, f, hf, hadm, hlie⟩
    · refine Or.inl ⟨.PSU, 5, 2, le_rfl, ?_, hlie⟩
      refine ⟨Nat.prime_two, by norm_num, ?_⟩
      exact ⟨by norm_num, by decide⟩

end Setting

@[expose] def Rest1327_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (_ : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H → False

theorem stmt13_2_7_ofNoN_F4
    (h331 : Stmt3_3_1_F4) (h523 : Stmt5_2_3_F4) (h1222 : Stmt12_2_2_F4) (hE22 : E2.E22StatementNoN)
    (hRes : Res1328a_F4) (hrest : Rest1327_F4) : Stmt13_2_7_F4 := by
  intro G _ _ T L V S H hH
  by_contra hHZ
  exact hrest G T L V S H hH hHZ (S.isSolvable_of_hStar_ofNoN_F4 h331 h523 h1222 hE22 hRes hH hHZ)

end CFSG.Quasithin.H13.A5
