module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs25
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Fin
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2

theorem S2.isSylow_of_le_of_le {G : Type} [Group G] [Finite G] {P C A : Subgroup G}
    (hP : IsSylowTwoOf P A) (hPC : P ≤ C) (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.2.1, fun hd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  have h2 : 2 ∣ P.relIndex A := by rw [← h1]; exact Dvd.dvd.mul_right hd _
  exact h2

theorem lemma2_4_25_D (hK : Kc3Inspection) : Lemma2_4_25_D := by
  intro G _ _ T M H S L cfg x K hKC
  have hSIN : s2SI S L ≤ Subgroup.normalizer (s2Phi S L : Set G) :=
    hKC.SI_phi.le.trans inf_le_right
  have hSIp : IsPGroup 2 ↥(s2SI S L) :=
    cfg.cs.setting.isPGroup.to_le (inf_le_left.trans cfg.cs.le_T)
  obtain ⟨T_I, hSIT, hTI⟩ := exists_isSylowTwoOf_of_le hSIN hSIp
  obtain ⟨hTN, hloc⟩ := hKC.local_all T_I hTI hSIT
  have hKN : K ≤ Subgroup.normalizer (s2Phi S L : Set G) := hKC.K_comp.1
  have hTK : IsSylowTwoOf T_I (K ⊔ T_I) :=
    S2.isSylow_of_le_of_le hTI le_sup_right (sup_le hKN hTI.1)
  obtain ⟨X, S₁, hXc, hLX, hXK, hS₁, hS₁S, hnot⟩ := hK G K L (s2SI S L) T_I
    (BenderBranch.isQuasisimple_of_isComponentIn hKC.K_comp) hKC.K_list hKC.K_center hKC.L_le
    cfg.cs.block.1.1 cfg.alt5 inf_le_right hSIp hTI.2.1 hSIT hTN hTK
  exact hnot (hloc X S₁ hXc hLX hXK hS₁ hS₁S)

end CFSG.QuasithinUnique.A5
