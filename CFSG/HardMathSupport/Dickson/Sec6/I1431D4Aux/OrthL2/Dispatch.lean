module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LocalAnalysis.GLTheoremB

section Model


variable (K : Type) [Field K] [Finite K]

theorem exists_classicalModel_adjointD4 :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = ringChar K ^ f ∧
      StatedClassicalModel (adjointGroup Tag.D4 K) .POmegaPlus 4 (ringChar K) f := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  obtain ⟨e⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  have hcard : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  exact ⟨n, n.pos, hcard, ⟨hp, n.pos, le_rfl⟩, K, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩

variable {K}

theorem isComponentOf_threeComponent_D4 (hK3 : ringChar K ≠ 3) {g : adjointGroup Tag.D4 K}
    (hg : orderOf g = 3) {J : Subgroup (adjointGroup Tag.D4 K)}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({g} : Set (adjointGroup Tag.D4 K))) J) :
    CFSG.Open.IsComponentOf J (Subgroup.centralizer ({g} : Set (adjointGroup Tag.D4 K))) := by
  obtain ⟨f, -, -, hmodel⟩ := exists_classicalModel_adjointD4 K
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hlayer : PerfectInLayer (MulAut.conj g) :=
    perfectInLayer_conj_omega (Or.inr (Or.inl rfl)) hmodel Nat.prime_three (by norm_num)
      (Ne.symm hK3) g hg3
  have hfix : fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set _) :=
    CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.fixSubgroup_conj_eq_centralizer' g
  rw [← hfix] at hJ ⊢
  exact (glaPComponent_isComponent_of_le_layer hJ
    (hlayer J hJ.1 (glaPComponent_perfect hJ))).1

end Model

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
