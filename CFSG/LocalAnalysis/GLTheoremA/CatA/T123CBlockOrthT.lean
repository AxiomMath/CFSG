module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockAbs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinPlane
  CFSG.RankThree.PartOne.KCUnitaryPlane

section Generalities

private theorem card_quot_center_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (G ⧸ Subgroup.center G) = Nat.card (H ⧸ Subgroup.center H) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

private theorem subgroupOf_quasisimple {G : Type*} [Group G] {Ω P : Subgroup G} (hPΩ : P ≤ Ω)
    (hq : CFSG.IsQuasisimple ↥P) {p : ℕ} (hd : p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P)) :
    CFSG.Open.IsQuasisimple ↥(P.subgroupOf Ω) ∧
      p ∣ Nat.card (↥(P.subgroupOf Ω) ⧸ Subgroup.center ↥(P.subgroupOf Ω)) := by
  let e : ↥(P.subgroupOf Ω) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPΩ
  have hq' : CFSG.IsQuasisimple ↥(P.subgroupOf Ω) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  refine ⟨⟨hq'.1.commutator_eq_top, hq'.2.1⟩, ?_⟩
  rw [card_quot_center_of_mulEquiv e]
  exact hd

private theorem isComponentOf_subgroupOf {G : Type*} [Group G] {Ω P S : Subgroup G}
    (C : Subgroup ↥Ω) (hPS : P ≤ S) (hPN : ∀ g ∈ S, ∀ y ∈ P, g * y * g⁻¹ ∈ P)
    (hSC : S.subgroupOf Ω ≤ C) (hSN : ∀ g ∈ C, ∀ y ∈ S, (g : G) * y * (g : G)⁻¹ ∈ S)
    (hPq : CFSG.Open.IsQuasisimple ↥(P.subgroupOf Ω)) :
    CFSG.Open.IsComponentOf (P.subgroupOf Ω) C := by
  have hPS' : P.subgroupOf Ω ≤ S.subgroupOf Ω := Subgroup.subgroupOf_mono Ω hPS
  have hN1 : ((P.subgroupOf Ω).subgroupOf (S.subgroupOf Ω)).Normal :=
    (Subgroup.normal_subgroupOf_iff hPS').2 fun x g hx hg => hPN g.1 hg x.1 hx
  have hN2 : ((S.subgroupOf Ω).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff hSC).2 fun x g hx hg => hSN g hg x.1 hx
  exact ⟨hPS'.trans hSC, CFSG.Open.IsSubnormal.step hPS' hN1
    (CFSG.Open.IsSubnormal.step hSC hN2 (CFSG.Open.IsSubnormal.refl C)), hPq⟩

end Generalities

section Transfer

variable {n : ℕ} {K : Type} [Field K] {Q : QuadraticForm K (Fin n → K)}
  {A : Subgroup ↥(orthDerived Q)} [Fintype ↥(A.map (orthToSL Q))]
  [IsMulCommutative ↥(A.map (orthToSL Q))]

private theorem actEquiv_orthToSL {g : ↥(orthDerived Q)} (hg : g ∈ A) :
    actEquiv (⟨orthToSL Q g, Subgroup.mem_map_of_mem _ hg⟩ : ↥(A.map (orthToSL Q))) =
      (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  LinearEquiv.toLinearMap_injective (toLin'_orthToSL Q g)

private theorem mul_comm_of_commute_act {y : (Fin n → K) ≃ₗ[K] (Fin n → K)}
    (hy : ∀ e : ↥(A.map (orthToSL Q)),
      Commute y.toLinearMap (act (planeRep (A.map (orthToSL Q))) e))
    {g : ↥(orthDerived Q)} (hg : g ∈ A) :
    y * (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) = g * y := by
  have h1 := hy ⟨orthToSL Q g, Subgroup.mem_map_of_mem _ hg⟩
  rw [← actEquiv_toLinearMap, actEquiv_orthToSL hg] at h1
  exact LinearEquiv.toLinearMap_injective h1.eq

private theorem commute_act_of_mem_centralizer {g' : ↥(orthDerived Q)}
    (hg' : g' ∈ Subgroup.centralizer (A : Set ↥(orthDerived Q)))
    (e : ↥(A.map (orthToSL Q))) :
    Commute (g' : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap
      (act (planeRep (A.map (orthToSL Q))) e) := by
  obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp e.2
  have he : e = ⟨orthToSL Q g, Subgroup.mem_map_of_mem _ hg⟩ := Subtype.ext hge.symm
  rw [he, ← actEquiv_toLinearMap, actEquiv_orthToSL hg]
  exact (congrArg (fun z : ↥(orthDerived Q) => (z : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap)
    (Subgroup.mem_centralizer_iff.mp hg' g hg)).symm

end Transfer

theorem innerBlock_of_orthBlockConcl {n p : ℕ} {K : Type} [Field K]
    {Q : QuadraticForm K (Fin n → K)} {A : Subgroup ↥(orthDerived Q)} {a : ↥(orthDerived Q)}
    (haA : a ∈ A) [Fintype ↥(A.map (orthToSL Q))] [IsMulCommutative ↥(A.map (orthToSL Q))]
    (hc : OrthBlockConcl Q (A.map (orthToSL Q)) p ⟨orthToSL Q a, Subgroup.mem_map_of_mem _ haA⟩) :
    ∃ a' ∈ A, a' ∉ Subgroup.zpowers a ∧ ∃ P M : Subgroup ↥(orthDerived Q),
      CFSG.Open.IsComponentOf P (Subgroup.centralizer (A : Set ↥(orthDerived Q))) ∧
      CFSG.Open.IsComponentOf M (Subgroup.centralizer ({a'} : Set ↥(orthDerived Q))) ∧ P ≤ M ∧
      p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) ∧ p ∣ Nat.card (↥M ⧸ Subgroup.center ↥M) ∧
      a ∉ Subgroup.centralizer (M : Set ↥(orthDerived Q)) := by
  obtain ⟨a'E, ha'E, P, S, M, hPS, hPN, hSΩ, hScomm, hSnorm, hPq, hPdvd, hMΩ, hMC, hMnorm, hMq,
    hPM, hMdvd, hâM⟩ := hc
  obtain ⟨a', ha'A, ha'e⟩ := Subgroup.mem_map.mp a'E.2
  have ha'E_eq : a'E = ⟨orthToSL Q a', Subgroup.mem_map_of_mem _ ha'A⟩ := Subtype.ext ha'e.symm
  subst ha'E_eq
  rw [actEquiv_orthToSL ha'A] at hMC hMnorm
  rw [actEquiv_orthToSL haA] at hâM
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hPΩ : P ≤ orthDerived Q := hPS.trans hSΩ
  refine ⟨a', ha'A, ?_, P.subgroupOf (orthDerived Q), M.subgroupOf (orthDerived Q), ?_, ?_,
    Subgroup.subgroupOf_mono _ hPM, (subgroupOf_quasisimple hPΩ hPq hPdvd).2,
    (subgroupOf_quasisimple hMΩ hMq hMdvd).2, ?_⟩
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ha'E (Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩)
    change orthToSL Q a ^ k = orthToSL Q a'
    rw [← map_zpow, hk]
  · refine isComponentOf_subgroupOf _ hPS hPN (fun x hx => ?_) (fun g hg y hy => ?_)
      (subgroupOf_quasisimple hPΩ hPq hPdvd).1
    · exact Subgroup.mem_centralizer_iff.mpr fun g hg =>
        Subtype.ext (mul_comm_of_commute_act (hScomm x.1 hx) hg).symm
    · exact hSnorm g.1 (hΩO g.2) (fun e => commute_act_of_mem_centralizer hg e) y hy
  · refine isComponentOf_subgroupOf _ le_rfl (fun g hg y hy => M.mul_mem (M.mul_mem hg hy)
      (M.inv_mem hg)) (fun x hx => ?_) (fun g hg y hy => ?_)
      (subgroupOf_quasisimple hMΩ hMq hMdvd).1
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp (hMC (show x.1 ∈ M from hx))).2))
    · refine hMnorm g.1 (Subgroup.mem_inf.mpr ⟨hΩO g.2, ?_⟩) y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
  · intro hac
    refine hâM (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hac ⟨y, hMΩ hy⟩ hy)

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
