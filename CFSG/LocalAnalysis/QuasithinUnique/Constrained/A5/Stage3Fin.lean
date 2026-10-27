module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3FinInputs
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43


public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

theorem thRaw_rone : thRaw rone = 0 :=
  Certificates.certificate17027.1

theorem thRaw_zraw : thRaw zraw = 0 :=
  Certificates.certificate17027.2.1

theorem thRaw_mul : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset, ∀ v' ∈ Evens, v' 4 = 0 → ∀ σ' ∈ Vset,
    thRaw (rmul (v, σ) (v', σ')) = thRaw (v, σ) + thRaw (v', σ') :=
  Certificates.certificate17027.2.2.1

theorem thRaw_ker : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset, thRaw (v, σ) = 0 →
    (v, σ) = rone ∨ (v, σ) = zraw :=
  Certificates.certificate17027.2.2.2.1

theorem thRaw_pre : ∀ v : V4, isE8 (preraw v).1 ∧ (preraw v).2 ∈ Vset ∧ thRaw (preraw v) = v :=
  Certificates.certificate17027.2.2.2.2.1

theorem thRaw_q : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    (quadHyp (thRaw (v, σ)) = 0 ∧ rmul (v, σ) (v, σ) = rone) ∨
    (quadHyp (thRaw (v, σ)) = 1 ∧ rmul (v, σ) (v, σ) = zraw) :=
  Certificates.certificate17027.2.2.2.2.2.1

theorem thRaw_W0 : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    (thRaw (v, σ) 0 = 0 ∧ thRaw (v, σ) 2 = 0) → σ = 1 :=
  Certificates.certificate17027.2.2.2.2.2.2.1

theorem Mt1_act : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    Mt1.mulVec (thRaw (v, σ)) = thRaw (rmul (rmul gt1 (v, σ)) gt1) :=
  Certificates.certificate17027.2.2.2.2.2.2.2.1

theorem Ms01_act : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    Ms01.mulVec (thRaw (v, σ)) = thRaw (rmul (rmul gs01 (v, σ)) gs01) :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.1

theorem Mk_act : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    Mk.mulVec (thRaw (v, σ)) = thRaw (rmul (rmul gk (v, σ)) gkinv) :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.1

theorem W0_sing : ∀ v : V4, inW0 v → v ≠ 0 → inSing v :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.1

theorem Mk_trans_W0 : ∀ v : V4, inW0 v → v ≠ 0 → ∀ v' : V4, inW0 v' → v' ≠ 0 →
    v' = v ∨ v' = Mk.mulVec v ∨ v' = Mk.mulVec (Mk.mulVec v) :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.1

theorem sing6_conn : ∀ a ∈ sing6, ∀ b ∈ sing6, ∃ w ∈ wordsUpTo 3, wact w a = b :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem t1_step : ∀ v : V4, ¬ inW0 v → inW0 (Mt1.mulVec v + v) ∧ Mt1.mulVec v + v ≠ 0 :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem S4_distinct : (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ Mt1 ∧
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ Ms01 ∧
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ Mt1 * Ms01 ∧ Mt1 ≠ Ms01 ∧ Mt1 ≠ Mt1 * Ms01 ∧
    Ms01 ≠ Mt1 * Ms01 :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem S4_inj : ∀ i j : Fin 4,
    (![1, Mt1, Ms01, Mt1 * Ms01] : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 2)) i =
      (![1, Mt1, Ms01, Mt1 * Ms01] : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 2)) j → i = j :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem thRaw_one_W0 : ∀ v : Fin 5 → ZMod 2, thRaw (v, 1) 0 = 0 ∧ thRaw (v, 1) 2 = 0 :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem swap_moves_e02 : pact (Equiv.swap 0 1) ![1, 0, 1, 0, 0] ≠ ![1, 0, 1, 0, 0] :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e02_even : isEven ![1, 0, 1, 0, 0] :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e02_four : (![1, 0, 1, 0, 0] : Fin 5 → ZMod 2) 4 = 0 :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem c3_inv : c3⁻¹ = c3 * c3 :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem nine_sing : (Finset.univ.filter fun v : V4 => inSing v).card = 9 :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem thRaw_mul' {r r' : RP} (h : inPraw r) (h' : inPraw r') :
    thRaw (rmul r r') = thRaw r + thRaw r' :=
  thRaw_mul r.1 (mem_Evens.mpr h.1.1) h.1.2 r.2 h.2 r'.1 (mem_Evens.mpr h'.1.1) h'.1.2 r'.2 h'.2

theorem thRaw_ker'
    {r : RP} (h : inPraw r) (h0 : thRaw r = 0) : r = rone ∨ r = zraw :=
  thRaw_ker r.1 (mem_Evens.mpr h.1.1) h.1.2 r.2 h.2 h0

theorem thRaw_q' {r : RP} (h : inPraw r) :
    (quadHyp (thRaw r) = 0 ∧ rmul r r = rone) ∨ (quadHyp (thRaw r) = 1 ∧ rmul r r = zraw) :=
  thRaw_q r.1 (mem_Evens.mpr h.1.1) h.1.2 r.2 h.2

theorem thRaw_W0'
    {r : RP} (h : inPraw r) (h0 : thRaw r 0 = 0 ∧ thRaw r 2 = 0) : r.2 = 1 :=
  thRaw_W0 r.1 (mem_Evens.mpr h.1.1) h.1.2 r.2 h.2 h0

theorem Mt1_act' {r : RP} (h : inPraw r) :
    Mt1.mulVec (thRaw r) = thRaw (rmul (rmul gt1 r) gt1) :=
  Mt1_act r.1 (mem_Evens.mpr h.1.1) h.1.2 r.2 h.2

theorem Ms01_act' {r : RP} (h : inPraw r) :
    Ms01.mulVec (thRaw r) = thRaw (rmul (rmul gs01 r) gs01) :=
  Ms01_act r.1 (mem_Evens.mpr h.1.1) h.1.2 r.2 h.2

theorem Mk_act' {r : RP} (h : inPraw r) :
    Mk.mulVec (thRaw r) = thRaw (rmul (rmul gk r) gkinv) :=
  Mk_act r.1 (mem_Evens.mpr h.1.1) h.1.2 r.2 h.2

theorem thRaw_pre'
    (v : V4) : inPraw (preraw v) ∧ thRaw (preraw v) = v :=
  ⟨⟨(thRaw_pre v).1, (thRaw_pre v).2.1⟩, (thRaw_pre v).2.2⟩

theorem sing_gen : ∀ v : V4, v = 0 ∨ inSing v ∨ ∃ a b : V4, inSing a ∧ inSing b ∧ a + b = v :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_O4Cols : Fintype.card O4Cols = 72 :=
  Certificates.certificate17027.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem quadHyp_single_0_check : quadHyp (Pi.single 0 1 : V4) = 0 :=
  Certificates.certificate5952.1

theorem quadHyp_single_1_check : quadHyp (Pi.single 1 1 : V4) = 0 :=
  Certificates.certificate5952.2.1

theorem quadHyp_single_0_1_check : quadHyp ((Pi.single 0 1 : V4) + Pi.single 1 1) = 1 :=
  Certificates.certificate5952.2.2.1

theorem quadHyp_single_2_check : quadHyp (Pi.single 2 1 : V4) = 0 :=
  Certificates.certificate5952.2.2.2.1

theorem quadHyp_single_0_2_check : quadHyp ((Pi.single 0 1 : V4) + Pi.single 2 1) = 0 :=
  Certificates.certificate5952.2.2.2.2.1

theorem quadHyp_single_1_2_check : quadHyp ((Pi.single 1 1 : V4) + Pi.single 2 1) = 0 :=
  Certificates.certificate5952.2.2.2.2.2.1

theorem quadHyp_single_3_check : quadHyp (Pi.single 3 1 : V4) = 0 :=
  Certificates.certificate5952.2.2.2.2.2.2.1

theorem quadHyp_single_0_3_check : quadHyp ((Pi.single 0 1 : V4) + Pi.single 3 1) = 0 :=
  Certificates.certificate5952.2.2.2.2.2.2.2.1

theorem quadHyp_single_1_3_check : quadHyp ((Pi.single 1 1 : V4) + Pi.single 3 1) = 0 :=
  Certificates.certificate5952.2.2.2.2.2.2.2.2.1

theorem quadHyp_single_2_3_check : quadHyp ((Pi.single 2 1 : V4) + Pi.single 3 1) = 1 :=
  Certificates.certificate5952.2.2.2.2.2.2.2.2.2

theorem card_O4PlusTwo_le :
    Nat.card O4PlusTwo ≤ 72 := by
  have hq : ∀ g : O4PlusTwo, ∀ v : V4,
      quadHyp ((g.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = quadHyp v := fun g => g.2
  let col : O4PlusTwo → Fin 4 → V4 := fun g i =>
    (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single i 1)
  have hsum : ∀ g i j, quadHyp (col g i + col g j) = quadHyp ((Pi.single i 1 : V4) + Pi.single j 1) := by
    intro g i j
    have : col g i + col g j =
        (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec ((Pi.single i 1 : V4) + Pi.single j 1) := by
      simp only [col, Matrix.mulVec_add]
    rw [this]
    exact hq g _
  have hone : ∀ g i, quadHyp (col g i) = quadHyp (Pi.single i 1 : V4) := fun g i => hq g _
  let f : O4PlusTwo → O4Cols := fun g =>
    ⟨⟨col g 0, (hone g 0).trans quadHyp_single_0_check⟩,
      ⟨⟨col g 1, (hone g 1).trans quadHyp_single_1_check, (hsum g 0 1).trans quadHyp_single_0_1_check⟩,
      ⟨⟨col g 2, (hone g 2).trans quadHyp_single_2_check, (hsum g 0 2).trans quadHyp_single_0_2_check,
        (hsum g 1 2).trans quadHyp_single_1_2_check⟩,
      ⟨col g 3, (hone g 3).trans quadHyp_single_3_check, (hsum g 0 3).trans quadHyp_single_0_3_check,
        (hsum g 1 3).trans quadHyp_single_1_3_check, (hsum g 2 3).trans quadHyp_single_2_3_check⟩⟩⟩⟩
  have hf : Function.Injective f := by
    intro g g' h
    have h0 : col g 0 = col g' 0 := congrArg (fun z => z.1.1) h
    have h1 : col g 1 = col g' 1 := congrArg (fun z => z.2.1.1) h
    have h2 : col g 2 = col g' 2 := congrArg (fun z => z.2.2.1.1) h
    have h3 : col g 3 = col g' 3 := congrArg (fun z => z.2.2.2.1) h
    have hc : ∀ i, col g i = col g' i := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    apply Subtype.ext
    apply Units.ext
    ext a b
    have := congrFun (hc b) a
    simpa [col, Matrix.mulVec_single_one] using this
  calc Nat.card O4PlusTwo ≤ Nat.card O4Cols := Nat.card_le_card_of_injective f hf
    _ = 72 := by rw [Nat.card_eq_fintype_card, card_O4Cols]

end CFSG.QuasithinUnique.A5
