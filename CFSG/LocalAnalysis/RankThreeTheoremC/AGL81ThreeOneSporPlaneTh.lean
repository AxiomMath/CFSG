module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneSporPlaneOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneSporPlaneThData
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThFive
public import CFSG.Sporadic.Bridge.ThSurj
public import Certificates.Certificate31021
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRNoX
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive
  CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

namespace ThFivePlane


local notation "regs5" => slpRows (rowsOf seedA) (rowsOf seedB) 118 prog5

local notation "R5" => slpJ a b prog5

local notation "x5" => R5 94

local notation "y5" => R5 105

local notation "c5" => R5 94 * R5 105 * R5 94 ^ 4 * R5 105 ^ 4

local notation "C5" =>
  mulRows (mulRows (mulRows regs5[94]! regs5[105]!) (powRowsN regs5[94]! 4))
    (powRowsN regs5[105]! 4)

local notation "Q5" => Subgroup.closure ({x5, y5} : Set J)

local notation "A0" => Subgroup.closure ({c5, y5} : Set J)

theorem thPlane_parts (h : thPlaneOK () = true) :
    (∀ e ∈ thPlaneEig (), thPlaneEigOK regs5 (idRows ()) regs5[94]! regs5[105]! C5 e = true) ∧
      (∀ r ∈ thPlaneWordA (), ((thPlaneEig ()).map Prod.fst).contains r = true) ∧
      (∀ r ∈ thPlaneWordB (), ((thPlaneEig ()).map Prod.fst).contains r = true) ∧
      (∀ r ∈ thPlaneWordA (), r < (regs5).size) ∧ (∀ r ∈ thPlaneWordB (), r < (regs5).size) ∧
      eqRows (wordRowsL regs5 (thPlaneWordA ())) (rowsOf seedA) = true ∧
      eqRows (wordRowsL regs5 (thPlaneWordB ())) (rowsOf seedB) = true ∧
      ∀ i < 5, ∀ j < 5, i + j ≠ 0 →
        thPlaneConjOK regs5 regs5[94]! regs5[105]! C5 (thPlaneConj ())[5 * i + j]! i j = true := by
  unfold thPlaneOK thPlaneCore at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun i hi j hj hij => (h8 i hi j hj).resolve_left hij⟩

theorem thPlane_eig {e : ℕ × ℕ × ℕ × ℕ}
    (h : thPlaneEigOK regs5 (idRows ()) regs5[94]! regs5[105]! C5 e = true) :
    y5 ^ e.2.1 * c5 ^ e.2.2.1 ≠ 1 ∧ (y5 ^ e.2.1 * c5 ^ e.2.2.1) ^ 5 = 1 ∧
      R5 e.1 * (y5 ^ e.2.1 * c5 ^ e.2.2.1) = (y5 ^ e.2.1 * c5 ^ e.2.2.1) ^ e.2.2.2 * R5 e.1 := by
  unfold thPlaneEigOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlt, hne⟩, h5⟩, hcomm⟩ := h
  have hW : rowsMatrix (cubeProd regs5[94]! regs5[105]! C5 0 e.2.1 e.2.2.1) =
      matJ (y5 ^ e.2.1 * c5 ^ e.2.2.1) := by
    rw [rowsMatrix_cubeProd rowsMatrix_x5 rowsMatrix_y5 rowsMatrix_c5, pow_zero, one_mul]
  have hone : rowsMatrix (idRows ()) = matJ 1 := by rw [rowsMatrix_idRows, matJ_one]
  have hr := hR5 e.1 hlt
  refine ⟨ne_of_rowsDiffer hW hone hne,
    eq_of_rowsMatrix_eq (by rw [rowsMatrix_powRowsN, hW, ← matJ_pow]) hone h5,
    eq_of_rowsMatrix_eq (by rw [rowsMatrix_mulRows, hr, hW, ← matJ_mul])
      (by rw [rowsMatrix_mulRows, rowsMatrix_powRowsN, hW, hr, ← matJ_pow, ← matJ_mul]) hcomm⟩

theorem thPlane_word {w : List ℕ} (hw : ∀ r ∈ w, r < (regs5).size) {S : String} {s : ↥J}
    (hS : rowsMatrix (rowsOf S) = matJ s) (h : eqRows (wordRowsL regs5 w) (rowsOf S) = true) :
    (w.map R5).prod = s :=
  eq_of_rowsMatrix_eq (rowsMatrix_wordRowsL fun r hr => hR5 r (hw r hr)) hS h

theorem thPlane_conj {d : List ℕ × ℕ × ℕ} {i j : ℕ}
    (h : thPlaneConjOK regs5 regs5[94]! regs5[105]! C5 d i j = true) :
    ∃ M : ↥J, M * c5 = c5 * M ∧ M * y5 = ((x5 ^ i * y5 ^ j) ^ d.2.1 * c5 ^ d.2.2) * M := by
  unfold thPlaneConjOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hw, hC, hY⟩ := h
  have hM := rowsMatrix_wordRowsL (R := R5) fun r hr => hR5 r (hw r hr)
  refine ⟨(d.1.map R5).prod, eq_of_rowsMatrix_eq ?_ ?_ hC, eq_of_rowsMatrix_eq ?_ ?_ hY⟩
  · rw [rowsMatrix_mulRows, hM, rowsMatrix_c5, ← matJ_mul]
  · rw [rowsMatrix_mulRows, hM, rowsMatrix_c5, ← matJ_mul]
  · rw [rowsMatrix_mulRows, hM, rowsMatrix_y5, ← matJ_mul]
  · simp only [rowsMatrix_mulRows, rowsMatrix_powRowsN, rowsMatrix_x5, rowsMatrix_y5, hM,
      matJ_mul, matJ_pow]

theorem thPlane_closure (h : thPlaneOK () = true) :
    Subgroup.closure {g : ↥J | ∃ e ∈ thPlaneEig (), g = R5 e.1} = ⊤ := by
  obtain ⟨-, hA, hB, hA', hB', hwA, hwB, -⟩ := thPlane_parts h
  have hmem : ∀ w : List ℕ, (∀ r ∈ w, ((thPlaneEig ()).map Prod.fst).contains r = true) →
      (w.map R5).prod ∈ Subgroup.closure {g : ↥J | ∃ e ∈ thPlaneEig (), g = R5 e.1} := by
    intro w hw
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.contains_iff_mem.1 (hw r hr))
    exact Subgroup.subset_closure ⟨e, he, rfl⟩
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · have h1 := hmem _ hA
    rw [thPlane_word hA' rowsMatrix_seedA hwA] at h1
    exact h1
  · have h1 := hmem _ hB
    rw [thPlane_word hB' rowsMatrix_seedB hwB] at h1
    exact h1

theorem glbCore_A0 [Finite ↥J] (h : thPlaneOK () = true) : GLBCore 5 1 A0 = ⊤ := by
  obtain ⟨heig, -⟩ := thPlane_parts h
  refine glbCore_one_eq_top_of_gens Nat.prime_five (thPlane_closure h) ?_
  rintro g ⟨e, he, rfl⟩
  obtain ⟨hne, h5, hcomm⟩ := thPlane_eig (heig e he)
  refine ⟨y5 ^ e.2.1 * c5 ^ e.2.2.1, ?_, hne, h5, e.2.2.2, hcomm⟩
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem xy_facts :
    x5 ^ 5 = 1 ∧ y5 ^ 5 = 1 ∧ ⁅x5, y5⁆ = c5 ∧ ∃ u ∈ Q5, ∃ v ∈ Q5, u * v ≠ v * u := by
  obtain ⟨-, -, hc1, -, -, hexp, -, -, -⟩ := th5_cube
  have hxQ : x5 ∈ Q5 := Subgroup.subset_closure (by simp)
  have hyQ : y5 ∈ Q5 := Subgroup.subset_closure (by simp)
  have hx5 : x5 ^ 5 = 1 := hexp _ hxQ
  have hy5 : y5 ^ 5 = 1 := hexp _ hyQ
  have hc' : c5 = x5 * y5 * x5 ^ (5 - 1) * y5 ^ (5 - 1) := by
    refine matJ_injective ?_
    simp only [matJ_mul, matJ_pow]
  refine ⟨hx5, hy5, ?_, x5, hxQ, y5, hyQ, fun hxy => hc1 ?_⟩
  · rw [hc']
    exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair.commutatorElement_eq_of_pow
      (by norm_num) hx5 hy5
  · have e1 : x5 * y5 * x5 ^ 4 * y5 ^ 4 = y5 * x5 ^ 5 * y5 ^ 4 := by rw [hxy]; group
    rw [e1, hx5, mul_one, ← pow_succ', hy5]

theorem plane_facts [Finite ↥J] (B : Subgroup ↥J) (hBQ : B ≤ Q5) (hB : IsElemAbelian 5 B)
    (hc : Nat.card B = 5 ^ 2) :
    c5 ∈ B ∧ ∃ i < 5, ∃ j < 5, i + j ≠ 0 ∧ x5 ^ i * y5 ^ j ∈ B := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hQ3, -, hc1, hc5, hcQ, -, -, hcx, hcy⟩ := th5_cube
  obtain ⟨hx5, hy5, hxy, hnc⟩ := xy_facts
  have hcB : c5 ∈ B := CFSG.AGLEmbedding.CoreD2.mem_of_central Nat.prime_five hQ3 hnc hBQ hB hc
    hcQ fun q hq => th5_Q_comm_c q hq
  obtain ⟨t, htB, htc⟩ : ∃ t ∈ B, t ∉ Subgroup.zpowers c5 := by
    by_contra hcon
    have hle := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers c5 from
      fun t ht => Classical.byContradiction fun h' => hcon ⟨t, ht, h'⟩)
    rw [hc, Nat.card_zpowers, orderOf_eq_prime hc5 hc1] at hle
    norm_num at hle
  have hzx : Commute ⁅x5, y5⁆ x5 := by rw [hxy]; exact hcx
  have hzy : Commute ⁅x5, y5⁆ y5 := by rw [hxy]; exact hcy
  obtain ⟨i, j, k, hi, hj, -, hijk⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm (by norm_num) hx5 hy5 hzx hzy (hBQ htB)
  rw [hxy] at hijk
  refine ⟨hcB, i, hi, j, hj, fun h0 => htc ?_, ?_⟩
  · rw [hijk, show i = 0 by omega, show j = 0 by omega, pow_zero, pow_zero, one_mul, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c5) k
  · have e : x5 ^ i * y5 ^ j = t * (c5 ^ k)⁻¹ := by rw [hijk, mul_inv_cancel_right]
    rw [e]
    exact B.mul_mem htB (B.inv_mem (B.pow_mem hcB k))

theorem glbCore_plane [Finite ↥J] (h : thPlaneOK () = true) (B : Subgroup ↥J) (hBQ : B ≤ Q5)
    (hB : IsElemAbelian 5 B) (hc : Nat.card B = 5 ^ 2) : GLBCore 5 1 B = ⊤ := by
  obtain ⟨hcB, i, hi, j, hj, hij, hsB⟩ := plane_facts B hBQ hB hc
  obtain ⟨-, -, -, -, -, -, -, hconj⟩ := thPlane_parts h
  obtain ⟨M, hMc, hMy⟩ := thPlane_conj (hconj i hi j hj hij)
  have hle : Subgroup.map (MulAut.conj M).toMonoidHom A0 ≤ B := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hu with rfl | rfl
    · rw [hMc, mul_inv_cancel_right]
      exact hcB
    · rw [hMy, mul_inv_cancel_right]
      exact B.mul_mem (B.pow_mem hsB _) (B.pow_mem hcB _)
  rw [eq_top_iff]
  intro g _
  have hg : M⁻¹ * g * M ∈ GLBCore 5 1 A0 := by
    rw [glbCore_A0 h]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem (MulAut.conj M).toMonoidHom hg
  rw [← CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_equiv] at h2
  have h3 := CFSG.AGLEmbeddingD2.glbCore_mono 5 1 hle h2
  have e : (MulAut.conj M).toMonoidHom (M⁻¹ * g * M) = g := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e] at h3
  exact h3

end ThFivePlane

theorem glbCore_one_eq_top_Th
    (K : Type) [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .Th).Group)) (A : Subgroup K)
    (hA : IsElemAbelian 5 A) (hc : Nat.card A = 5 ^ 2) : GLBCore 5 1 A = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have : Finite ↥J := th_finite
  obtain ⟨hQ3, -⟩ := th5_cube
  have hfac : (Nat.card ↥J).factorization 5 = 3 := by
    rw [CFSG.Sporadic.Th.Max3.natCard_J,
      show (90745943887872000 : ℕ) = 5 ^ 3 * 725967551102976 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  exact @glbCore_one_eq_top_of_mulEquiv K _ _ 5 ↥J (Subgroup.toGroup J) _ 3 Nat.prime_five
    ((e₁.trans e₂.symm).trans thEquivJ) _ hQ3 hfac
    (fun B hBQ hB hBc => ThFivePlane.glbCore_plane Certificates.certificate31021 B hBQ hB hBc)
    A hA hc

theorem sporPlaneAt_Th :
    SporPlaneAt .Th 5 :=
  fun K _ _ hK A hA hc => glbCore_one_eq_top_Th K hK A hA hc

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
