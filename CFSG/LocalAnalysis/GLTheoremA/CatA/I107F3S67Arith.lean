module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3S
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Blueprint.Multiplier CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (torsBound tors tors_of_not_dvd)

@[expose] def small67 (lab : GLALabel) : Prop :=
  lab = ⟨.A, 1, 2⟩ ∨ lab = ⟨.twD, 2, 1⟩ ∨ lab = ⟨.A, 2, 1⟩ ∨ lab = ⟨.A, 3, 1⟩ ∨
    lab = ⟨.D, 3, 1⟩ ∨ lab = ⟨.A, 2, 2⟩ ∨ lab = ⟨.G2, 0, 2⟩ ∨ lab = ⟨.twB2, 0, 3⟩ ∨
    lab = ⟨.B2der, 0, 1⟩

theorem not_two_dvd_genericOrders {t : StatedLieTag} {N f : ℕ} (hf : 1 ≤ f)
    (ht : t ≠ .POmegaOdd) (hN : t = .POmegaMinus → 1 ≤ N) :
    ¬ 2 ∣ (genericOrders t N 2 f).1 ∧ ¬ 2 ∣ (genericOrders t N 2 f).2 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = 2 * k := ⟨2 ^ (f - 1), by rw [← pow_succ']; congr 1; omega⟩
  have hk1 : 1 ≤ k := by
    have : 0 < 2 ^ f := by positivity
    omega
  have hm : ¬ 2 ∣ 2 ^ f - 1 := by omega
  have hp : ¬ 2 ∣ 2 ^ f + 1 := by omega
  have hq : Even (2 ^ f) := ⟨k, by omega⟩
  cases t <;> simp only [genericOrders]
  case POmegaMinus =>
    refine ⟨fun h => ?_, by norm_num⟩
    have hN1 := hN rfl
    obtain ⟨j, hj⟩ : ∃ j, (2 ^ f) ^ N = 2 * j := ⟨k * (2 ^ f) ^ (N - 1), by
      rw [← mul_assoc, ← hk, ← pow_succ']
      congr 1
      omega⟩
    have := h.trans (Nat.gcd_dvd_right _ _)
    omega
  all_goals first
    | exact absurd rfl ht
    | exact ⟨fun h => hm (h.trans (Nat.gcd_dvd_right _ _)), by norm_num⟩
    | exact ⟨fun h => hp (h.trans (Nat.gcd_dvd_right _ _)), by norm_num⟩
    | (simp only [hq, if_true]; norm_num)
    | norm_num

theorem exceptionalOrders_two_cases {t : StatedLieTag} {N p f : ℕ}
    (h : 2 ∣ (exceptionalOrders t N p f).1 ∨ 2 ∣ (exceptionalOrders t N p f).2) :
    p = 2 ∧ ((t = .PSL ∧ N = 2 ∧ f = 2) ∨ (t = .PSL ∧ N = 3 ∧ f = 1) ∨
      (t = .PSL ∧ N = 4 ∧ f = 1) ∨ (t = .PSL ∧ N = 3 ∧ f = 2) ∨ (t = .PSU ∧ N = 4 ∧ f = 1) ∨
      (t = .PSU ∧ N = 6 ∧ f = 1) ∨ (t = .PSp ∧ N = 3 ∧ f = 1) ∨
      (t = .POmegaPlus ∧ N = 4 ∧ f = 1) ∨ (t = .G2 ∧ N = 0 ∧ f = 2) ∨ (t = .F4 ∧ N = 0 ∧ f = 1) ∨
      (t = .twistedB2 ∧ N = 0 ∧ f = 3) ∨ (t = .twistedE6 ∧ N = 0 ∧ f = 1)) := by
  revert h
  unfold exceptionalOrders
  split
  all_goals intro h
  all_goals first
    | (exfalso; omega)
    | simp

theorem torsBound_two_mark_cases {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (h2 : 2 ≤ torsBound 2 (markTag lab) (markRank lab) (markChar lab) (markDeg lab)) :
    exempt107 lab ∨ cover107 lab ∨ small67 lab := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hn hl
  by_cases hB : t = .B2der
  · subst hB
    obtain ⟨rfl, rfl⟩ := hl
    simp [small67]
  by_cases hG : t = .G2der
  · subst hG
    exfalso
    revert h2
    simp [torsBound, tors, markTag, markRank, markChar, markDeg, genericOrders, exceptionalOrders]
  have hc : markChar ⟨t, l, n⟩ = 2 := by cases t <;> simp_all [markChar]
  have hf : 1 ≤ markDeg ⟨t, l, n⟩ := by
    cases t <;> simp only [markDeg] <;> (try split_ifs) <;> omega
  have ht : markTag ⟨t, l, n⟩ ≠ .POmegaOdd := by
    cases t <;> simp only [markTag] <;> (try split_ifs) <;> simp
  have hN : markTag ⟨t, l, n⟩ = .POmegaMinus → 1 ≤ markRank ⟨t, l, n⟩ := by
    intro h
    cases t <;> (try simp only [markTag, markRank] at h hl ⊢) <;> (try split_ifs at h ⊢) <;>
      first | omega | simp at h
  rw [hc] at h2
  obtain ⟨g1, g2⟩ := not_two_dvd_genericOrders hf ht hN
  unfold torsBound at h2
  rw [tors_of_not_dvd g1, tors_of_not_dvd g2] at h2
  have he : 2 ∣ (exceptionalOrders (markTag ⟨t, l, n⟩) (markRank ⟨t, l, n⟩) 2
      (markDeg ⟨t, l, n⟩)).1 ∨ 2 ∣ (exceptionalOrders (markTag ⟨t, l, n⟩)
      (markRank ⟨t, l, n⟩) 2 (markDeg ⟨t, l, n⟩)).2 := by
    by_contra hcon
    rw [not_or] at hcon
    rw [tors_of_not_dvd hcon.1, tors_of_not_dvd hcon.2] at h2
    omega
  obtain ⟨-, key⟩ := exceptionalOrders_two_cases he
  cases t <;> simp only [markTag, markRank, markDeg] at key <;> (try split_ifs at key) <;>
    simp_all [exempt107, cover107, small67] <;> omega

theorem upA107_le_two_of_small67 {lab : GLALabel} (hs : small67 lab) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : upA107 lab p ≤ 2 := by
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hd1 : ¬ p ∣ 1 := fun h => by
    have := Nat.le_of_dvd one_pos h
    omega
  have hd2 : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd two_pos h
    omega
  have hm1 : rk2Ord p 1 ≠ 1 := fun h => hd1 (by simpa using rk2Ord_eq_one_iff.mp h)
  have hpos : ∀ n, 0 < rk2Ord p n := rk2Ord_pos hp hp2
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := hpos 2
    simp only [upA107, rk2Mult, hd2, if_false]
    generalize rk2Ord p 2 = m at *
    have : 2 / m ≤ 2 := Nat.div_le_self _ _
    split_ifs <;> simp_all <;> omega
  · have := hpos 1
    simp only [upA107, rk2Mult, hd1, if_false]
    generalize rk2Ord p 1 = m at *
    have h4 : m % 2 = 0 → 4 / m ≤ 2 := fun h => Nat.div_le_of_le_mul (by omega)
    have : 2 / m ≤ 2 := Nat.div_le_self _ _
    split_ifs <;> simp_all <;> omega
  · have := hpos 1
    simp only [upA107, rk2Mult, hd1, if_false]
    generalize rk2Ord p 1 = m at *
    have : 3 / m ≤ 2 := Nat.div_le_of_le_mul (by omega)
    split_ifs <;> simp_all <;> omega
  · have := hpos 1
    simp only [upA107, rk2Mult, hd1, if_false]
    generalize rk2Ord p 1 = m at *
    have : 4 / m ≤ 2 := Nat.div_le_of_le_mul (by omega)
    split_ifs <;> simp_all <;> omega
  · have := hpos 1
    simp only [upA107, rk2Mult, hd1, if_false]
    generalize rk2Ord p 1 = m at *
    rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
    · norm_num
    · have : 6 / m ≤ 2 := Nat.div_le_of_le_mul (by omega)
      have : 3 / m ≤ 1 := Nat.div_le_of_le_mul (by omega)
      split_ifs <;> simp_all <;> omega
  · have := hpos 2
    simp only [upA107, rk2Mult, hd2, if_false]
    generalize rk2Ord p 2 = m at *
    have : m ≠ 1 → 3 / m ≤ 2 := fun h => Nat.div_le_of_le_mul (by omega)
    split_ifs <;> simp_all <;> omega
  · simp only [upA107, rk2Mult, rk2Cnt, List.countP_cons, List.countP_nil, hd2, if_false]
    split_ifs <;> simp_all
  · simp only [upA107, rk2Mult, rk2Cnt]
    generalize rk2Ord p 3 = m at *
    have hx : ¬ (m ∣ 1 ∧ (m ∣ 2 * 2 ∧ ¬ m ∣ 2)) := fun ⟨h1, _, h3⟩ => h3 (h1.trans (one_dvd 2))
    simp only [List.countP_cons, List.countP_nil]
    split_ifs <;> simp_all <;> omega
  · have := hpos 1
    simp only [upA107, rk2Mult, hd1, if_false]
    generalize rk2Ord p 1 = m at *
    have h4 : m % 2 = 0 → 4 / m ≤ 2 := fun h => Nat.div_le_of_le_mul (by omega)
    have : 2 / m ≤ 2 := Nat.div_le_self _ _
    split_ifs <;> simp_all <;> omega

end CFSG.LocalAnalysis.GLTheoremA
