module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
open CFSG.StandardType

section Arithmetic

theorem u64_exc_dvd_twelve (t : StatedLieTag) (n p f : ℕ) :
    (exceptionalOrders t n p f).1 ∣ 12 ∧ (exceptionalOrders t n p f).2 ∣ 12 := by
  unfold exceptionalOrders
  split <;> norm_num

theorem u64_gen_dvd_twelve {t : StatedLieTag} (ht1 : t ≠ .PSL) (ht2 : t ≠ .PSU) (n p f : ℕ) :
    (genericOrders t n p f).1 ∣ 12 ∧ (genericOrders t n p f).2 ∣ 12 := by
  unfold genericOrders
  dsimp only
  split
  all_goals first
    | exact absurd rfl ht1
    | exact absurd rfl ht2
    | skip
  all_goals (try split_ifs)
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | (norm_num; done)
    | (apply Nat.dvd_trans (Nat.gcd_dvd_left _ _); norm_num; done)

theorem u64_five_dvd_of_mul_dvd_144 {a x : ℕ} (h : 5 ∣ a * x) (hx : x ∣ 144) : 5 ∣ a := by
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).1 h with h1 | h1
  · exact h1
  · exact absurd (h1.trans hx) (by norm_num)

theorem u64_five_not_dvd_gcd {m x : ℕ} (hm : m ∣ 12) (hr : 5 ∣ Nat.gcd m x) : False :=
  absurd (hr.trans ((Nat.gcd_dvd_left m x).trans hm)) (by norm_num)

theorem u64_tag_of_five {lab : GLALabel} {x : ℕ}
    (hT : markTag lab = .PSL ∨ markTag lab = .PSU) (hr : 5 ∣ Nat.gcd (markRank lab) x) :
    lab.tag = .A ∨ lab.tag = .twA := by
  obtain ⟨t, r, k⟩ := lab
  cases t <;> simp [markTag, markRank] at hT hr ⊢
  all_goals (try split_ifs at hT hr)
  all_goals (try simp_all)
  all_goals exact u64_five_not_dvd_gcd (by norm_num) hr

theorem u64_two_pow_mod_five (n : ℕ) : 2 ^ n % 5 = 2 ^ (n % 4) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem u64_four_dvd_of_five_dvd_two_pow_sub_one {n : ℕ} (h : 5 ∣ 2 ^ n - 1) : 4 ∣ n := by
  have hm := u64_two_pow_mod_five n
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h0 : (2 ^ n - 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
  obtain h1 | h1 | h1 | h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  · exact Nat.dvd_of_mod_eq_zero h1
  all_goals (rw [h1] at hm; norm_num at hm; omega)

theorem u64_mod_four_of_five_dvd_two_pow_add_one {n : ℕ} (h : 5 ∣ 2 ^ n + 1) : n % 4 = 2 := by
  have hm := u64_two_pow_mod_five n
  have h0 : (2 ^ n + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
  obtain h1 | h1 | h1 | h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  all_goals first
    | exact h1
    | (rw [h1] at hm; norm_num at hm; omega)

end Arithmetic

section Marking


theorem u64_marking_model {Q : Type} [Group Q] [Finite Q] {lab : GLALabel}
    (h : GLAMarking Q fun lab' _ _ _ _ _ => lab' = lab) :
    CFSG.Open.IsQuasisimple Q ∧ MarkedModel lab (Q ⧸ Subgroup.center Q) := by
  obtain ⟨hcomm, lab', -, R, _, I, F, θ, hs, -, ⟨rfl, hm⟩⟩ :=
    Canonical.largeEvenMarking_exists (Canonical.largeEvenMarking_markedModel h)
  haveI := hs
  exact ⟨⟨hcomm, θ.isSimpleGroup⟩, MarkedModel.of_mulEquiv θ.symm hm⟩

end Marking

section Griess


theorem u64_five_dvd_center_model {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) t n p f)
    (h5 : 5 ∣ Nat.card (Subgroup.center Q)) :
    (t = .PSL ∧ 5 ∣ Nat.gcd n (p ^ f - 1)) ∨ (t = .PSU ∧ 5 ∣ Nat.gcd n (p ^ f + 1)) := by
  have hg : genericOrders t n p f = ((genericOrders t n p f).1, (genericOrders t n p f).2) := rfl
  have he : exceptionalOrders t n p f =
      ((exceptionalOrders t n p f).1, (exceptionalOrders t n p f).2) := rfl
  have h := (h5.trans (i61_card_center_dvd_native hQ hm hg he))
  obtain ⟨e1, e2⟩ := u64_exc_dvd_twelve t n p f
  have hE : (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2 ∣ 144 :=
    Nat.mul_dvd_mul e1 e2
  by_cases hL : t = .PSL
  · subst hL
    have hg' : genericOrders .PSL n p f = (Nat.gcd n (p ^ f - 1), 1) := rfl
    have h6 := u64_five_dvd_of_mul_dvd_144 h hE
    rw [hg'] at h6
    exact Or.inl ⟨rfl, by simpa using h6⟩
  by_cases hU : t = .PSU
  · subst hU
    have hg' : genericOrders .PSU n p f = (Nat.gcd n (p ^ f + 1), 1) := rfl
    have h6 := u64_five_dvd_of_mul_dvd_144 h hE
    rw [hg'] at h6
    exact Or.inr ⟨rfl, by simpa using h6⟩
  exfalso
  obtain ⟨g1, g2⟩ := u64_gen_dvd_twelve hL hU n p f
  have hG : (genericOrders t n p f).1 * (genericOrders t n p f).2 ∣ 144 :=
    (Nat.mul_dvd_mul g1 g2 : _ ∣ 12 * 12)
  have h144 := h.trans (Nat.mul_dvd_mul hG hE)
  norm_num at h144

theorem u64_five_center_label {Q : Type} [Group Q] [Finite Q] {lab : GLALabel}
    (hQ : CFSG.Open.IsQuasisimple Q) (hm : CFSG.StandardType.MarkedModel lab (Q ⧸ Subgroup.center Q))
    (h5 : 5 ∣ Nat.card (Subgroup.center Q)) :
    (lab.tag = .A ∧ 5 ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n - 1)) ∨
      (lab.tag = .twA ∧ 5 ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n + 1)) := by
  rcases u64_five_dvd_center_model hQ hm h5 with ⟨ht, hg⟩ | ⟨ht, hg⟩
  · rcases u64_tag_of_five (Or.inl ht) hg with h | h
    · refine Or.inl ⟨h, ?_⟩
      have e1 : markRank lab = lab.rank + 1 := by simp [markRank, h]
      have e2 : markChar lab = 2 := by simp [markChar, h]
      have e3 : markDeg lab = lab.n := by simp [markDeg, h]
      rw [e1, e2, e3] at hg
      exact hg
    · simp [markTag, h] at ht
  · rcases u64_tag_of_five (Or.inr ht) hg with h | h
    · simp [markTag, h] at ht
    · refine Or.inr ⟨h, ?_⟩
      have e1 : markRank lab = lab.rank + 1 := by simp [markRank, h]
      have e2 : markChar lab = 2 := by simp [markChar, h]
      have e3 : markDeg lab = lab.n := by simp [markDeg, h]
      rw [e1, e2, e3] at hg
      exact hg

theorem u64_five_center_of_marking {G : Type} [Group G] [Finite G] {K : Subgroup G} {lab : GLALabel}
    (hlab : GLAMarking (PQuot 5 K) fun lab' _ _ _ _ _ => lab' = lab)
    (h5 : 5 ∣ Nat.card (Subgroup.center (PQuot 5 K))) :
    (lab.tag = .A ∧ 4 ∣ lab.n ∧ 5 ∣ lab.rank + 1) ∨
      (lab.tag = .twA ∧ lab.n % 4 = 2 ∧ 5 ∣ lab.rank + 1) := by
  obtain ⟨hQ, hm⟩ := u64_marking_model hlab
  rcases u64_five_center_label hQ hm h5 with ⟨ht, hg⟩ | ⟨ht, hg⟩
  · exact Or.inl ⟨ht, u64_four_dvd_of_five_dvd_two_pow_sub_one (hg.trans (Nat.gcd_dvd_right _ _)),
      hg.trans (Nat.gcd_dvd_left _ _)⟩
  · exact Or.inr ⟨ht, u64_mod_four_of_five_dvd_two_pow_add_one (hg.trans (Nat.gcd_dvd_right _ _)),
      hg.trans (Nat.gcd_dvd_left _ _)⟩

end Griess

end CFSG.LocalAnalysis.GLTheoremA
