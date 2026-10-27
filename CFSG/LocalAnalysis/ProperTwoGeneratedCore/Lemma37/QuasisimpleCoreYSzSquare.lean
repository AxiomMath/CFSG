module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightRoot
public import Certificates.Certificate113
public import CFSG.GH74.Statements
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.NonSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBound
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Remaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.WalterRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.TheoremC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI

theorem card_center_sylow_szModel {L : Type*} [Group L] [Finite L]
    (e : L ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) (R : Sylow 2 L) :
    Nat.card (Subgroup.center (R : Subgroup L)) = 8 := by
  let e' : L ≃* SuzukiMatrixGroup 1 :=
    e.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup 1))
  obtain ⟨θ⟩ := CFSG.ProperTwoGeneratedCore.BenderFacts.nonempty_sylow_mulEquiv_of_mulEquiv e' R
    (suzukiCoverSylow 1 one_pos)
  rw [Nat.card_congr (Subgroup.centerCongr θ).toEquiv]
  change Nat.card (Subgroup.center (suzukiCoverRoot 1)) = 8
  rw [← (suzukiCoverRoot_structure 1 one_pos).2.2.1, suzukiCoverDerived_card 1 one_pos]
  norm_num

theorem exists_independent_triple {C : Type*} [Group C] [Finite C] (hC : Nat.card C = 8)
    (hsq : ∀ x : C, x * x = 1) :
    ∃ a b c : C, a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ a * b ≠ 1 ∧ a * c ≠ 1 ∧ b * c ≠ 1 ∧
      a * b * c ≠ 1 := by
  classical
  have : Fintype C := Fintype.ofFinite C
  have hcard : Fintype.card C = 8 := by rw [Fintype.card_eq_nat_card, hC]
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset C)) (t := Finset.univ)
    (by rw [Finset.card_univ, hcard, Finset.card_singleton]; norm_num)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a} : Finset C)) (t := Finset.univ)
    (by rw [Finset.card_univ, hcard]; exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a, b, a * b} : Finset C)) (t := Finset.univ)
    (by rw [Finset.card_univ, hcard]; exact lt_of_le_of_lt Finset.card_le_four (by norm_num))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha hb hc
  have hinv : ∀ x y : C, x * y = 1 → y = x := fun x y h => by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (hsq x)]
  refine ⟨a, b, c, ha, hb.1, hc.1, fun h => hb.2 (hinv a b h), fun h => hc.2.1 (hinv a c h),
    fun h => hc.2.2.1 (hinv b c h), fun h => hc.2.2.2 (hinv (a * b) c h)⟩

theorem mul_comm_of_mul_self {G : Type*} [Group G] {x y z : G} (hz : ∀ g : G, g * z = z * g)
    (hzz : z * z = 1) (hx : x * x = z) (hy : y * y = z) (hxy : x * y * (x * y) = z) :
    y * x = x * y * z := by
  have h : x * (y * x) * y = x * (x * y * z) * y := by
    calc x * (y * x) * y = x * y * (x * y) := by group
      _ = z * z * z := by rw [hxy, hzz, one_mul]
      _ = x * x * (y * y) * z := by rw [hx, hy]
      _ = x * x * y * (y * z) := by group
      _ = x * x * y * (z * y) := by rw [hz y]
      _ = x * (x * y * z) * y := by group
  exact mul_left_cancel (mul_right_cancel h)

theorem mul_mul_self_eq_one_of_mul_self {G : Type*} [Group G] {a b c z : G}
    (hz : ∀ g : G, g * z = z * g) (hzz : z * z = 1) (ha : a * a = z) (hb : b * b = z)
    (hc : c * c = z) (hab : a * b * (a * b) = z) (hac : a * c * (a * c) = z)
    (hbc : b * c * (b * c) = z) : a * b * c * (a * b * c) = 1 := by
  have hca := mul_comm_of_mul_self hz hzz ha hc hac
  have hcb := mul_comm_of_mul_self hz hzz hb hc hbc
  have hcab : c * (a * b) = a * b * c := by
    calc c * (a * b) = c * a * b := by group
      _ = a * c * z * b := by rw [hca]
      _ = a * c * (z * b) := by group
      _ = a * c * (b * z) := by rw [hz b]
      _ = a * (c * b) * z := by group
      _ = a * (b * c * z) * z := by rw [hcb]
      _ = a * b * c * (z * z) := by group
      _ = a * b * c := by rw [hzz, mul_one]
  calc a * b * c * (a * b * c) = a * b * (c * (a * b)) * c := by group
    _ = a * b * (a * b * c) * c := by rw [hcab]
    _ = a * b * (a * b) * (c * c) := by group
    _ = 1 := by rw [hab, hc, hzz]

theorem mul_self_eq_one_of_szModel {K : Type} [Group K] [Finite K]
    (hZ : Nat.card (Subgroup.center K) = 2)
    (e : K ⧸ Subgroup.center K ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) {k : K}
    (hk : k * k ∈ Subgroup.center K) : k * k = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center K with hZdef
  set π := QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hZsq : ∀ c ∈ Z, c * c = 1 := fun c hc => by
    have h := pow_card_eq_one' (G := Z) (x := ⟨c, hc⟩)
    rw [hZ, pow_two] at h
    exact congrArg Subtype.val h
  by_contra hk1
  set z := k * k with hzdef
  have hzc : ∀ g : K, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hk g
  have hzz : z * z = 1 := hZsq z hk
  have hZmem : ∀ c ∈ Z, c = 1 ∨ c = z := by
    intro c hc
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    right
    obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
    have h1 := hyu ⟨c, hc⟩ fun h' => hc1 (congrArg Subtype.val h')
    have h2 := hyu ⟨z, hk⟩ fun h' => hk1 (congrArg Subtype.val h')
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hkp : IsPGroup 2 (Subgroup.zpowers k) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_one, pow_two]
      exact hk1
    · rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two]
      exact hzz
  obtain ⟨R, hkR⟩ := hkp.exists_le_sylow
  set Rs : Sylow 2 (K ⧸ Z) := R.mapSurjective hπ with hRsdef
  have hRs : (Rs : Subgroup (K ⧸ Z)) = (R : Subgroup K).map π := Sylow.coe_mapSurjective _ _
  have hSF := szEightSylowFacts_of_mulEquiv e Rs
  have hBF : BenderBorelFacts (K ⧸ Z) ((R : Subgroup K).map π) := by
    rw [← hRs]
    exact benderBorelFactsHold _ (.isSuzuki 1 le_rfl e) Rs
  have hcen : ∀ y : Subgroup.center (Rs : Subgroup (K ⧸ Z)),
      InCenterOf ((R : Subgroup K).map π) ((y : Rs) : K ⧸ Z) := by
    intro y
    refine ⟨hRs ▸ (y : Rs).2, fun q hq => ?_⟩
    have h := Subgroup.mem_center_iff.mp y.2 ⟨q, hRs ▸ hq⟩
    exact congrArg Subtype.val h
  have hkS : π k ∈ (Rs : Subgroup (K ⧸ Z)) := hRs ▸ Subgroup.mem_map_of_mem π (hkR
    (Subgroup.mem_zpowers k))
  have hkk : π k * π k = 1 := by
    rw [← map_mul, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  have hkc : InCenterOf ((R : Subgroup K).map π) (π k) := by
    have h := hSF.comm_of_sq ⟨π k, hkS⟩ (Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]
      exact hkk))
    exact ⟨hRs ▸ hkS, fun q hq => (congrArg Subtype.val (h ⟨q, hRs ▸ hq⟩)).symm⟩
  suffices hx : ∃ x : K, x * x = 1 ∧ InCenterOf ((R : Subgroup K).map π) (π x) ∧ π x ≠ 1 by
    obtain ⟨x, hxx, hxc, hx1⟩ := hx
    exact hk1 (mul_self_eq_one_of_torus hZsq hBF hxx hxc hx1 hkc)
  by_contra hno
  push Not at hno
  have hsq : ∀ (y : Subgroup.center (Rs : Subgroup (K ⧸ Z))) (x : K),
      π x = ((y : Rs) : K ⧸ Z) → y ≠ 1 → x * x = z := by
    intro y x hxy hy1
    have hxc : InCenterOf ((R : Subgroup K).map π) (π x) := hxy ▸ hcen y
    have hx1 : π x ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext (hxy.symm.trans h)))
    have hxZ : x * x ∈ Z := by
      have h := hSF.sq_of_comm (y : Rs) fun w => (Subgroup.mem_center_iff.mp y.2 w).symm
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπdef, map_mul, hxy,
        ← pow_two]
      exact congrArg Subtype.val h
    exact (hZmem _ hxZ).resolve_left fun h => hx1 (hno x h hxc)
  have hcard := card_center_sylow_szModel e Rs
  have hsqC : ∀ y : Subgroup.center (Rs : Subgroup (K ⧸ Z)), y * y = 1 := fun y => by
    have h := hSF.sq_of_comm (y : Rs) fun w => (Subgroup.mem_center_iff.mp y.2 w).symm
    rw [pow_two] at h
    exact Subtype.ext h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, habc⟩ := exists_independent_triple hcard hsqC
  obtain ⟨a', ha'⟩ := hπ ((a : Rs) : K ⧸ Z)
  obtain ⟨b', hb'⟩ := hπ ((b : Rs) : K ⧸ Z)
  obtain ⟨c', hc'⟩ := hπ ((c : Rs) : K ⧸ Z)
  have h3 := mul_mul_self_eq_one_of_mul_self hzc hzz (hsq a a' ha' ha) (hsq b b' hb' hb)
    (hsq c c' hc' hc) (hsq (a * b) (a' * b') (by rw [map_mul, ha', hb']; rfl) hab)
    (hsq (a * c) (a' * c') (by rw [map_mul, ha', hc']; rfl) hac)
    (hsq (b * c) (b' * c') (by rw [map_mul, hb', hc']; rfl) hbc)
  have h4 := hsq (a * b * c) (a' * b' * c') (by rw [map_mul, map_mul, ha', hb', hc']; rfl) habc
  exact hk1 (h4.symm.trans h3)

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
