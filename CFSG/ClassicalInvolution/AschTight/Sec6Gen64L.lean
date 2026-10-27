module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64K
public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2Layer
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen610
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen611
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64I
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64J
public import CFSG.ClassicalInvolution.AschTight.Thm6Tight
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
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

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

variable {G : Type} [Group G]

section Bar

variable {Y : Subgroup G} (X : Subgroup G) [(X.subgroupOf Y).Normal]

@[expose] def bar {g : G} (hg : g ∈ Y) : ↥Y ⧸ X.subgroupOf Y := QuotientGroup.mk ⟨g, hg⟩

theorem bar_mul {g h : G} (hg : g ∈ Y) (hh : h ∈ Y) :
    bar X hg * bar X hh = bar X (Y.mul_mem hg hh) := rfl

theorem bar_inv {g : G} (hg : g ∈ Y) : (bar X hg)⁻¹ = bar X (Y.inv_mem hg) := rfl

theorem bar_one : bar X (Y.one_mem) = 1 := rfl

theorem bar_pow {g : G} (hg : g ∈ Y) (n : ℕ) : bar X hg ^ n = bar X (Y.pow_mem hg n) := by
  unfold bar
  rw [← QuotientGroup.mk_pow]
  rfl

theorem bar_zpow {g : G} (hg : g ∈ Y) (n : ℤ) : bar X hg ^ n = bar X (Y.zpow_mem hg n) := by
  unfold bar
  rw [← QuotientGroup.mk_zpow]
  rfl

theorem bar_eq_one_iff {g : G} (hg : g ∈ Y) : bar X hg = 1 ↔ g ∈ X := by
  unfold bar
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf

omit [(X.subgroupOf Y).Normal] in
theorem bar_eq_bar_iff {g h : G} (hg : g ∈ Y) (hh : h ∈ Y) :
    bar X hg = bar X hh ↔ g⁻¹ * h ∈ X := by
  unfold bar
  rw [QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf

omit [(X.subgroupOf Y).Normal] in
theorem exists_bar_eq (q : ↥Y ⧸ X.subgroupOf Y) : ∃ g : G, ∃ hg : g ∈ Y, bar X hg = q := by
  induction q using QuotientGroup.induction_on with
  | H y => exact ⟨y, y.2, rfl⟩

omit [(X.subgroupOf Y).Normal] in
theorem conj_eq_of_bar_eq {y y' : G} (hy : y ∈ Y) (hy' : y' ∈ Y) (h : bar X hy = bar X hy')
    {w : G} (hw : X ≤ Subgroup.centralizer ({w} : Set G)) : y * w * y⁻¹ = y' * w * y'⁻¹ := by
  have hx : y⁻¹ * y' ∈ X := (bar_eq_bar_iff X hy hy').mp h
  have hc : (y⁻¹ * y') * w = w * (y⁻¹ * y') := Subgroup.mem_centralizer_singleton_iff.mp (hw hx)
  have e : y' = y * (y⁻¹ * y') := by group
  rw [e]
  calc y * w * y⁻¹ = y * w * (y⁻¹ * y') * (y⁻¹ * y')⁻¹ * y⁻¹ := by group
    _ = y * ((y⁻¹ * y') * w) * (y⁻¹ * y')⁻¹ * y⁻¹ := by rw [mul_assoc y w, ← hc]
    _ = y * (y⁻¹ * y') * w * (y * (y⁻¹ * y'))⁻¹ := by group

end Bar

variable [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G} {z j u v : G}

structure Cfg64D (Ω : Set (Subgroup G)) (K J : Subgroup G) (z j u v : G)
    (R T N₀K N₀J : Subgroup G) (r t : G) : Prop where
  c : Cfg64 Ω K J z j u v R T
  hK0 : OddCompl (K ⊓ Subgroup.centralizer ({j} : Set G)) (Subgroup.zpowers u) N₀K
  hJ0 : OddCompl (J ⊓ Subgroup.centralizer ({z} : Set G)) (Subgroup.zpowers v) N₀J
  hr : r ∈ R
  hru : r ∉ Subgroup.zpowers u
  ht : t ∈ T
  htv : t ∉ Subgroup.zpowers v

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

theorem normal : ((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer d.c.X_le_Y).mpr
    (d.c.Y_le_normalizer_X d.hK0 d.hJ0)

theorem r_mem_Y : r ∈ pairNormalizers K J z j := d.c.R_le_Y d.hr

theorem t_mem_Y : t ∈ pairNormalizers K J z j := d.c.T_le_Y d.ht

theorem rho_mem_Y : r * t ∈ pairNormalizers K J z j := Subgroup.mul_mem _ d.r_mem_Y d.t_mem_Y

theorem U_le_X : Subgroup.zpowers u ≤ 𝕏(K, J) :=
  fun _ hx => d.c.X_eq ▸ Subgroup.mem_sup_right ⟨d.c.hUK hx, d.c.U_le_centralizer hx⟩

theorem V_le_X : Subgroup.zpowers v ≤ 𝕏(K, J) :=
  fun _ hx => d.c.X_eq ▸ Subgroup.mem_sup_left ⟨d.c.hVJ hx, d.c.symm.U_le_centralizer hx⟩

theorem R_le : R ≤ 𝕏(K, J) ⊔ Subgroup.zpowers r := by
  intro r' hr'
  by_cases h : r' ∈ Subgroup.zpowers u
  · exact Subgroup.mem_sup_left (d.U_le_X h)
  · have h1 : r⁻¹ * r' ∈ Subgroup.zpowers u :=
      AscL62.inv_mul_mem_of_index_two d.c.huR d.c.natCard_R d.hr hr' d.hru h
    have := Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers r))
      (Subgroup.mem_sup_left (d.U_le_X h1))
    simpa using this

theorem T_le : T ≤ 𝕏(K, J) ⊔ Subgroup.zpowers t := by
  intro t' ht'
  by_cases h : t' ∈ Subgroup.zpowers v
  · exact Subgroup.mem_sup_left (d.V_le_X h)
  · have h1 : t⁻¹ * t' ∈ Subgroup.zpowers v :=
      AscL62.inv_mul_mem_of_index_two d.c.hvT d.c.symm.natCard_R d.ht ht' d.htv h
    have := Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_left (d.V_le_X h1))
    simpa using this

theorem conj_rho_zpow_three_z (k : ℤ) : (r * t) ^ (3 * k) * z * ((r * t) ^ (3 * k))⁻¹ = z :=
  (d.c.conj_rho_zpow_z_eq_iff d.hr d.hru d.ht d.htv (3 * k)).mpr (dvd_mul_right 3 k)

theorem conj_rho_zpow_three_j (k : ℤ) : (r * t) ^ (3 * k) * j * ((r * t) ^ (3 * k))⁻¹ = j := by
  have h3 := d.c.conj_rho3_j d.hr d.hru d.ht d.htv
  have e3 : (r * t) ^ (3 : ℤ) = (r * t) ^ (3 : ℕ) := zpow_natCast (r * t) 3
  have hc : Commute ((r * t) ^ (3 : ℤ)) j := by
    rw [e3]
    show (r * t) ^ 3 * j = j * (r * t) ^ 3
    calc (r * t) ^ 3 * j = (r * t) ^ 3 * j * ((r * t) ^ 3)⁻¹ * (r * t) ^ 3 := by group
      _ = j * (r * t) ^ 3 := by rw [h3]
  rw [zpow_mul, (hc.zpow_left k).eq]
  group

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
