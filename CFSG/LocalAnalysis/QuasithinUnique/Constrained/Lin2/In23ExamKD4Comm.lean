module

public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKElem
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.Foundations
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace D4Exam

section Abstract

variable {G : Type*} [Group G]

theorem comm_expand {A Y0 Y1 Y3 M0 M1 M3 N01 N03 N13 P H : G}
    (hA0 : ⁅A, Y0⁆ = M0) (hA1 : ⁅A, Y1⁆ = M1) (hA3 : ⁅A, Y3⁆ = M3)
    (h01 : ⁅Y0, M1⁆ = N01) (h13 : ⁅Y1, M3⁆ = N13) (h03 : ⁅Y0, M3⁆ = N03)
    (hP : ⁅Y0, N13⁆ = P) (hH : ⁅N01, M3⁆ = H)
    (c1 : Commute N01 M1) (c2 : Commute M3 N03) (c3 : Commute M3 N13) (c4 : Commute M3 P)
    (cH3 : Commute H M3) (cH01 : Commute H N01) (cHP : Commute H P) (cH13 : Commute H N13)
    (cH03 : Commute H N03) (c0113 : Commute N01 N13)
    (c0103 : Commute N01 N03) (cP13 : Commute P N13) (cP03 : Commute P N03) :
    ⁅A, Y0 * Y1 * Y3⁆ = M0 * M1 * M3 * (N13 * N03 * N01) * P * H := by
  have rA0 : A * Y0 * A⁻¹ = M0 * Y0 := by rw [← hA0, commutatorElement_def]; group
  have rA1 : A * Y1 * A⁻¹ = M1 * Y1 := by rw [← hA1, commutatorElement_def]; group
  have rA3 : A * Y3 * A⁻¹ = M3 * Y3 := by rw [← hA3, commutatorElement_def]; group
  have r01 : Y0 * M1 * Y0⁻¹ = N01 * M1 := by rw [← h01, commutatorElement_def]; group
  have r13 : Y1 * M3 * Y1⁻¹ = N13 * M3 := by rw [← h13, commutatorElement_def]; group
  have r03 : Y0 * M3 * Y0⁻¹ = N03 * M3 := by rw [← h03, commutatorElement_def]; group
  have rP : Y0 * N13 * Y0⁻¹ = P * N13 := by rw [← hP, commutatorElement_def]; group
  have rH : ∀ w : G, N01 * (M3 * w) = H * (M3 * (N01 * w)) := fun w => by
    rw [← hH, commutatorElement_def]; group
  have s1 : ⁅A, Y0 * Y1 * Y3⁆ =
      (A * Y0 * A⁻¹) * (A * Y1 * A⁻¹) * (A * Y3 * A⁻¹) * (Y3⁻¹ * Y1⁻¹ * Y0⁻¹) := by
    rw [commutatorElement_def]; group
  rw [s1, rA0, rA1, rA3]
  have s2 : M0 * Y0 * (M1 * Y1) * (M3 * Y3) * (Y3⁻¹ * Y1⁻¹ * Y0⁻¹) =
      M0 * Y0 * M1 * (Y1 * M3 * Y1⁻¹) * Y0⁻¹ := by group
  rw [s2, r13]
  have s3 : M0 * Y0 * M1 * (N13 * M3) * Y0⁻¹ =
      M0 * ((Y0 * M1 * Y0⁻¹) * (Y0 * N13 * Y0⁻¹) * (Y0 * M3 * Y0⁻¹)) := by group
  rw [s3, r01, rP, r03]
  simp only [mul_assoc]
  rw [c1.left_comm, ← c2.eq, c3.symm.left_comm, c4.symm.left_comm, rH, cH3.left_comm,
    cH01.left_comm, cHP.left_comm, cH13.left_comm, cH03.eq, cP13.left_comm, cP03.left_comm,
    c0113.left_comm, c0103.left_comm]

theorem core_abstract {R A A' : Subgroup G} {a b p q h w : G}
    (ha : a ∈ R) (hb : b ∈ R) (hh : h ∈ R) (hw : ⁅a, w⁆ = p * q * b * h)
    (hRw : ∀ r ∈ R, w * r * w⁻¹ ∈ R) (hab : ⁅a, b⁆ = h) (hpq : ⁅p, q⁆ = h)
    (haa : a * a = 1) (hbb : b * b = 1) (hpp : p * p = 1) (hqq : q * q = 1) (hhh : h * h = 1)
    (hh1 : h ≠ 1) (cap : Commute a p) (caq : Commute a q) (cbp : Commute b p)
    (cbq : Commute b q) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA' : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x)
    (hel : ∀ e ∈ R, e * e = 1 → e ∈ A ∨ e ∈ A') : False := by
  have h1 : ⁅a, w⁆ ∈ R := by
    have : ⁅a, w⁆ = a * (w * a⁻¹ * w⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    refine R.mul_mem ha ?_
    have h2 : w * a * w⁻¹ ∈ R := hRw a ha
    have : w * a⁻¹ * w⁻¹ = (w * a * w⁻¹)⁻¹ := by group
    rw [this]
    exact R.inv_mem h2
  have hpqR : p * q ∈ R := by
    have e : p * q = (p * q * b * h) * h⁻¹ * b⁻¹ := by group
    rw [e, ← hw]
    exact R.mul_mem (R.mul_mem h1 (R.inv_mem hh)) (R.inv_mem hb)
  set e := a * b * (p * q) with he
  have heR : e ∈ R := R.mul_mem (R.mul_mem ha hb) hpqR
  have cpa : Commute a (p * q) := cap.mul_right caq
  have cpb : Commute b (p * q) := cbp.mul_right cbq
  have eab : a * b = h * b * a := by rw [← hab, commutatorElement_def]; group
  have epq : p * q = h * q * p := by rw [← hpq, commutatorElement_def]; group
  have habab : a * b * (a * b) = h := by
    have : a * b * (a * b) = (h * b * a) * (a * b) := by rw [← eab]
    rw [this]
    calc h * b * a * (a * b) = h * (b * (a * a) * b) := by group
      _ = h := by rw [haa]; simp [hbb]
  have hpqpq : p * q * (p * q) = h := by
    have : p * q * (p * q) = (h * q * p) * (p * q) := by rw [← epq]
    rw [this]
    calc h * q * p * (p * q) = h * (q * (p * p) * q) := by group
      _ = h := by rw [hpp]; simp [hqq]
  have hee : e * e = 1 := by
    have hc : Commute (p * q) (a * b) := cpa.symm.mul_right cpb.symm
    calc e * e = (a * b) * ((p * q) * (a * b)) * (p * q) := by rw [he]; group
      _ = (a * b) * ((a * b) * (p * q)) * (p * q) := by rw [hc.eq]
      _ = ((a * b) * (a * b)) * ((p * q) * (p * q)) := by group
      _ = 1 := by rw [habab, hpqpq, hhh]
  have nab : a * b ≠ b * a := by
    intro hc
    apply hh1
    rw [← hab, commutatorElement_def]
    calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [hc]
      _ = 1 := by group
  have nae : a * e ≠ e * a := by
    intro hc
    apply nab
    have e1 : a * e = b * (p * q) := by
      calc a * e = (a * a) * b * (p * q) := by rw [he]; group
        _ = b * (p * q) := by rw [haa, one_mul]
    have e2 : e * a = a * b * a * (p * q) := by
      calc e * a = a * b * ((p * q) * a) := by rw [he]; group
        _ = a * b * (a * (p * q)) := by rw [cpa.eq]
        _ = a * b * a * (p * q) := by group
    rw [e1, e2] at hc
    have e3 : b = a * b * a := mul_right_cancel hc
    calc a * b = a * b * (a * a) := by rw [haa, mul_one]
      _ = (a * b * a) * a := by group
      _ = b * a := by rw [← e3]
  have nbe : b * e ≠ e * b := by
    intro hc
    apply nab
    have e1 : b * e = b * a * b * (p * q) := by rw [he]; group
    have e2 : e * b = a * (p * q) := by
      calc e * b = a * b * ((p * q) * b) := by rw [he]; group
        _ = a * b * (b * (p * q)) := by rw [cpb.eq]
        _ = a * (b * b) * (p * q) := by group
        _ = a * (p * q) := by rw [hbb, mul_one]
    rw [e1, e2] at hc
    have e3 : b * a * b = a := mul_right_cancel (by
      calc b * a * b * (p * q) = a * (p * q) := hc)
    calc a * b = (b * a * b) * b := by rw [e3]
      _ = b * a * (b * b) := by group
      _ = b * a := by rw [hbb, mul_one]
  exact three_noncommuting hA hA' (hel a ha haa) (hel b hb hbb) (hel e heR hee) nab nae nbe

end Abstract

section Roots

@[expose] def rC : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 1, 0]

@[expose] def rE0 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 0, 0]
@[expose] def rE1 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 1, 0, 0]
@[expose] def rE3 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 0, 1]

@[expose] def rM0 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 1, 0]
@[expose] def rM1 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 1, 1, 0]
@[expose] def rM3 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 1, 1]

@[expose] def rN01 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 1, 0]
@[expose] def rN03 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 1, 1]
@[expose] def rN13 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 1, 1, 1]

@[expose] def rP : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 1, 1]
@[expose] def rH : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 2, 1]

end Roots

section D4

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem comm_root
    (β : K) :
    ⁅Xr rC β, Xr rE0 1 * Xr rE1 1 * Xr rE3 1⁆ =
      Xr rM0 β * Xr rM1 β * Xr rM3 β * (Xr rN13 β * Xr rN03 β * Xr rN01 β) * Xr rP β *
        Xr rH (β * β) := by
  have hs : ∀ {α γ δ : Fin TwistTag.D4.tag.rank → ℤ}, d4SumB α γ δ = true → ∀ s t : K,
      ⁅Xr α s, Xr γ t⁆ = Xr δ (s * t) := fun h s t => commutator_of_d4SumB h s t
  have hc : ∀ {α γ : Fin TwistTag.D4.tag.rank → ℤ}, d4CommB α γ = true → ∀ s t : K,
      Commute (Xr α s) (Xr γ t) := fun h s t => commute_of_d4CommB h s t
  refine comm_expand (A := Xr rC β) (Y0 := Xr rE0 1) (Y1 := Xr rE1 1) (Y3 := Xr rE3 1)
    (M0 := Xr rM0 β) (M1 := Xr rM1 β) (M3 := Xr rM3 β) (N01 := Xr rN01 β) (N03 := Xr rN03 β)
    (N13 := Xr rN13 β) (P := Xr rP β) (H := Xr rH (β * β)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have := hs (α := rC) (γ := rE0) (δ := rM0) (by decide +kernel) β 1
    rwa [mul_one] at this
  · have := hs (α := rC) (γ := rE1) (δ := rM1) (by decide +kernel) β 1
    rwa [mul_one] at this
  · have := hs (α := rC) (γ := rE3) (δ := rM3) (by decide +kernel) β 1
    rwa [mul_one] at this
  · have := hs (α := rE0) (γ := rM1) (δ := rN01) (by decide +kernel) 1 β
    rwa [one_mul] at this
  · have := hs (α := rE1) (γ := rM3) (δ := rN13) (by decide +kernel) 1 β
    rwa [one_mul] at this
  · have := hs (α := rE0) (γ := rM3) (δ := rN03) (by decide +kernel) 1 β
    rwa [one_mul] at this
  · have := hs (α := rE0) (γ := rN13) (δ := rP) (by decide +kernel) 1 β
    rwa [one_mul] at this
  · exact hs (α := rN01) (γ := rM3) (δ := rH) (by decide +kernel) β β
  · exact hc (α := rN01) (γ := rM1) (by decide +kernel) β β
  · exact hc (α := rM3) (γ := rN03) (by decide +kernel) β β
  · exact hc (α := rM3) (γ := rN13) (by decide +kernel) β β
  · exact hc (α := rM3) (γ := rP) (by decide +kernel) β β
  · exact hc (α := rH) (γ := rM3) (by decide +kernel) (β * β) β
  · exact hc (α := rH) (γ := rN01) (by decide +kernel) (β * β) β
  · exact hc (α := rH) (γ := rP) (by decide +kernel) (β * β) β
  · exact hc (α := rH) (γ := rN13) (by decide +kernel) (β * β) β
  · exact hc (α := rH) (γ := rN03) (by decide +kernel) (β * β) β
  · exact hc (α := rN01) (γ := rN13) (by decide +kernel) β β
  · exact hc (α := rN01) (γ := rN03) (by decide +kernel) β β
  · exact hc (α := rP) (γ := rN13) (by decide +kernel) β β
  · exact hc (α := rP) (γ := rN03) (by decide +kernel) β β

end D4

end D4Exam

end CFSG.QuasithinUnique.Lin2
