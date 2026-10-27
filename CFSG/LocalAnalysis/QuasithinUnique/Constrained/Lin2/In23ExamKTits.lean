module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKElem
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.Sporadic.Schreier.TitsQTModel
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsQTCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Certificate2264
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKTitsInputs
public import Certificates.Certificate4132
public import Certificates.Certificate4155
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate2263
public import Certificates.Certificate2267
public import Certificates.Certificate2268
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
public import Certificates.Certificate8033
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.RootCommutator
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
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.Schreier.TitsQT

namespace TitsExam

theorem titsW_check :
    isInvA 1755 conjFArr conjFInvArr = true ∧
    siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 conjWArr = true ∧
    (compA 1755 conjWArr conjXArr)[12]! = 78 ∧ (compA 1755 conjXArr conjWArr)[12]! = 101 ∧
    (compA 1755 conjWArr conjYArr)[12]! = 38 ∧ (compA 1755 conjYArr conjWArr)[12]! = 34 :=
  Certificates.certificate4132

@[expose] noncomputable def conjF : Equiv.Perm (Fin 1755) :=
  titsDGen 0 * titsDGen 1 * titsDGen 1 * titsDGen 1 * titsDGen 0 * titsDGen 0

theorem rep_conjF : Rep 1755 conjFArr conjF :=
  rep_compA (rep_compA (rep_compA (rep_compA (rep_compA rep_conjD0 rep_conjD1) rep_conjD1)
    rep_conjD1) rep_conjD0) rep_conjD0

theorem rep_conjFInv : Rep 1755 conjFInvArr conjF⁻¹ :=
  rep_inv_of_isInvA rep_conjF titsW_check.1

theorem conjF_mem : conjF ∈ titsD :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (titsDGen_mem_titsD (by norm_num))
    (titsDGen_mem_titsD (by norm_num))) (titsDGen_mem_titsD (by norm_num)))
    (titsDGen_mem_titsD (by norm_num))) (titsDGen_mem_titsD (by norm_num)))
    (titsDGen_mem_titsD (by norm_num))

theorem rep_conjW : Rep 1755 conjWArr (conjF * titsZ * conjF⁻¹) :=
  rep_compA (rep_compA rep_conjF titsZ_rep) rep_conjFInv

theorem conjW_mem_titsS : conjF * titsZ * conjF⁻¹ ∈ titsS :=
  mem_titsS_of_sift rep_conjW titsW_check.2.1

theorem tits_triple :
    ∃ g h f : Equiv.Perm (Fin 1755), g ∈ titsD ∧ h ∈ titsD ∧ f ∈ titsD ∧
      g * titsZ * g⁻¹ ∈ titsS ∧ h * titsZ * h⁻¹ ∈ titsS ∧ f * titsZ * f⁻¹ ∈ titsS ∧
      g * titsZ * g⁻¹ * (h * titsZ * h⁻¹) ≠ h * titsZ * h⁻¹ * (g * titsZ * g⁻¹) ∧
      g * titsZ * g⁻¹ * (f * titsZ * f⁻¹) ≠ f * titsZ * f⁻¹ * (g * titsZ * g⁻¹) ∧
      h * titsZ * h⁻¹ * (f * titsZ * f⁻¹) ≠ f * titsZ * f⁻¹ * (h * titsZ * h⁻¹) := by
  obtain ⟨hgD, hhD⟩ := conjugators_mem_titsD
  set g : Equiv.Perm (Fin 1755) :=
    (titsDGen 1)⁻¹ * titsDGen 0 * (titsDGen 1)⁻¹ * titsDGen 0 ^ 2 with hg
  set h : Equiv.Perm (Fin 1755) := (titsDGen 0)⁻¹ with hh
  obtain ⟨hxS, hyS, hxy, -, -⟩ :=
    QT_unique_Tits_central_involution_noncommuting_Sylow_conjugates g h hg hh
  have eX : g * titsZ * g⁻¹ =
      ((titsDGen 1)⁻¹ * titsDGen 0 * (titsDGen 1)⁻¹ * titsDGen 0 * titsDGen 0) * titsZ *
        ((titsDGen 0)⁻¹ * (titsDGen 0)⁻¹ * titsDGen 1 * (titsDGen 0)⁻¹ * titsDGen 1) := by
    rw [hg]
    simp only [pow_two, mul_inv_rev, inv_inv, mul_assoc]
  have eY : h * titsZ * h⁻¹ = (titsDGen 0)⁻¹ * titsZ * titsDGen 0 := by
    rw [hh]
    simp only [inv_inv]
  have hX : Rep 1755 conjXArr (g * titsZ * g⁻¹) := by
    rw [eX]
    exact rep_compA (rep_compA rep_conjG titsZ_rep) rep_conjGInv
  have hY : Rep 1755 conjYArr (h * titsZ * h⁻¹) := by
    rw [eY]
    exact rep_compA (rep_compA rep_conjD0Inv titsZ_rep) rep_conjD0
  obtain ⟨-, -, hw1, hw2, hw3, hw4⟩ := titsW_check
  refine ⟨g, h, conjF, hgD, hhD, conjF_mem, hxS, hyS, conjW_mem_titsS, hxy, ?_, ?_⟩
  · intro hxw
    have h1 := (rep_compA hX rep_conjW).apply (show 12 < 1755 by norm_num)
    have h2 := (rep_compA rep_conjW hX).apply (show 12 < 1755 by norm_num)
    rw [hw2] at h1
    rw [hw1] at h2
    rw [hxw] at h1
    omega
  · intro hyw
    have h1 := (rep_compA hY rep_conjW).apply (show 12 < 1755 by norm_num)
    have h2 := (rep_compA rep_conjW hY).apply (show 12 < 1755 by norm_num)
    rw [hw4] at h1
    rw [hw3] at h2
    rw [hyw] at h1
    omega

theorem tits_false (R₀ A₀ A₀' : Subgroup ↥titsD) (hRU : R₀ ≤ (titsSylow : Subgroup ↥titsD))
    (hnorm : ∀ n ∈ Subgroup.normalizer ((titsSylow : Subgroup ↥titsD) : Set ↥titsD),
      ∀ r ∈ R₀, n * r * n⁻¹ ∈ R₀)
    (hne : R₀ ≠ ⊥) (hA : IsElemAbelian 2 A₀) (hA' : IsElemAbelian 2 A₀')
    (hel : ∀ e ∈ R₀, e * e = 1 → e ∈ A₀ ∨ e ∈ A₀')
    (hstrong : ∀ r ∈ R₀, r * r = 1 → ∀ g : ↥titsD,
      g * r * g⁻¹ ∈ (titsSylow : Subgroup ↥titsD) → g * r * g⁻¹ ∈ R₀) : False := by
  obtain ⟨z', hz'R, hz'1, hz'c⟩ := CFSG.QuasithinUnique.K1.exists_ne_one_mem_centralizer
    (Q := (titsSylow : Subgroup ↥titsD)) titsSylow.isPGroup' hRU
    (fun a ha q hq => by
      have := hnorm q⁻¹ (Subgroup.le_normalizer (Subgroup.inv_mem _ hq)) a ha
      simpa using this) hne
  have hzR : titsZD ∈ R₀ := by
    rcases titsSylow_central_eq z' (hRU hz'R) hz'c with h1 | h1
    · exact absurd h1 hz'1
    · rw [← h1]; exact hz'R
  have hzz : titsZD * titsZD = 1 := Subtype.ext titsZ_mul_self
  obtain ⟨g, h, f, hgD, hhD, hfD, hgS, hhS, hfS, hgh, hgf, hhf⟩ := tits_triple
  have hmemS : ∀ w : ↥titsD, w ∈ (titsSylow : Subgroup ↥titsD) ↔
      (w : Equiv.Perm (Fin 1755)) ∈ titsS := fun w => by
    rw [coe_titsSylow]
    exact Subgroup.mem_subgroupOf
  have key : ∀ (c : Equiv.Perm (Fin 1755)) (hcD : c ∈ titsD), c * titsZ * c⁻¹ ∈ titsS →
      (⟨c, hcD⟩ : ↥titsD) * titsZD * (⟨c, hcD⟩ : ↥titsD)⁻¹ ∈ R₀ := by
    intro c hcD hcS
    exact hstrong titsZD hzR hzz ⟨c, hcD⟩ ((hmemS _).2 hcS)
  have hx := key g hgD hgS
  have hy := key h hhD hhS
  have hw := key f hfD hfS
  have hinv : ∀ (c : Equiv.Perm (Fin 1755)) (hcD : c ∈ titsD),
      ((⟨c, hcD⟩ : ↥titsD) * titsZD * (⟨c, hcD⟩ : ↥titsD)⁻¹) *
        ((⟨c, hcD⟩ : ↥titsD) * titsZD * (⟨c, hcD⟩ : ↥titsD)⁻¹) = 1 := by
    intro c hcD
    calc ((⟨c, hcD⟩ : ↥titsD) * titsZD * (⟨c, hcD⟩ : ↥titsD)⁻¹) *
          ((⟨c, hcD⟩ : ↥titsD) * titsZD * (⟨c, hcD⟩ : ↥titsD)⁻¹)
        = (⟨c, hcD⟩ : ↥titsD) * (titsZD * titsZD) * (⟨c, hcD⟩ : ↥titsD)⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  refine three_noncommuting (A := A₀) (A' := A₀')
    (fun a ha b hb => congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (fun a ha b hb => congrArg Subtype.val (hA'.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (hel _ hx (hinv g hgD)) (hel _ hy (hinv h hhD)) (hel _ hw (hinv f hfD)) ?_ ?_ ?_
  · intro hc
    exact hgh (congrArg Subtype.val hc)
  · intro hc
    exact hgf (congrArg Subtype.val hc)
  · intro hc
    exact hhf (congrArg Subtype.val hc)

end TitsExam

theorem examExcludes_tits : ExamExcludes FamTits := by
  rintro G _ _ K B B' P R m h hmodel
  obtain ⟨e⟩ := titsModelEquiv _ 2 1 hmodel
  let θ : ↥K →* ↥titsD := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθsurj : Function.Surjective θ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : θ.ker ≤ Subgroup.center ↥K := by
    intro x hx
    have hx' : e (QuotientGroup.mk x) = 1 := hx
    rwa [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff] at hx'
  have hU : IsSylowTwoOf (titsSylow : Subgroup ↥titsD) ⊤ :=
    CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨titsSylow.isPGroup', titsSylow.not_dvd_index⟩
  obtain ⟨R₀, A₀, A₀', hRU, hnorm, hne, hA, hA', hel, hstrong⟩ :=
    h.toAbs.exists_RprimeE θ hθsurj hker _ hU
  exact TitsExam.tits_false R₀ A₀ A₀' hRU hnorm hne hA hA' hel hstrong

end CFSG.QuasithinUnique.Lin2
