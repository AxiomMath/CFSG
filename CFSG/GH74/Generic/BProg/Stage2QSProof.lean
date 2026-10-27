module

public import CFSG.GH74.Generic.BProg.Stage2QS
public import CFSG.GH74.Generic.BProg.Stage2QSProofAbs
public import CFSG.GH74.Generic.Front.Transfer
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Th2Sig10
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.Generic.BProg.Assembly
public import CFSG.GH74.Generic.BProg.NS.Leaf
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement MatrixGroups

theorem exists_noncomm_two_elements_of_isQuasi2CompIn {Y : Type} [Group Y] [Finite Y]
    {H Lb : Subgroup Y} (h : IsQuasi2CompIn H Lb) :
    Lb ≤ H ∧ ∃ a b : Y, a ∈ Lb ∧ b ∈ Lb ∧ (∃ k : ℕ, a ^ (2 ^ k) = 1) ∧
      (∃ k : ℕ, b ^ (2 ^ k) = 1) ∧ a * b ≠ b * a := by
  rcases h with ⟨hle, hcomp⟩ | ⟨Lbb, -, ⟨e⟩, hLb⟩
  · refine ⟨hle, ?_⟩
    have : Group.IsPerfect ↥(Lb.subgroupOf H) :=
      CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hcomp
    have : Nontrivial ↥(Lb.subgroupOf H) :=
      CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hcomp
    obtain ⟨a, b, ⟨k, ha⟩, ⟨l, hb⟩, hab⟩ :=
      exists_noncomm_two_elements_of_perfect (M := ↥(Lb.subgroupOf H))
    refine ⟨((a : ↥H) : Y), ((b : ↥H) : Y), Subgroup.mem_subgroupOf.1 a.2,
      Subgroup.mem_subgroupOf.1 b.2, ⟨k, ?_⟩, ⟨l, ?_⟩, fun hcom => hab ?_⟩
    · have := congrArg (fun z : ↥(Lb.subgroupOf H) => ((z : ↥H) : Y)) ha
      simpa using this
    · have := congrArg (fun z : ↥(Lb.subgroupOf H) => ((z : ↥H) : Y)) hb
      simpa using this
    · exact Subtype.ext (Subtype.ext hcom)
  · have hLbH : Lb ≤ H := by
      rw [hLb]
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    refine ⟨hLbH, ?_⟩
    obtain ⟨s, t, hs, ht, hst⟩ := exists_noncomm_sl23
    have lift : ∀ u : SL(2, ZMod 3), u ^ 4 = 1 → ∃ z : ↥H, (∃ k : ℕ, z ^ (2 ^ k) = 1) ∧
        QuotientGroup.mk' (pPrimeCore 2 ↥H) z = ((e.symm u : ↥Lbb) : ↥H ⧸ pPrimeCore 2 ↥H) := by
      intro u hu
      obtain ⟨h₀, hh₀⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H)
        ((e.symm u : ↥Lbb) : ↥H ⧸ pPrimeCore 2 ↥H)
      have hk : (QuotientGroup.mk' (pPrimeCore 2 ↥H) h₀) ^ (2 ^ 2) = 1 := by
        rw [hh₀]
        have : (e.symm u) ^ (2 ^ 2) = 1 := by
          rw [← map_pow]
          have : u ^ (2 ^ 2) = 1 := hu
          rw [this, map_one]
        exact congrArg Subtype.val this
      obtain ⟨n, m, hnm, hqn⟩ :=
        exists_pow_two_power_lift (QuotientGroup.mk' (pPrimeCore 2 ↥H)) h₀ hk
      exact ⟨h₀ ^ n, ⟨m, hnm⟩, hqn.trans hh₀⟩
    obtain ⟨zs, ⟨ks, hks⟩, hqs⟩ := lift s hs
    obtain ⟨zt, ⟨kt, hkt⟩, hqt⟩ := lift t ht
    have hmem : ∀ (z : ↥H) (u : SL(2, ZMod 3)),
        QuotientGroup.mk' (pPrimeCore 2 ↥H) z = ((e.symm u : ↥Lbb) : ↥H ⧸ pPrimeCore 2 ↥H) →
        ((z : ↥H) : Y) ∈ Lb := fun z u hz => by
      rw [hLb]
      exact ⟨z, Subgroup.mem_comap.2 (by rw [hz]; exact (e.symm u).2), rfl⟩
    refine ⟨((zs : ↥H) : Y), ((zt : ↥H) : Y), hmem zs s hqs, hmem zt t hqt, ⟨ks, ?_⟩, ⟨kt, ?_⟩,
      fun hcom => hst ?_⟩
    · have := congrArg (fun z : ↥H => (z : Y)) hks
      simpa using this
    · have := congrArg (fun z : ↥H => (z : Y)) hkt
      simpa using this
    · have h1 : zs * zt = zt * zs := Subtype.ext hcom
      have h2 := congrArg (QuotientGroup.mk' (pPrimeCore 2 ↥H)) h1
      rw [map_mul, map_mul, hqs, hqt] at h2
      have h3 : (e.symm s) * (e.symm t) = (e.symm t) * (e.symm s) := Subtype.ext h2
      have h4 := congrArg e h3
      simpa using h4

theorem exists_mem_liftAt_of_two_pow_eq_one {G : Type} [Group G] [Finite G] {x y : G}
    (hy : y ∈ centralizer ({x} : Set G)) (hy2 : y * y = 1)
    {Lb : Subgroup (CentralizerBar x)} {a : CentralizerBar x} (ha : a ∈ Lb)
    (hay : a * bar x y = bar x y * a) {k : ℕ} (hk : a ^ (2 ^ k) = 1) :
    ∃ (g : G) (hg : g ∈ centralizer ({x} : Set G)), g ∈ liftAt x y Lb ∧
      proj x ⟨g, hg⟩ = a ∧ ∃ m : ℕ, g ^ (2 ^ m) = 1 := by
  classical
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  let u : ↥C := ⟨y, hy⟩
  have hu2 : u * u = 1 := Subtype.ext hy2
  have hbar : bar x y = proj x u := bar_of_mem hy
  obtain ⟨g', hg'u, hg'a⟩ := proj_cent x hu2 a (by rw [← hbar]; exact hay)
  obtain ⟨n, m, hnm, hqn⟩ :=
    exists_pow_two_power_lift (proj x) g' (k := k) (by rw [hg'a]; exact hk)
  have hmem : proj x (g' ^ n) ∈ Lb := by rw [hqn, hg'a]; exact ha
  have hcent : ((g' ^ n : ↥C) : G) ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg Subtype.val ((Commute.pow_left (show Commute g' u from hg'u) n).eq)
    exact this
  have hP : ((g' ^ n : ↥C) : G) ∈
      ((Lb.comap (proj x)).map C.subtype) ⊓ centralizer ({y} : Set G) :=
    ⟨⟨g' ^ n, hmem, rfl⟩, hcent⟩
  have hpow : ((g' ^ n : ↥C) : G) ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hnm
    simpa using this
  refine ⟨((g' ^ n : ↥C) : G), (g' ^ n).2, ?_, ?_, m, hpow⟩
  · have h2 : (⟨_, hP⟩ :
        ↥(((Lb.comap (proj x)).map C.subtype) ⊓ centralizer ({y} : Set G))) ∈
        oPrimeResidual 2 ↥(((Lb.comap (proj x)).map C.subtype) ⊓ centralizer ({y} : Set G)) :=
      Subgroup.subset_closure ⟨m, Subtype.ext hpow⟩
    exact ⟨⟨_, hP⟩, h2, rfl⟩
  · rw [hqn, hg'a]

theorem stage2QSNS_of_allow (hS : SourceExists) (hA : AdmissibleExists) (hAll : Stage2Allow) :
    Stage2QSNS := by
  intro G _ _ hyp noAlt x K hcirc hshape
  obtain ⟨A, hsrc⟩ := hS G hyp noAlt x K hcirc hshape
  obtain ⟨y, Lb, hadm⟩ := hA G hyp noAlt x K hcirc A hsrc
  have hss : NbhdSemisimple x y Lb := hAll G hyp noAlt x K hcirc A hsrc y Lb hadm
  have hx2 : orderOf x = 2 := hcirc.1.1.1.1
  have hxC : K ≤ centralizer ({x} : Set G) := hcirc.1.1.1.2.2.1
  have hKc : IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set G))) := hcirc.1.1.1.2.2.2
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx2
    omega
  have hcomm : ⁅liftAt x y Lb, pPrimeCoreOf 2 (centralizer ({x} : Set G))⁆ = ⊥ :=
    hss x (Subgroup.subset_closure (Set.mem_insert _ _)) hx1
  have hyC : y ∈ centralizer ({x} : Set G) := hadm.sub.y_mem
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hadm.sub.y_ord, pow_two] at this
  obtain ⟨hLH, a, b, haL, hbL, ⟨ka, ha⟩, ⟨kb, hb⟩, hab⟩ :=
    exists_noncomm_two_elements_of_isQuasi2CompIn
      (H := centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) (Lb := Lb)
      (hadm.sub.rel.2.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  obtain ⟨g₁, hg₁C, hg₁L, hg₁a, m₁, hm₁⟩ :=
    exists_mem_liftAt_of_two_pow_eq_one hyC hy2 haL
      (Subgroup.mem_centralizer_singleton_iff.1 (hLH haL).1) ha
  obtain ⟨g₂, hg₂C, hg₂L, hg₂b, m₂, hm₂⟩ :=
    exists_mem_liftAt_of_two_pow_eq_one hyC hy2 hbL
      (Subgroup.mem_centralizer_singleton_iff.1 (hLH hbL).1) hb
  have hmemK : ∀ (g : G) (hgC : g ∈ centralizer ({x} : Set G)) (m : ℕ) (c : CentralizerBar x),
      g ^ (2 ^ m) = 1 → proj x ⟨g, hgC⟩ = c → c ∈ imgBar x K → g ∈ K := by
    intro g hgC m c hgm hgc hcK
    have hgm' : (⟨g, hgC⟩ : ↥(centralizer ({x} : Set G))) ^ (2 ^ m) = 1 :=
      Subtype.ext (by simpa using hgm)
    have := mem_of_two_pow_eq_one_of_map_mem hKc hgm' (by rw [← hgc] at hcK; exact hcK)
    exact Subgroup.mem_subgroupOf.1 this
  have hg₁K : g₁ ∈ K := hmemK g₁ hg₁C m₁ a hm₁ hg₁a (hLH haL).2
  have hg₂K : g₂ ∈ K := hmemK g₂ hg₂C m₂ b hm₂ hg₂b (hLH hbL).2
  have hcent : ∀ w ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)),
      (⟨g₁, hg₁C⟩ : ↥(centralizer ({x} : Set G))) * w = w * ⟨g₁, hg₁C⟩ := by
    intro w hw
    have hwO : (w : G) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := ⟨w, hw, rfl⟩
    have h1 : ⁅g₁, (w : G)⁆ ∈ ⁅liftAt x y Lb, pPrimeCoreOf 2 (centralizer ({x} : Set G))⁆ :=
      Subgroup.commutator_mem_commutator hg₁L hwO
    rw [hcomm, Subgroup.mem_bot] at h1
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hnc : QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨g₁, hg₁C⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨g₂, hg₂C⟩ ≠
      QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨g₂, hg₂C⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨g₁, hg₁C⟩ := by
    change proj x ⟨g₁, hg₁C⟩ * proj x ⟨g₂, hg₂C⟩ ≠ proj x ⟨g₂, hg₂C⟩ * proj x ⟨g₁, hg₁C⟩
    rw [hg₁a, hg₂b]
    exact hab
  have hq := (isQuasisimple_of_isPComponent_of_noncomm hKc
    (Subgroup.mem_subgroupOf.2 hg₁K) (Subgroup.mem_subgroupOf.2 hg₂K) hcent hnc).2
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hxC) hq

end CFSG.GH74.Generic.BProg
