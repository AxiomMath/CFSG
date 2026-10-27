module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def
import CFSG.GH74.GLS.C3.Layer1.Th2IV26
import CFSG.GH74.Generic.BProg.B2.T1Basic
import CFSG.GH74.Generic.BProg.B2.Thm2Comp
import CFSG.GroupTheory.InvolutionFixedCentralSylow
import CFSG.GroupTheory.SubnormalJoin
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
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
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
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
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.GH74.Generic.BProg.B1.PilotS4
import CFSG.GH74.Generic.S3.LeavesFine
import CFSG.GH74.Generic.S3.Lem37

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

namespace T1Comp

open CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.ComponentClassification

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_of_isSubnormal {Kb L J : Subgroup X} (hKL : Kb ≤ L) (hLsub : L.IsSubnormal)
    (hmin : ∀ J : Subgroup X, Kb ≤ J → J ≤ L → J.IsSubnormal → J = L)
    (hKJ : Kb ≤ J) (hJ : J.IsSubnormal) : L ≤ J :=
  inf_eq_left.1 (hmin (L ⊓ J) (le_inf hKL hKJ) inf_le_left (hLsub.inf hJ))

theorem mem_normalizer_closure {Kb L : Subgroup X} {t : X} (hKt : ∀ k ∈ Kb, t * k = k * t)
    (hKL : Kb ≤ L) (hLsub : L.IsSubnormal)
    (hmin : ∀ J : Subgroup X, Kb ≤ J → J ≤ L → J.IsSubnormal → J = L) :
    t ∈ normalizer (L : Set X) := by
  set f : X →* X := (MulAut.conj t).toMonoidHom with hf
  have hLt : (L.map f).IsSubnormal := Subgroup.IsSubnormal.map (MulAut.conj t).surjective hLsub
  have hKLt : Kb ≤ L.map f := fun k hk =>
    ⟨k, hKL hk, by show t * k * t⁻¹ = k; rw [hKt k hk]; group⟩
  have hle : L ≤ L.map f := le_of_isSubnormal hKL hLsub hmin hKLt hLt
  have hcard : Nat.card (L.map f) = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have heq : L = L.map f := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm

omit [Finite X] in
theorem mem_normalizer_centralizer {L : Subgroup X} {t : X} (ht : t ∈ normalizer (L : Set X)) :
    t ∈ normalizer ((centralizer (L : Set X) : Subgroup X) : Set X) := by
  have key : ∀ {s : X}, s ∈ normalizer (L : Set X) → ∀ c ∈ centralizer (L : Set X),
      s * c * s⁻¹ ∈ centralizer (L : Set X) := by
    intro s hs c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro l hl
    have h1 : s⁻¹ * l * s ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hs) l).1 hl
      simpa using this
    have h2 := hc _ h1
    calc l * (s * c * s⁻¹) = s * ((s⁻¹ * l * s) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * l * s)) * s⁻¹ := by rw [h2]
      _ = s * c * s⁻¹ * l := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key ht c, fun hc => ?_⟩
  have := key (inv_mem ht) _ hc
  simpa [mul_assoc] using this

theorem exists_involution_comm {L : Subgroup X} {t : X} (ht : orderOf t = 2)
    (htL : t ∈ normalizer (L : Set X)) {b : X} (hb2 : orderOf b = 2) (hbL : ∀ l ∈ L, b * l = l * b) :
    ∃ a : X, orderOf a = 2 ∧ (∀ l ∈ L, a * l = l * a) ∧ a * t = t * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hPA : zpowers t ≤ normalizer ((centralizer (L : Set X) : Subgroup X) : Set X) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_centralizer htL
  have hbC : b ∈ centralizer (L : Set X) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => (hbL l hl).symm
  have hA : Even (Nat.card (centralizer (L : Set X))) := by
    rw [even_iff_two_dvd, ← hb2]
    exact Subgroup.orderOf_dvd_natCard _ hbC
  obtain ⟨a, haC, ha2, hat⟩ :=
    CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer hP hPA hA
  exact ⟨a, ha2, fun l hl => (Subgroup.mem_centralizer_iff.1 haC l hl).symm,
    (hat t (Subgroup.mem_zpowers t)).symm⟩

theorem isTwoComponent_of_isCompIn {t : X} {Kb : Subgroup X}
    (hKc : IsCompIn (centralizer ({t} : Set X)) Kb) :
    TwoComponents.IsTwoComponent (Kb.subgroupOf (centralizer ({t} : Set X))) :=
  (TwoThin.isPCompIn_two_iff.1 ⟨hKc.1, isPComponent_two_of_isComponent hKc.2⟩).2

theorem le_layer_of_isCompIn (hcore : pPrimeCore 2 X = ⊥) {t : X} (ht : orderOf t = 2)
    {Kb : Subgroup X} (hKc : IsCompIn (centralizer ({t} : Set X)) Kb) : Kb ≤ CFSG.layer X :=
  EvenCore.le_layer_of_isTwoComponent hcore ht hKc.1 (isTwoComponent_of_isCompIn hKc)

omit [Finite X] in
theorem eq_of_involution_centralizes {Kb L : Subgroup X} {b : X} (hKL : Kb ≤ L)
    (hLsub : L.IsSubnormal)
    (hmin : ∀ J : Subgroup X, Kb ≤ J → J ≤ L → J.IsSubnormal → J = L)
    (hbL : ∀ l ∈ L, b * l = l * b) (hcomp : IsCompIn (centralizer ({b} : Set X)) Kb) : L = Kb := by
  have hLC : L ≤ centralizer ({b} : Set X) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (hbL l hl).symm
  have hsubC : (Kb.subgroupOf (centralizer ({b} : Set X))).IsSubnormal := hcomp.2.2
  have hKsubL : (Kb.subgroupOf L).IsSubnormal := by
    have h1 := hsubC.comap (Subgroup.inclusion hLC)
    have heq : (Kb.subgroupOf (centralizer ({b} : Set X))).comap (Subgroup.inclusion hLC) =
        Kb.subgroupOf L := by
      ext l
      rfl
    rwa [heq] at h1
  have hKsub : Kb.IsSubnormal := Subgroup.IsSubnormal.trans hKL hKsubL hLsub
  exact (hmin Kb le_rfl hKL hKsub).symm

theorem component_le_of_noInv {L : Subgroup X} (hLsub : L.IsSubnormal)
    (hno : ∀ b : X, orderOf b = 2 → ¬ ∀ l ∈ L, b * l = l * b) {J : Subgroup X}
    (hJ : IsComponent J) : J ≤ L := by
  rcases CFSG.LocalCores.component_subnormal_subgroup hJ hLsub with h | h
  · exact h
  · exfalso
    obtain ⟨b, hbJ, hb2⟩ := EvenCore.exists_involution_of_isComponent hJ
    refine hno b hb2 fun l hl => ?_
    have := Subgroup.commutator_mem_commutator hbJ hl
    rw [h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this

theorem socle_of_noInv (hcore : pPrimeCore 2 X = ⊥) {L : Subgroup X} (hLsub : L.IsSubnormal)
    (hLlayer : L ≤ CFSG.layer X)
    (hno : ∀ b : X, orderOf b = 2 → ¬ ∀ l ∈ L, b * l = l * b) :
    CFSG.layer X = L ∧ generalizedFitting X = L ∧ center ↥L = ⊥ := by
  have hlayerL : CFSG.layer X = L :=
    le_antisymm (sSup_le fun J hJ => component_le_of_noInv hLsub hno hJ) hLlayer
  have hF : fittingSubgroup X = ⊥ := by
    by_contra hne
    have hFn : (fittingSubgroup X).Normal := inferInstance
    have hFp : IsPGroup 2 ↥(fittingSubgroup X) :=
      isPGroup_of_nilpotent_normal (fittingSubgroup X) hFn inferInstance hcore
    obtain ⟨b, hbF, hb2⟩ := Th2.exists_involution_mem hFp hne
    have hcomm : ⁅fittingSubgroup X, CFSG.layer X⁆ = ⊥ := CFSG.LocalCores.fitting_layer_commute
    refine hno b hb2 fun l hl => ?_
    have h1 := Subgroup.commutator_mem_commutator hbF (hlayerL ▸ hl : l ∈ CFSG.layer X)
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hFstar : generalizedFitting X = L := by
    rw [generalizedFitting, hF, hlayerL, bot_sup_eq]
  have hLn : L.Normal := by
    rw [← hlayerL]
    have := CFSG.LocalCores.layer_characteristic (G := X)
    infer_instance
  have hZ : center ↥L = ⊥ := by
    have hnormal : ((center ↥L).map L.subtype).Normal := inferInstance
    have : Group.IsNilpotent ↥((center ↥L).map L.subtype) :=
      Group.nilpotent_of_mulEquiv ((center ↥L).equivMapOfInjective L.subtype L.subtype_injective)
    have hle : (center ↥L).map L.subtype ≤ fittingSubgroup X := le_sSup ⟨hnormal, inferInstance⟩
    rw [hF, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hle
  exact ⟨hlayerL, hFstar, hZ⟩

omit [Finite X] in
theorem isSimpleGroup_of_center_eq_bot {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    (hZ : center Q = ⊥) : IsSimpleGroup Q := by
  have hs : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  let e : Q ≃* (Q ⧸ center Q) :=
    (QuotientGroup.quotientBot (G := Q)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact e.isSimpleGroup

omit [Finite X] in
theorem eq_of_isComponent_le {J Λ : Subgroup X} (hJ : IsComponent J) (hΛ : IsComponent Λ)
    (h : J ≤ Λ) : J = Λ := by
  have hsub : (J.subgroupOf Λ).IsSubnormal := hJ.2.subgroupOf
  rcases quasisimple_subnormal_subgroups hΛ.1 hsub with h1 | h1
  · exact le_antisymm h (Subgroup.subgroupOf_eq_top.1 h1)
  · exfalso
    have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1.1
    have hbot : ⁅J, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k1 hk1
      rw [Subgroup.mem_centralizer_iff]
      intro k2 hk2
      have := Subgroup.mem_center_iff.mp
        (h1 (show (⟨k1, h hk1⟩ : ↥Λ) ∈ J.subgroupOf Λ from hk1)) ⟨k2, h hk2⟩
      exact congrArg Subtype.val this
    exact ne_bot_of_isComponent hJ (by rw [← hJperf, hbot])

omit [Finite X] in
theorem center_eq_bot_of_factor {L L₁ L₂ : Subgroup X} (hL : L = L₁ ⊔ L₂) (hZ : center ↥L = ⊥)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) : center ↥L₁ = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz1 : (z : X) ∈ L := hL ▸ Subgroup.mem_sup_left z.2
  have hle : L₁ ⊔ L₂ ≤ centralizer ({(z : X)} : Set X) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨a, ha⟩)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm z z.2 b hb).symm
  have hzL : (⟨z, hz1⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : (g : X) ∈ centralizer ({(z : X)} : Set X) := hle (hL ▸ g.2)
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hg)
  rw [hZ, Subgroup.mem_bot] at hzL
  have h3 := congrArg Subtype.val hzL
  exact Subtype.ext (by simpa using h3)

theorem trichotomy (hcore : pPrimeCore 2 X = ⊥) {t : X} (ht : orderOf t = 2) {Kb L : Subgroup X}
    (hKc : IsCompIn (centralizer ({t} : Set X)) Kb) (hKL : Kb ≤ L) (hLsub : L.IsSubnormal)
    (hmin : ∀ J : Subgroup X, Kb ≤ J → J ≤ L → J.IsSubnormal → J = L)
    (hTT : ∀ b : X, orderOf b = 2 → (∀ l ∈ L, b * l = l * b) → b * t = t * b →
      IsCompIn (centralizer ({b} : Set X)) Kb) :
    L = Kb ∨ (generalizedFitting X = L ∧ IsSimpleGroup ↥L) ∨
      (generalizedFitting X = L ∧ ∃ L₁ L₂ : Subgroup X, IsComponent L₁ ∧ IsComponent L₂ ∧ L₁ ≠ L₂ ∧
        IsSimpleGroup ↥L₁ ∧ IsSimpleGroup ↥L₂ ∧ L = L₁ ⊔ L₂ ∧
        L₁.map (MulAut.conj t).toMonoidHom = L₂ ∧
        ∀ J : Subgroup X, IsComponent J → J = L₁ ∨ J = L₂) := by
  have hKt : ∀ k ∈ Kb, t * k = k * t := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKc.1 hk)).symm
  have htL : t ∈ normalizer (L : Set X) := mem_normalizer_closure hKt hKL hLsub hmin
  by_cases hb : ∃ b : X, orderOf b = 2 ∧ (∀ l ∈ L, b * l = l * b) ∧ b * t = t * b
  · obtain ⟨b, hb2, hbL, hbt⟩ := hb
    exact Or.inl (eq_of_involution_centralizes hKL hLsub hmin hbL (hTT b hb2 hbL hbt))
  · right
    have hno : ∀ b : X, orderOf b = 2 → ¬ ∀ l ∈ L, b * l = l * b := fun b hb2 hbL =>
      hb (exists_involution_comm ht htL hb2 hbL)
    have hKlayer : Kb ≤ CFSG.layer X := le_layer_of_isCompIn hcore ht hKc
    have hlayerN : (CFSG.layer X).Normal := by
      have := CFSG.LocalCores.layer_characteristic (G := X)
      infer_instance
    have hLlayer : L ≤ CFSG.layer X :=
      le_of_isSubnormal hKL hLsub hmin hKlayer hlayerN.isSubnormal
    obtain ⟨-, hFstar, hZ⟩ := socle_of_noInv hcore hLsub hLlayer hno
    obtain ⟨Λ, hΛ, hcase⟩ := TwoThin.exists_component_orbit_location ht hKc.1
      (isTwoComponent_of_isCompIn hKc) hKlayer
    rcases hcase with ⟨-, hKΛ⟩ | ⟨hΛt, hAB, hKD⟩
    ·
      have hΛL : Λ ≤ L := component_le_of_noInv hLsub hno hΛ
      have hLΛ : L ≤ Λ := le_of_isSubnormal hKL hLsub hmin hKΛ hΛ.2
      have hLe : L = Λ := le_antisymm hLΛ hΛL
      refine Or.inl ⟨hFstar, ?_⟩
      rw [hLe] at hZ ⊢
      exact isSimpleGroup_of_center_eq_bot hΛ.1 hZ
    ·
      have ht' : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
      set L₂ : Subgroup X := conjSub t⁻¹ Λ with hL₂
      have hL₂c : IsComponent L₂ := isComponent_conjSub hΛ t⁻¹
      have hL₁L : Λ ≤ L := component_le_of_noInv hLsub hno hΛ
      have hL₂L : L₂ ≤ L := component_le_of_noInv hLsub hno hL₂c
      have hKsup : Kb ≤ Λ ⊔ L₂ := fun k hk => by
        obtain ⟨a, rfl⟩ := hKD hk
        exact swapDiag_mem_sup hAB a
      have hLsup : L = Λ ⊔ L₂ :=
        le_antisymm
          (le_of_isSubnormal hKL hLsub hmin hKsup
            (CFSG.GroupTheory.isSubnormal_sup hΛ.2 hL₂c.2))
          (sup_le hL₁L hL₂L)
      have hcomm12 : ∀ a ∈ Λ, ∀ b ∈ L₂, a * b = b * a := fun a ha b hb =>
        commute_of_commutator_conj_eq_bot hAB ha hb
      have hZ1 : center ↥Λ = ⊥ := center_eq_bot_of_factor hLsup hZ hcomm12
      have hZ2 : center ↥L₂ = ⊥ :=
        center_eq_bot_of_factor (sup_comm Λ L₂ ▸ hLsup) hZ
          (fun a ha b hb => (hcomm12 b hb a ha).symm)
      refine Or.inr ⟨hFstar, Λ, L₂, hΛ, hL₂c, fun h => hΛt h.symm,
        isSimpleGroup_of_center_eq_bot hΛ.1 hZ1, isSimpleGroup_of_center_eq_bot hL₂c.1 hZ2,
        hLsup, ?_, ?_⟩
      · show Λ.map (MulAut.conj t).toMonoidHom = Λ.map (MulAut.conj t⁻¹).toMonoidHom
        rw [ht']
      · intro J hJ
        have hJL : J ≤ L := component_le_of_noInv hLsub hno hJ
        by_cases h1 : J ≤ Λ
        · exact Or.inl (eq_of_isComponent_le hJ hΛ h1)
        · by_cases h2 : J ≤ L₂
          · exact Or.inr (eq_of_isComponent_le hJ hL₂c h2)
          · exfalso
            have c1 : ⁅J, Λ⁆ = ⊥ :=
              (CFSG.LocalCores.component_subnormal_subgroup hJ hΛ.2).resolve_left h1
            have c2 : ⁅J, L₂⁆ = ⊥ :=
              (CFSG.LocalCores.component_subnormal_subgroup hJ hL₂c.2).resolve_left h2
            rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at c1 c2
            apply ne_bot_of_isComponent hJ
            rw [eq_bot_iff]
            intro j hj
            rw [Subgroup.mem_bot]
            have hjL : j ∈ L := hJL hj
            have hjΛ : ∀ a ∈ Λ, a * j = j * a := fun a ha =>
              Subgroup.mem_centralizer_iff.1 (c1 hj) a ha
            have hjL₂ : ∀ b ∈ L₂, b * j = j * b := fun b hb =>
              Subgroup.mem_centralizer_iff.1 (c2 hj) b hb
            have hle : Λ ⊔ L₂ ≤ centralizer ({j} : Set X) := sup_le
              (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hjΛ a ha))
              (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hjL₂ b hb))
            have hjc : (⟨j, hjL⟩ : ↥L) ∈ center ↥L := by
              rw [Subgroup.mem_center_iff]
              intro g
              have hg : (g : X) ∈ centralizer ({j} : Set X) := hle (hLsup ▸ g.2)
              exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hg)
            rw [hZ, Subgroup.mem_bot] at hjc
            have h3 := congrArg Subtype.val hjc
            simpa using h3

end T1Comp

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

theorem barIn_K_isCompIn_gen (hB : B_B2_g4) (hyp : Hyp2 G) (hMtop : M ≠ ⊤) (hILo : IsILo 2 x K)
    (hKM : K ≤ M) (hxM : x ∈ M) :
    IsCompIn (centralizer ({(QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M)} : Set (Mbar M)))
      (barIn M K) := by
  have hKP : IsKProperSimple G := isKProperSimple_of_kgh hyp.simple hyp.nonab hyp.kgh
  have hMb : IsKGroupNative (Mbar M) := Th2.P85.isKGroupNative_Mb hKP hMtop
  have hcore : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hx2 : orderOf x = 2 := hILo.1
  have hxo : orderOf (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) = 2 :=
    TwoThin.orderOf_barMk ((Subgroup.orderOf_mk x hxM).trans hx2)
  have hB' := Th2.IV26.isComponent_of_B2 hB (Th2.IV26.gen4_Mb hyp.gen4 M) hMb hcore hxo
  exact Th2.IV26.isCompIn_imgM_at_x hxM hx2 hKM hILo.2.2 hB'

theorem barIn_K_isCompIn (hB : B_B2_g4) (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) (hxM : x ∈ M) :
    IsCompIn (centralizer ({(QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M)} : Set (Mbar M)))
      (barIn M K) :=
  barIn_K_isCompIn_gen hB hs.hyp hs.maxM.1 hs.pair.1.1.1 hKM hxM

open CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.IV26 CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.Th2.HY in
theorem barIn_K_isCompIn_at (hB : B_B2_g4) (hyp : Hyp2 G) (hMtop : M ≠ ⊤) (hILo : IsILo 2 x K)
    (hterm : IsTwoTerminal x K) (hKM : K ≤ M)
    (hKq : IsQuasisimple ↥(barIn M K)) {e : G} (heC : e ∈ CxK x K) (he2 : orderOf e = 2)
    (heM : e ∈ M)
    (hecent : (QuotientGroup.mk (⟨e, heM⟩ : ↥M) : Mbar M) ∈
      centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M))) :
    IsCompIn (centralizer ({(QuotientGroup.mk (⟨e, heM⟩ : ↥M) : Mbar M)} : Set (Mbar M)))
      (barIn M K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKP : IsKProperSimple G := isKProperSimple_of_kgh hyp.simple hyp.nonab hyp.kgh
  have hMb : IsKGroupNative (Mbar M) := Th2.P85.isKGroupNative_Mb hKP hMtop
  have hcore : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hBe : ∀ J : Subgroup ↥(centralizer ({eb M heM} : Set (Mb M))), IsPComponent 2 J →
      IsComponent J :=
    Th2.IV26.isComponent_of_B2 hB (Th2.IV26.gen4_Mb hyp.gen4 M) hMb hcore
      (TwoThin.orderOf_barMk ((Subgroup.orderOf_mk e heM).trans he2))
  have hcomp : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hR3 : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := by
    have h3 : 3 ≤ pRank 2 G := by
      rw [pRank_two_eq_twoRank]
      exact hyp.rank
    exact fun y hy => TwoThin.rankThreeCentralizers G hyp.simple hyp.nonab h3 y hy
  obtain ⟨Λ, hΛ⟩ := exists_isLam he2 hcomp heC.2
  obtain ⟨M₁, hlt⟩ := C3.Layer1.PumpRigid.exists_pumpUpLT hILo he2 heC (hR3 e he2)
  obtain ⟨hxM₁, ⟨e₁⟩⟩ := hterm.2.1 e M₁ hlt
  have hM₁c : IsPCompIn 2 (centralizer ({e} : Set G)) M₁ := hlt.2.1.2.2
  have hΛM₁ : PumpCalc.bar e Λ ≤ PumpCalc.bar e M₁ := bar_le_of_stable hlt hΛ hxM₁
  have hΛeq : PumpCalc.bar e Λ = PumpCalc.bar e M₁ := bar_lam_eq hΛ hM₁c hΛM₁ e₁
  have hcomp' : IsComponent (PumpCalc.bar e Λ) := hΛeq ▸ isComponent_bar hM₁c
  have hΛK : Λ ≤ K := hΛ.le.trans inf_le_left
  have hΛC : Λ ≤ centralizer ({e} : Set G) := hΛ.le.trans inf_le_right
  set W : Subgroup ↥(centralizer ({e} : Set G)) :=
    (PumpCalc.bar e Λ).comap (barMk ↥(centralizer ({e} : Set G))) with hW
  have hWsub : W.IsSubnormal := hcomp'.2.comap _
  have hWmem : ∀ (g : G) (hg : g ∈ centralizer ({e} : Set G)),
      (⟨g, hg⟩ : ↥(centralizer ({e} : Set G))) ∈ W ↔
        ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({e} : Set G)), g = l * o := by
    intro g hg
    rw [hW, Subgroup.mem_comap]
    show sbar g hg ∈ PumpCalc.bar e Λ ↔ _
    rw [sbar_mem_bar_iff hg hΛC]
    exact mem_sup_iff_mul_of_le_normalizer (le_normalizer_O hΛC)
  set D : Subgroup (Mb M) := centralizer ({eb M heM} : Set (Mb M)) with hD
  set Oe : Subgroup G := pPrimeCoreOf 2 (centralizer ({e} : Set G)) with hOe
  obtain ⟨Z, hZsub, hZmem⟩ := exists_subnormal_transport heM he2 hWsub
  have hKbD : imgM M K ≤ D := by
    intro k hk
    rw [hD, mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hecent k hk
  have hΛb : imgM M Λ = imgM M K := imgM_eq_of_cover hKM hΛK hΛ.cover hKq
  have hOeC : Oe ≤ centralizer ({e} : Set G) := TwoThin.pPrimeCoreOf_le _
  have hObD : imgM M Oe ≤ D := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hw
    rw [hD, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hOeC hm))
  set K' : Subgroup ↥D := (imgM M K).subgroupOf D with hK'
  set R' : Subgroup ↥D := (imgM M Oe).subgroupOf D with hR'
  have hK'Z : K' ≤ Z := by
    intro d hd
    have hd' : (d : Mb M) ∈ imgM M K := hd
    rw [← hΛb] at hd'
    obtain ⟨l, hl, hld⟩ := mem_imgM_iff.1 hd'
    exact (hZmem d).2 ⟨(l : G), hΛC hl, l.2,
      (hWmem _ _).2 ⟨l, hl, 1, Subgroup.one_mem _, (mul_one _).symm⟩, hld⟩
  have hZKR : ∀ z ∈ Z, ∃ k ∈ K', ∃ r ∈ R', z = k * r := by
    intro z hz
    obtain ⟨g, hg, hgM, hgW, hzd⟩ := (hZmem z).1 hz
    obtain ⟨l, hl, o, ho, hgeq⟩ := (hWmem g hg).1 hgW
    have hlM : l ∈ M := hKM (hΛK hl)
    have hoM : o ∈ M := by
      have : o = l⁻¹ * g := by rw [hgeq]; group
      rw [this]
      exact M.mul_mem (M.inv_mem hlM) hgM
    have hlb : barMk ↥M ⟨l, hlM⟩ ∈ imgM M K := mem_imgM_iff.2 ⟨⟨l, hlM⟩, hΛK hl, rfl⟩
    have hob : barMk ↥M ⟨o, hoM⟩ ∈ imgM M Oe := mem_imgM_iff.2 ⟨⟨o, hoM⟩, ho, rfl⟩
    refine ⟨⟨barMk ↥M ⟨l, hlM⟩, hKbD hlb⟩, hlb, ⟨barMk ↥M ⟨o, hoM⟩, hObD hob⟩, hob, ?_⟩
    apply Subtype.ext
    rw [← hzd]
    have : (⟨g, hgM⟩ : ↥M) = ⟨l, hlM⟩ * ⟨o, hoM⟩ := Subtype.ext hgeq
    rw [this, map_mul]
    rfl
  have hso : orderOf (⟨e, heM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk e heM).trans he2
  have hRnorm : R'.Normal := by
    refine ⟨fun r hr d => ?_⟩
    rw [hR', Subgroup.mem_subgroupOf] at hr ⊢
    obtain ⟨o, hoO, hor⟩ := mem_imgM_iff.1 hr
    obtain ⟨c, hcd⟩ := barMkCentralizer_surjective hso d
    have hcG : ((c : ↥M) : G) ∈ centralizer ({e} : Set G) := by
      have h := c.2
      rw [mem_centralizer_singleton_iff] at h ⊢
      exact congrArg Subtype.val h
    have hcdv : (d : Mb M) = barMk ↥M (c : ↥M) := by
      rw [← hcd]
      exact barMkCentralizer_apply hso c
    have hmem : ((c : ↥M) * o * (c : ↥M)⁻¹ : ↥M).1 ∈ Oe := by
      have := TwoThin.pPrimeCoreOf_normalized (centralizer ({e} : Set G)) hcG hoO
      simpa using this
    refine mem_imgM_iff.2 ⟨(c : ↥M) * o * (c : ↥M)⁻¹, hmem, ?_⟩
    show barMk ↥M ((c : ↥M) * o * (c : ↥M)⁻¹) = (d : Mb M) * (r : Mb M) * (d : Mb M)⁻¹
    rw [map_mul, map_mul, map_inv, hor, hcdv]
  have hRodd : Odd (Nat.card R') := by
    rw [hR', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hObD).toEquiv]
    have h1 : Nat.card (imgM M Oe) ∣ Nat.card (Oe.subgroupOf M) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (Oe.subgroupOf M) ∣ Nat.card Oe := by
      have h3 : Nat.card (Oe.subgroupOf M) = Nat.card ((Oe.subgroupOf M).map M.subtype) :=
        (Subgroup.card_map_of_injective M.subtype_injective).symm
      rw [h3]
      exact Subgroup.card_dvd_of_le (by rintro _ ⟨m, hm, rfl⟩; exact hm)
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _) (h1.trans h2)
  have hR : R' ≤ pPrimeCore 2 ↥D := le_sSup ⟨hRnorm, Nat.coprime_two_left.2 hRodd⟩
  have hKperf : ⁅K, K⁆ = K :=
    commutator_self_of_isTwoComponent (isPCompIn_two_iff.1 hcomp).1 (isPCompIn_two_iff.1 hcomp).2
  have hK'perf : ⁅K', K'⁆ = K' := by
    have h1 : Group.IsPerfect ↥(imgM M K) :=
      Subgroup.isPerfect_iff.mpr (isPerfect_imgM hKM hKperf)
    have h2 : Group.IsPerfect ↥K' :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKbD).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKbD).symm.surjective
    exact Subgroup.isPerfect_iff.mp h2
  have hK'q : IsQuasisimple ↥K' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKbD).symm hKq
  have hKq' := isQuasisimple_map_of_isQuasisimple hK'q
  have hcompK' : IsComponent K' := isComponent_of_sandwich hBe hK'perf hZsub hK'Z hR hZKR hKq'
  exact ⟨hKbD, hcompK'⟩

namespace T1Comp

theorem exists_lift {x : G} {M : Subgroup G} (hxM : x ∈ M) (hx2 : orderOf x = 2) {b : Mbar M}
    (hb2 : orderOf b = 2) (hbt : b * (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) =
      (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) * b) :
    ∃ (g : G) (hg : g ∈ M), orderOf g = 2 ∧ g ∈ centralizer ({x} : Set G) ∧
      (QuotientGroup.mk (⟨g, hg⟩ : ↥M) : Mbar M) = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hso : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hx2
  have hbC : b ∈ centralizer ({TwoThin.barMk ↥M ⟨x, hxM⟩} : Set (Mbar M)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hbt
  have hb' : b ∈ (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)).map (TwoThin.barMk ↥M) := by
    rw [TwoThin.map_centralizer_barMk hso]
    exact hbC
  obtain ⟨c0, hc0, hcb⟩ := hb'
  have hb2sq : b ^ 2 = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb2] at this
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb2
    omega
  have hsq : c0 ^ 2 ∈ pPrimeCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff (c0 ^ 2)]
    show TwoThin.barMk ↥M (c0 ^ 2) = 1
    rw [map_pow, hcb, hb2sq]
  have hodd : Odd (orderOf (c0 ^ 2)) := by
    have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥M) hsq
    exact Odd.of_dvd_nat (TwoThin.odd_card_pPrimeCore ↥M) (by simpa using hdvd)
  set m := orderOf (c0 ^ 2) with hm
  have hg2 : (c0 ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hm, pow_orderOf_eq_one]
  have hgb : TwoThin.barMk ↥M (c0 ^ m) = b := by
    rw [map_pow, hcb]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, hb2sq, one_pow, one_mul]
  have hg1 : c0 ^ m ≠ 1 := by
    intro h
    rw [h, map_one] at hgb
    exact hb1 hgb.symm
  have hgo : orderOf (c0 ^ m) = 2 := orderOf_eq_prime hg2 hg1
  have hgc : c0 ^ m ∈ centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) :=
    Subgroup.pow_mem _ hc0 m
  refine ⟨((c0 ^ m : ↥M) : G), (c0 ^ m).2, ?_, ?_, hgb⟩
  · rw [Subgroup.orderOf_coe]
    exact hgo
  · rw [Subgroup.mem_centralizer_singleton_iff] at hgc ⊢
    exact congrArg Subtype.val hgc

end T1Comp

theorem lemma119_gen (hB : B_B2_g4) (hyp : Hyp2 G) (hMtop : M ≠ ⊤) (hILo : IsILo 2 x K)
    (hterm : IsTwoTerminal x K) (hKM : K ≤ M) (hxM : x ∈ M)
    {H : Subgroup G} (hH : IsMinSubnormalIn K M H) : HTri x K M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := hILo.1
  have ht2 : orderOf (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) = 2 :=
    TwoThin.orderOf_barMk ((Subgroup.orderOf_mk x hxM).trans hx2)
  have hcore : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hKc := barIn_K_isCompIn_gen hB hyp hMtop hILo hKM hxM
  have hKq : IsQuasisimple ↥(barIn M K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKc.1) hKc.2.1
  have hKL : barIn M K ≤ barIn M H := Th2.P85.imgM_mono hH.1
  have hLsub : (barIn M H).IsSubnormal := Th2.P85.isSubnormal_imgM hH.2.1
  have hmin : ∀ J : Subgroup (Mbar M), barIn M K ≤ J → J ≤ barIn M H → J.IsSubnormal →
      J = barIn M H := fun J hKJ hJL hJ => Th2.P85.imgM_min hH hKJ hJL hJ
  have hTT : ∀ b : Mbar M, orderOf b = 2 → (∀ l ∈ barIn M H, b * l = l * b) →
      b * (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) =
        (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) * b →
      IsCompIn (centralizer ({b} : Set (Mbar M))) (barIn M K) := by
    intro b hb2 hbL hbt
    obtain ⟨g, hgM, hg2, hgx, hgb⟩ := T1Comp.exists_lift hxM hx2 hb2 hbt
    have hecent : (QuotientGroup.mk (⟨g, hgM⟩ : ↥M) : Mbar M) ∈
        centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)) := by
      rw [hgb]
      exact Subgroup.mem_centralizer_iff.2 fun k hk => (hbL k (hKL hk)).symm
    have hcomm : ∀ l ∈ K, ⁅l, g⁆ ∈ pPrimeCoreOf 2 M := by
      intro l hl
      have hlM : l ∈ M := hKM hl
      refine (Thm2Comp.comm_mem_pPrimeCoreOf_iff (⟨l, hlM⟩ : ↥M) ⟨g, hgM⟩).2 ?_
      refine commutatorElement_eq_one_iff_mul_comm.2 ?_
      have hlb : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨l, hlM⟩ ∈ barIn M H :=
        hKL ⟨⟨l, hlM⟩, hl, rfl⟩
      have := hbL _ hlb
      show (QuotientGroup.mk ⟨l, hlM⟩ : Mbar M) * QuotientGroup.mk ⟨g, hgM⟩ =
        QuotientGroup.mk ⟨g, hgM⟩ * QuotientGroup.mk ⟨l, hlM⟩
      rw [hgb]
      exact this.symm
    have hCxK : g ∈ CxK x K := Thm2Comp.mem_CxK_of_comm_mem_O hILo.2.2 hgx hKM rfl hcomm
    have h := barIn_K_isCompIn_at hB hyp hMtop hILo hterm hKM hKq hCxK hg2 hgM hecent
    rwa [hgb] at h
  rcases T1Comp.trichotomy hcore ht2 hKc hKL hLsub hmin hTT with
    h | ⟨hF, hS⟩ | ⟨hF, L₁, L₂, h₁, h₂, hne, hs₁, hs₂, hsup, hconj, hall⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hF.symm, hS⟩)
  · exact Or.inr (Or.inr ⟨hF.symm, hxM, L₁, L₂, h₁, h₂, hne, hs₁, hs₂, hsup, hconj, hall⟩)

theorem lemma119 (hB : B_B2_g4) (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) (hQM : Q ≤ M)
    {H : Subgroup G} (hH : IsMinSubnormalIn K M H) : HTri x K M H :=
  lemma119_gen hB hs.hyp hs.maxM.1 hs.pair.1.1.1 hs.pair.1.2.2 hKM (hQM (x_mem_Q hs)) hH

end CFSG.GH74.Generic.BProg.B2
