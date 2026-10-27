module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Pair
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelJ
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abG2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Sylow
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OrdG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelLU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.GLS.Stage1.Main.BrPairAbs
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.Stage2.Local.PerfInner
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Back112Kfacts
public import CFSG.GH74.GLS.C3.Layer1.Back91
public import CFSG.GH74.GLS.C3.Layer1.Split
public import CFSG.GH74.GLS.C3.Layer1.Thm1FmemberF
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint

theorem card_le_of_surj_of_odd_kernel {P K R : Type} [Group P] [Finite P] [Group K] [Finite K]
    [Group R] (π : P →* K) (hπ : Function.Surjective π) (ρ : P →* R)
    (hρ : ∀ x ∈ ρ.ker, Odd (orderOf x)) :
    Nat.card K ≤ Nat.card ↥ρ.range * Nat.card ↥(pPrimeCore 2 K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup K := ρ.ker.map π
  have hZn : Z.Normal := Subgroup.Normal.map (MonoidHom.normal_ker ρ) π hπ
  have hZodd : ∀ y ∈ Z, Odd (orderOf y) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hρ x hx).of_dvd_nat (orderOf_map_dvd π x)
  have hZle : Z ≤ pPrimeCore 2 K :=
    GroupTheory.le_pPrimeCore_of_normal hZn
      (Nat.coprime_two_left.2 (odd_card_of_forall_odd Z hZodd))
  let ψ : P →* K ⧸ Z := (QuotientGroup.mk' Z).comp π
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective Z).comp hπ
  have hrange : Finite ↥ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  let Φ : ↥ρ.range → K ⧸ Z := fun r => ψ (Function.surjInv ρ.rangeRestrict_surjective r)
  have hΦ : Function.Surjective Φ := by
    intro κ
    obtain ⟨p, hp⟩ := hψ κ
    refine ⟨ρ.rangeRestrict p, ?_⟩
    set p' := Function.surjInv ρ.rangeRestrict_surjective (ρ.rangeRestrict p) with hp'
    have h1 : ρ.rangeRestrict p' = ρ.rangeRestrict p := Function.surjInv_eq _ _
    have h2 : ρ p' = ρ p := congrArg Subtype.val h1
    have h3 : p⁻¹ * p' ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
    have h4 : π (p⁻¹ * p') ∈ Z := ⟨_, h3, rfl⟩
    have h5 : ψ (p⁻¹ * p') = 1 := (QuotientGroup.eq_one_iff _).2 h4
    rw [map_mul, map_inv, inv_mul_eq_one] at h5
    show ψ p' = κ
    rw [← h5]
    exact hp
  calc Nat.card K = Nat.card (K ⧸ Z) * Nat.card ↥Z :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    _ ≤ Nat.card ↥ρ.range * Nat.card ↥(pPrimeCore 2 K) :=
        Nat.mul_le_mul (Nat.card_le_card_of_surjective Φ hΦ) (Subgroup.card_le_of_le hZle)

theorem perfect_le_oPrimePResidual (Q : Type) [Group Q] [Finite Q] {K : Subgroup Q}
    (hK : Group.IsPerfect ↥K) : K ≤ oPrimePResidual 2 Q := by
  have hKY : K ≤ oPrimeResidual 2 Q := Stage2.Final.LayerFD.perfect_le_oPrimeResidual hK
  have hK'perf : Group.IsPerfect ↥(K.subgroupOf (oPrimeResidual 2 Q)) := by
    have e : ↥(K.subgroupOf (oPrimeResidual 2 Q)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKY
    exact Group.IsPerfect.ofSurjective (G := ↥K) (G' := ↥(K.subgroupOf (oPrimeResidual 2 Q)))
      (f := e.symm.toMonoidHom) e.symm.surjective
  have h1 : K.subgroupOf (oPrimeResidual 2 Q) ≤ oResidual 2 ↥(oPrimeResidual 2 Q) :=
    Stage1.Main.perfect_le_oResidual _ hK'perf
  calc K = (K.subgroupOf (oPrimeResidual 2 Q)).map (oPrimeResidual 2 Q).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hKY).symm
    _ ≤ (oResidual 2 ↥(oPrimeResidual 2 Q)).map (oPrimeResidual 2 Q).subtype :=
        Subgroup.map_mono h1

theorem perfect_le_LC {G : Type} [Group G] [Finite G] (z : G) (hI : PerfInner z) {P : Subgroup G}
    (hP : P ≤ Cen z) (hperf : Group.IsPerfect ↥P) : P ≤ LC z :=
  perfect_le_LC_of z hI hP hperf

theorem card_perfect_le_of_one_class {G : Type} [Group G] [Finite G] {z : G} (hI : PerfInner z)
    (hz2 : orderOf z = 2)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    {H : Subgroup G} {y : HBar H} (hy : orderOf y = 2) {K : Subgroup (HBar H)}
    (hKp : Group.IsPerfect ↥K) (hKy : K ≤ centralizer ({y} : Set (HBar H))) :
    Nat.card ↥K ≤ Nat.card ↥(LBar z) * Nat.card ↥(pPrimeCore 2 ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ∀ w ∈ (mkH H).ker, Odd (orderOf w) := by
    intro w hw
    exact odd_orderOf_of_mem_pPrimeCore ((QuotientGroup.eq_one_iff w).1 hw)
  obtain ⟨yt, hyt2, hyty⟩ := exists_involution_lift (mkH H) hodd hy
    (by rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; trivial)
  have huH : (yt : G) ∈ H := yt.2
  have hu2 : orderOf (yt : G) = 2 := (Subgroup.orderOf_coe yt).trans hyt2
  have hcent := centralizer_mk_eq H hu2 huH
  have hyeq : mkH H ⟨(yt : G), huH⟩ = y := hyty
  rw [hyeq] at hcent
  set A : Subgroup ↥H := (Cen (yt : G)).subgroupOf H with hA
  let f : ↥A →* HBar H := (mkH H).comp A.subtype
  have hKf : K ≤ f.range := by
    intro k hk
    have hk' : k ∈ barIn H (Cen (yt : G)) := hcent ▸ hKy hk
    obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.1 hk'
    exact ⟨⟨a, ha⟩, hak⟩
  obtain ⟨P, hPK, hPP⟩ := exists_perfect_lift f (Subgroup.isPerfect_iff.mp hKp) hKf
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone (yt : G) z hu2 hz2)
  let κA : ↥A →* G := (MulAut.conj c).toMonoidHom.comp (H.subtype.comp A.subtype)
  have hκA : ∀ a : ↥A, κA a = c * ((a : ↥H) : G) * c⁻¹ := fun a => rfl
  have hκCen : ∀ a : ↥A, κA a ∈ Cen z := by
    intro a
    have ha : ((a : ↥H) : G) ∈ Cen (yt : G) := a.2
    rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
    rw [hκA, ← hc]
    calc c * ((a : ↥H) : G) * c⁻¹ * (c * (yt : G) * c⁻¹) = c * (((a : ↥H) : G) * (yt : G)) * c⁻¹ := by group
      _ = c * ((yt : G) * ((a : ↥H) : G)) * c⁻¹ := by rw [ha]
      _ = c * (yt : G) * c⁻¹ * (c * ((a : ↥H) : G) * c⁻¹) := by group
  have hκinj : Function.Injective κA := by
    intro a b hab
    have : ((a : ↥H) : G) = ((b : ↥H) : G) := by
      have h1 : c * ((a : ↥H) : G) * c⁻¹ = c * ((b : ↥H) : G) * c⁻¹ := hab
      simpa using h1
    exact Subtype.ext (Subtype.ext this)
  have hQperf : Group.IsPerfect ↥(P.map κA) := by
    refine Subgroup.isPerfect_iff.mpr ?_
    rw [← Subgroup.map_commutator, hPP]
  have hQle : P.map κA ≤ Cen z := by
    rintro _ ⟨a, -, rfl⟩
    exact hκCen a
  have hQL : P.map κA ≤ LC z := perfect_le_LC z hI hQle hQperf
  let κ₁ : ↥A →* ↥(Cen z) := κA.codRestrict (Cen z) hκCen
  let ρ : ↥P →* CentralizerBar z := ((toBar z).comp κ₁).comp P.subtype
  let π : ↥P →* ↥K := (f.comp P.subtype).codRestrict K (fun p => by
    rw [← hPK]
    exact ⟨p, p.2, rfl⟩)
  have hπ : Function.Surjective π := by
    intro k
    have hk : (k : HBar H) ∈ P.map f := by rw [hPK]; exact k.2
    obtain ⟨a, ha, hak⟩ := hk
    exact ⟨⟨a, ha⟩, Subtype.ext hak⟩
  have hκ₁inj : Function.Injective κ₁ := fun a b hab => hκinj (congrArg Subtype.val hab)
  have hρker : ∀ x ∈ ρ.ker, Odd (orderOf x) := by
    intro x hx
    have h1 : toBar z (κ₁ (P.subtype x)) = 1 := MonoidHom.mem_ker.1 hx
    have h2 : κ₁ (P.subtype x) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 h1
    have h3 := odd_orderOf_of_mem_pPrimeCore h2
    have h4 : orderOf (κ₁ (P.subtype x)) = orderOf x := by
      rw [orderOf_injective κ₁ hκ₁inj, orderOf_injective P.subtype (Subgroup.subtype_injective P)]
    rwa [h4] at h3
  have hρle : ρ.range ≤ LBar z := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_map.2 ⟨κ₁ (x : ↥A), ?_, rfl⟩
    exact hQL ⟨x, x.2, rfl⟩
  have key := card_le_of_surj_of_odd_kernel π hπ ρ hρker
  exact key.trans (Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hρle))

theorem quasisimple_image_bounds {Q X : Type} [Group Q] [Finite Q] [Group X]
    (hQ : CFSG.IsQuasisimple Q) (hZ : Nat.card ↥(center Q) = 2) (ψ : Q →* X) (hψ : ψ ≠ 1) :
    Nat.card Q ≤ 2 * Nat.card ↥ψ.range ∧ pPrimeCore 2 ↥ψ.range = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect Q := hQ.1
  have hker : ψ.ker ≤ center Q := by
    rcases LocalCores.quasisimple_normal_subgroups hQ (MonoidHom.normal_ker ψ) with h | h
    · exact absurd (MonoidHom.ext fun g => (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))) hψ
    · exact h
  have hfinR : Finite ↥ψ.range := Finite.of_surjective _ ψ.rangeRestrict_surjective
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h1
    have h2 : Nat.card ↥ψ.ker ≤ 2 := hZ ▸ Subgroup.card_le_of_le hker
    calc Nat.card Q = Nat.card ↥ψ.range * Nat.card ↥ψ.ker := h1
      _ ≤ Nat.card ↥ψ.range * 2 := Nat.mul_le_mul_left _ h2
      _ = 2 * Nat.card ↥ψ.range := mul_comm _ _
  ·
    set N : Subgroup ↥ψ.range := pPrimeCore 2 ↥ψ.range with hN
    have hNodd : Odd (Nat.card ↥N) :=
      odd_card_of_forall_odd N (fun y hy => odd_orderOf_of_mem_pPrimeCore hy)
    have hNn : (N.comap ψ.rangeRestrict).Normal := Subgroup.Normal.comap inferInstance _
    rcases LocalCores.quasisimple_normal_subgroups hQ hNn with htop | hcen
    · exfalso
      have hall : ∀ r : ↥ψ.range, r ∈ N := by
        intro r
        obtain ⟨g, rfl⟩ := ψ.rangeRestrict_surjective r
        have : g ∈ N.comap ψ.rangeRestrict := htop ▸ Subgroup.mem_top g
        exact this
      have hodd : Odd (Nat.card ↥ψ.range) := by
        have h1 := odd_card_of_forall_odd (⊤ : Subgroup ↥ψ.range)
          (fun r _ => odd_orderOf_of_mem_pPrimeCore (hall r))
        rwa [Subgroup.card_top] at h1
      have hsolv : Group.IsSolvable ↥ψ.range := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      have : Group.IsPerfect ↥ψ.range :=
        Group.IsPerfect.ofSurjective (G := Q) (G' := ↥ψ.range) (f := ψ.rangeRestrict)
          ψ.rangeRestrict_surjective
      have : Nontrivial ↥ψ.range := by
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        apply hψ
        ext g
        have := Subsingleton.elim (ψ.rangeRestrict g) 1
        exact congrArg Subtype.val this
      exact Group.IsPerfect.not_isSolvable ↥ψ.range hsolv
    · have hle : Nat.card ↥N ≤ Nat.card ↥(N.comap ψ.rangeRestrict) := by
        refine Nat.card_le_card_of_surjective
          (fun x : ↥(N.comap ψ.rangeRestrict) => (⟨ψ.rangeRestrict (x : Q), x.2⟩ : ↥N)) ?_
        intro n
        obtain ⟨g, hg⟩ := ψ.rangeRestrict_surjective (n : ↥ψ.range)
        exact ⟨⟨g, by show ψ.rangeRestrict g ∈ N; rw [hg]; exact n.2⟩, Subtype.ext hg⟩
      have h2 : Nat.card ↥(N.comap ψ.rangeRestrict) ≤ 2 := hZ ▸ Subgroup.card_le_of_le hcen
      have h3 : Nat.card ↥N = 1 := by
        have h4 : 0 < Nat.card ↥N := Nat.card_pos
        obtain ⟨m, hm⟩ := hNodd
        omega
      exact Subgroup.card_eq_one.1 h3

section Consumers

open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem isPerfect_of_simple_noncomm {K : Type*} [Group K] [IsSimpleGroup K]
    (hK : ∃ x y : K, x * y ≠ y * x) : Group.IsPerfect K := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hK
    apply hxy
    have hmem : ⁅x, y⁆ ∈ commutator K := by
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure (commutator_mem_commutatorSet x y)
    rw [h, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h

theorem false_of_big_simple_centralizer (hp : Stage1Pair G z S q L₁ L₂) (hz2 : orderOf z = 2)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    {H : Subgroup G} {y : HBar H} (hy : orderOf y = 2) {K : Subgroup (HBar H)}
    (hKs : IsSimpleGroup ↥K) (hKn : ∃ a b : ↥K, a * b ≠ b * a)
    (hKc : K ≤ centralizer ({y} : Set (HBar H)))
    (hbig : (q * (q ^ 2 - 1)) ^ 2 < 2 * Nat.card ↥K) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥K := isPerfect_of_simple_noncomm hKn
  have hcore : pPrimeCore 2 ↥K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥K) with h | h
    · exact h
    · exfalso
      have hodd : Odd (Nat.card ↥K) := by
        have h1 := odd_card_of_forall_odd (⊤ : Subgroup ↥K)
          (fun r _ => odd_orderOf_of_mem_pPrimeCore (h ▸ Subgroup.mem_top r))
        rwa [Subgroup.card_top] at h1
      have hsolv : Group.IsSolvable ↥K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      have : Nontrivial ↥K := by
        obtain ⟨a, b, hab⟩ := hKn
        exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
      exact Group.IsPerfect.not_isSolvable ↥K hsolv
  have hC := card_perfect_le_of_one_class (perfInner_of_pair hp) hz2 hone hy hperf hKc
  rw [hcore, Subgroup.card_bot, mul_one] at hC
  have h2 := two_mul_card_LBar hp.prod hp.sl₁ hp.sl₂
  omega

theorem false_of_sl2_centralizer (hp : Stage1Pair G z S q L₁ L₂) (hz2 : orderOf z = 2)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    {H : Subgroup G} {y : HBar H} (hy : orderOf y = 2) {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = q ^ 2) (ψ : SL(2, E) →* HBar H) (hψ : ψ ≠ 1)
    (hψc : ∀ g, ψ g * y = y * ψ g) : False := by
  classical
  obtain ⟨m, hm⟩ := hp.odd
  have hq5 : 5 ≤ q := by
    have := hp.gt3
    omega
  have hE4 : 4 ≤ Nat.card E := by
    rw [hE]
    nlinarith
  have hEodd : Odd (Nat.card E) := by
    rw [hE]
    exact (Nat.odd_iff.2 (by omega : q % 2 = 1)).pow
  have hchar : ringChar E ≠ 2 := CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hEodd
  have hQ : CFSG.IsQuasisimple SL(2, E) := GHInv.isQuasisimple_sl2 hE4
  have hZ : Nat.card ↥(center SL(2, E)) = 2 := CFSG.LieType.SteinbergBR.card_center_SL2_eq_two hchar
  obtain ⟨hbound, -⟩ := quasisimple_image_bounds hQ hZ ψ hψ
  have : Group.IsPerfect SL(2, E) := hQ.1
  have hKperf : Group.IsPerfect ↥ψ.range :=
    Group.IsPerfect.ofSurjective (G := SL(2, E)) (G' := ↥ψ.range) (f := ψ.rangeRestrict)
      ψ.rangeRestrict_surjective
  have hKc : ψ.range ≤ centralizer ({y} : Set (HBar H)) := by
    rintro _ ⟨g, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hψc g)
  have hC := card_perfect_le_of_one_class (perfInner_of_pair hp) hz2 hone hy hKperf hKc
  have hcore : pPrimeCore 2 ↥ψ.range = ⊥ := (quasisimple_image_bounds hQ hZ ψ hψ).2
  rw [hcore, Subgroup.card_bot, mul_one] at hC
  have h2 := two_mul_card_LBar hp.prod hp.sl₁ hp.sl₂
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two E, hE] at hbound
  obtain ⟨u, hu⟩ : ∃ u, q ^ 2 = u + 1 := ⟨q ^ 2 - 1, by have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hu1 : 1 ≤ u := by nlinarith
  have e1 : (q ^ 2) ^ 2 - 1 = u * (u + 2) := by
    rw [hu]
    have : (u + 1) ^ 2 = u * (u + 2) + 1 := by ring
    omega
  have e2 : (q * (q ^ 2 - 1)) ^ 2 = (u + 1) * (u * u) := by
    have : q ^ 2 - 1 = u := by omega
    rw [mul_pow, this, hu]
    ring
  rw [e1, hu] at hbound
  rw [e2] at h2
  nlinarith

end Consumers

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
