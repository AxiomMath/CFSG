module

public import CFSG.GH74.GLS.Stage2.Local.P34NS12J
public import CFSG.GH74.GLS.Stage2.Local.P34NS12M12
public import CFSG.GH74.GLS.Stage2.Local.P34NS12Stmt
public import CFSG.GH74.GLS.Stage2.Local.P34S5Frat
public import CFSG.GH74.GLS.Stage2.Local.Ctx0
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Red
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Sylow
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93KindM12
public import CFSG.GH74.GLS.TwoThin.Basic
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
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.LU.Local.A3Reduce2
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.Stage2.Local.P34S5Clo
public import CFSG.GH74.GLS.Stage2.Local.P34S5SE
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.LargeEvenClassification.Delta
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalCoreIntersection
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.NonSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Remaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.WalterRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.TheoremC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt CFSG.GH74.GLS.Stage2.Local.P34NS CFSG.Blueprint
open scoped commutatorElement

section Aux

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidualOf_conj_mem (N : Subgroup G) {n : G} (hn : n ∈ N) {r : G}
    (hr : r ∈ oPrimeResidualOf 2 N) : n * r * n⁻¹ ∈ oPrimeResidualOf 2 N := by
  obtain ⟨r', hr', rfl⟩ := hr
  refine ⟨⟨n, hn⟩ * r' * ⟨n, hn⟩⁻¹, ?_, by simp⟩
  induction hr' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := hy
    refine Subgroup.subset_closure ⟨k, ?_⟩
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  | one => simp
  | mul y w _ _ hy hw =>
    have e : (⟨n, hn⟩ : ↥N) * (y * w) * (⟨n, hn⟩ : ↥N)⁻¹ =
        ((⟨n, hn⟩ : ↥N) * y * (⟨n, hn⟩ : ↥N)⁻¹) * ((⟨n, hn⟩ : ↥N) * w * (⟨n, hn⟩ : ↥N)⁻¹) := by group
    rw [e]
    exact mul_mem hy hw
  | inv y _ hy =>
    have e : (⟨n, hn⟩ : ↥N) * y⁻¹ * (⟨n, hn⟩ : ↥N)⁻¹ = ((⟨n, hn⟩ : ↥N) * y * (⟨n, hn⟩ : ↥N)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hy

omit [Finite G] in
theorem not_solvable_of_perfect {X P : Subgroup G} (hPX : P ≤ X) (hperf : ⁅P, P⁆ = P) (hne : P ≠ ⊥) :
    ¬ Group.IsSolvable ↥X := by
  intro hX
  have hP : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPX)
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥P
  have htop : commutator ↥P = ⊤ := (Subgroup.isPerfect_iff.2 hperf).commutator_eq_top
  rw [htop] at hlt
  exact lt_irrefl _ hlt

theorem exists_perfect_cent (hK : Ivk93KindM12) (hM : M12Facts) {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.m12 S) {H : Subgroup G} (hne : H ≠ ⊤) (hCH : Cen z ≤ H)
    (hV : pCore 2 (HBar H) = ⊥) (hs : IsSimpleGroup ↥(generalizedFitting (HBar H)))
    (hnab : ∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) (hPerf : PerfInJ H)
    (h2 : HasTwoInvolutionClasses (HBar H)) {x : G} (hxC : x ∈ Cen z) (hxnc : IsNonCentralInvolution x) :
    ∃ P : Subgroup G, P ≤ centralizer ({x} : Set G) ⊓ H ∧ ⁅P, P⁆ = P ∧ P ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, hMf⟩ := hM
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hzH : z ∈ H := hCH (mem_Cen_self z)
  have hxH : x ∈ H := hCH hxC
  have hx2 : orderOf x = 2 := hxnc.1
  have hzH2 : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by
    rw [← hz2]; exact (Subgroup.orderOf_coe (⟨z, hzH⟩ : ↥H)).symm
  have hxH2 : orderOf (⟨x, hxH⟩ : ↥H) = 2 := by
    rw [← hx2]; exact (Subgroup.orderOf_coe (⟨x, hxH⟩ : ↥H)).symm
  obtain ⟨-, ⟨eJ0⟩⟩ := hK G z S hctx H hne hCH hV hs hnab hPerf h2
  set J : Subgroup (HBar H) := generalizedFitting (HBar H) with hJ
  let eJ : ↥J ≃* ↥NativeSporadic.M12 := eJ0
  have hJnorm : J.Normal := LocalCores.generalized_fitting_characteristic.2
  have hJcard : Nat.card ↥J = 95040 := by
    rw [Nat.card_congr eJ.toEquiv]; exact hcard
  obtain ⟨T, hT⟩ := exists_sylow_barIn hctx hCH
  have hTc64 : Nat.card ↥(T : Subgroup (HBar H)) = 64 := by
    rw [hT, card_barIn_S hctx hCH, card_S_m12 hctx]
  have hTJ : (T : Subgroup (HBar H)) ≤ J := by
    obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal T (N := J)
    have hQc : Nat.card ↥(Q : Subgroup ↥J) = 64 := by
      rw [Sylow.card_eq_multiplicity Q, hJcard, factorization_95040]; norm_num
    have hinf : Nat.card ↥((T : Subgroup (HBar H)) ⊓ J) = 64 := by
      rw [hQ] at hQc
      rw [← hQc]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : (T : Subgroup (HBar H)) ⊓ J ≤ J)).toEquiv).symm
    have heq : (T : Subgroup (HBar H)) ⊓ J = T :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hinf, hTc64])
    rw [← heq]
    exact inf_le_right
  set zb : HBar H := mkH H ⟨z, hzH⟩ with hzb
  set xb : HBar H := mkH H ⟨x, hxH⟩ with hxb
  have hzb2 : orderOf zb = 2 := orderOf_mk_eq_two H hzH2
  have hxb2 : orderOf xb = 2 := orderOf_mk_eq_two H hxH2
  have hzJ : zb ∈ J := hTJ (by rw [hT]; exact zbar_mem_barIn hctx hCH)
  have hxJ : xb ∈ J := by
    have hpx : IsPGroup 2 (zpowers xb) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxb2]; norm_num)
    obtain ⟨Q, hQ⟩ := hpx.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (HBar H) T Q
    have hxQ : xb ∈ (Q : Subgroup (HBar H)) := hQ (Subgroup.mem_zpowers xb)
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    have h1 : g⁻¹ * xb * g ∈ (T : Subgroup (HBar H)) := by simpa using hxQ
    have h2' : g⁻¹ * xb * g ∈ J := hTJ h1
    have := hJnorm.conj_mem _ h2' g
    simpa [mul_assoc] using this
  let ζ : ↥J := ⟨zb, hzJ⟩
  let ξ : ↥J := ⟨xb, hxJ⟩
  have hζ2 : orderOf ζ = 2 := by rw [← Subgroup.orderOf_coe]; exact hzb2
  have hξ2 : orderOf ξ = 2 := by rw [← Subgroup.orderOf_coe]; exact hxb2
  have h64 : 64 ∣ Nat.card ↥(centralizer ({ζ} : Set ↥J)) := by
    have hT'le : (T : Subgroup (HBar H)).subgroupOf J ≤ centralizer ({ζ} : Set ↥J) := by
      intro t ht
      rw [Subgroup.mem_subgroupOf] at ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact zbar_comm_barIn hctx hCH (hT ▸ ht)
    have := Subgroup.card_dvd_of_le hT'le
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv, hTc64] at this
  have h64' : 64 ∣ Nat.card ↥(centralizer ({eJ ζ} : Set NativeSporadic.M12)) := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.M12Cover.centralizerEquiv eJ ζ).toEquiv]
    exact h64
  have hnc : ¬ IsConj (eJ ζ) (eJ ξ) := by
    intro hc
    rw [CFSG.ComponentClassification.M12Cover.isConj_iff_of_mulEquiv] at hc
    have hc1 : IsConj zb xb := by
      have := J.subtype.map_isConj hc
      simpa using this
    have hc2 : IsConj (⟨z, hzH⟩ : ↥H) ⟨x, hxH⟩ := isConj_of_mk_isConj H hzH2 hxH2 hc1
    have hc3 : IsConj z x := by
      have := H.subtype.map_isConj hc2
      simpa using this
    exact hxnc.2 (isCentralInvolution_of_isConj_P34 hctx.central hc3)
  obtain ⟨P, hPc, hPp, hPn⟩ := hMf (eJ ζ) (eJ ξ) (by rw [MulEquiv.orderOf_eq]; exact hζ2)
    (by rw [MulEquiv.orderOf_eq]; exact hξ2) h64' hnc
  set PJ : Subgroup ↥J := P.map eJ.symm.toMonoidHom with hPJ
  have hPJc : PJ ≤ centralizer ({ξ} : Set ↥J) := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hPc hg)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' := congrArg eJ.symm h1
    simpa using h'
  have hPJp : ⁅PJ, PJ⁆ = PJ := by rw [hPJ, ← Subgroup.map_commutator, hPp]
  have hPJn : PJ ≠ ⊥ := fun h =>
    hPn ((Subgroup.map_eq_bot_iff_of_injective _ eJ.symm.injective).1 h)
  set PB : Subgroup (HBar H) := PJ.map J.subtype with hPB
  have hPBp : ⁅PB, PB⁆ = PB := by rw [hPB, ← Subgroup.map_commutator, hPJp]
  have hPBn : PB ≠ ⊥ := fun h => hPJn ((Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 h)
  have hPBc : PB ≤ centralizer ({xb} : Set (HBar H)) := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hPJc hg)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h1
  have hbar : centralizer ({xb} : Set (HBar H)) = barIn H (Cen x) := centralizer_mk_eq H hx2 hxH
  let A : Subgroup ↥H := (centralizer ({x} : Set G)).subgroupOf H
  let φ : ↥A →* HBar H := (mkH H).comp A.subtype
  have hle : PB ≤ φ.range := by
    intro g hg
    have hg' : g ∈ barIn H (Cen x) := hbar ▸ hPBc hg
    obtain ⟨a, ha, rfl⟩ := hg'
    exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨P₁, hP₁p, hP₁m⟩ := P34NS.exists_perfect_lift φ hPBp hle
  have hP₁n : P₁ ≠ ⊥ := by
    intro h
    apply hPBn
    rw [← hP₁m, h, Subgroup.map_bot]
  refine ⟨(P₁.map A.subtype).map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a.2, (a : ↥H).2⟩
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hP₁p]
  · intro h
    apply hP₁n
    have h1 := (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 h
    exact (Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective).1 h1

omit [Finite G] in
theorem isSolvable_closure_pair {x y : G} (hxy : x * y = y * x) :
    Group.IsSolvable ↥(Subgroup.closure ({x, y} : Set G)) := by
  have hc : IsMulCommutative ↥(Subgroup.closure ({x, y} : Set G)) :=
    Subgroup.isMulCommutative_closure (by
      intro a ha b hb hne
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hne
      · rw [Set.mem_singleton_iff] at hb
        subst hb
        exact hxy
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hxy.symm
      · rw [Set.mem_singleton_iff] at ha hb
        subst ha hb
        exact absurd rfl hne)
  infer_instance

end Aux

theorem nsm12H_of (hK : Ivk93KindM12) (hM : M12Facts) : NSm12H := by
  intro G _ _ z S hctx H hne hCH hV hs hnab hPerf h2 x hxC hxnc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPle, hPperf, hPne⟩ :=
    exists_perfect_cent hK hM hctx hne hCH hV hs hnab hPerf h2 hxC hxnc
  have hPN : P ≤ centralizer ({x} : Set G) := hPle.trans inf_le_left
  have hPH : P ≤ H := hPle.trans inf_le_right
  obtain ⟨K, y, q, hKc, -, -, hyC, -, -, -, hRO, -⟩ :=
    hctx.detail.m12 rfl x hxnc.1
      (fun hc => hxnc.2 (isCentralInvolution_of_isConj_P34 hctx.central hc))
  have hKJ : K ≤ Jx x := le_sSup hKc
  have hxC' : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  let T : Subgroup G := Subgroup.closure {x, y}
  have hxT : x ∈ T := Subgroup.subset_closure (Set.mem_insert x {y})
  have hyT : y ∈ T := Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))
  have hTN : T ≤ centralizer ({x} : Set G) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxC', Set.singleton_subset_iff.2 hyC⟩)
  have hTsol : Group.IsSolvable ↥T := isSolvable_closure_pair hxy
  have hf : oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T := by
    rw [hRO]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left)
      ((Subgroup.zpowers_le.2 hxT).trans le_sup_right))
      (sup_le (hKJ.trans (le_sup_right.trans le_sup_left))
        ((Subgroup.zpowers_le.2 hyT).trans le_sup_right))
  have hPJ : P ≤ Jx x :=
    perfect_le_of_structure (N := centralizer ({x} : Set G)) (Jx_le_centralizer x)
      (TwoThin.pPrimeCoreOf_le _) (Subgroup.map_subtype_le _) (Jx_normalized x)
      (fun n hn o ho => TwoThin.pPrimeCoreOf_normalized _ hn ho)
      (fun n hn r hr => oPrimeResidualOf_conj_mem _ hn hr)
      (TwoThin.card_pPrimeCoreOf_odd _) hTsol hTN not_two_dvd_relIndex_oPrimeResidual_sup hf hPN
      hPperf
  exact not_solvable_of_perfect (le_inf hPJ hPH) hPperf hPne

end CFSG.GH74.GLS.Stage2.Local.P34
