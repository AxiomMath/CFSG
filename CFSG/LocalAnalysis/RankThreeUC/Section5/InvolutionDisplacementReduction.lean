module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CommRankDef
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
import CFSG.LocalAnalysis.RankThreeUC.Section5.PNoncentralizingInvolutionDisplacement
import CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowLeCardDelta
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HBasic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicSubgroupCharacteristic
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.InvolutionDisplacementReduction

open CFSG.LocalAnalysis.RankThreeUC

theorem two_mul_card_le_finrank {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] {W : ι → Submodule K V} (hW : iSupIndep W) (f : ι → Fin 2 → V)
    (hf : ∀ i, LinearIndependent K (f i)) (hfW : ∀ i j, f i j ∈ W i) :
    2 * Fintype.card ι ≤ Module.finrank K V := by
  have hspan : ∀ i, Submodule.span K (Set.range (f i)) ≤ W i := fun i =>
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hfW i j)
  have hli : LinearIndependent K (fun ij : (Σ _ : ι, Fin 2) => f ij.1 ij.2) := by
    refine linearIndependent_iUnion_finite hf fun i t _ hit => ?_
    refine (hW.disjoint_biSup hit).mono (hspan i) (iSup₂_le fun k hk => (hspan k).trans ?_)
    exact le_iSup₂_of_le (f := fun j (_ : j ∈ t) => W j) k hk le_rfl
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hcard
  omega

theorem mem_fixedSubmodule_zpowers {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {g : G} {v : V} (h : ρ g v = v) :
    v ∈ fixedSubmodule ρ (Subgroup.zpowers g) := by
  rw [QuadraticSetConjugationTransport.mem_fixedSubmodule_iff]
  intro n hn
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hn)
  rw [map_pow, Module.End.pow_apply, Function.iterate_fixed h]

theorem finrank_le_two_mul_commRank {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V) {t c : G} (htc : t * c * t⁻¹ = c⁻¹)
    (hodd : Odd (orderOf c)) (hfix : ∀ v : V, ρ c v = v → v = 0) :
    Module.finrank (ZMod 2) V ≤ 2 * commRank ρ t := by
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨d, hd⟩ : ∃ d : G, d = c ^ (k + 1) := ⟨_, rfl⟩
  have hd2 : d * d = c := by
    rw [hd, ← pow_add, show k + 1 + (k + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have htd : t * d * t⁻¹ = d⁻¹ := by
    rw [hd, ← conj_pow, htc, inv_pow]
  have htd' : t * d⁻¹ * t⁻¹ = d := by
    calc t * d⁻¹ * t⁻¹ = (t * d * t⁻¹)⁻¹ := by group
      _ = d := by rw [htd, inv_inv]
  have hconj : d * t * d⁻¹ = c * t := by
    calc d * t * d⁻¹ = d * (t * d⁻¹ * t⁻¹) * t := by group
      _ = c * t := by rw [htd', hd2]
  have hrank : commRank ρ (c * t) = commRank ρ t := by
    rw [← hconj, commRank_conj]
  have hinf : LinearMap.ker (ρ t - 1) ⊓ LinearMap.ker (ρ (c * t) - 1) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv1 hv2
    apply hfix v
    calc ρ c v = ρ c (ρ t v) := by rw [hv1]
      _ = ρ (c * t) v := by rw [map_mul, Module.End.mul_apply]
      _ = v := hv2
  have h1 := LinearMap.finrank_range_add_finrank_ker (ρ t - 1)
  have h2 := LinearMap.finrank_range_add_finrank_ker (ρ (c * t) - 1)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (ρ t - 1)) (LinearMap.ker (ρ (c * t) - 1))
  rw [hinf, finrank_bot] at h3
  have h4 := Submodule.finrank_le (LinearMap.ker (ρ t - 1) ⊔ LinearMap.ker (ρ (c * t) - 1))
  unfold commRank at hrank ⊢
  omega

theorem exists_prime_commutator_ne_bot {G : Type*} [Group G] [Finite G] (hO2 : CFSG.pCore 2 G = ⊥) {t : G}
    (htF : ¬ ∀ x ∈ CFSG.fittingSubgroup G, t * x = x * t) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ⁅CFSG.Open.pCoreOf q (⊤ : Subgroup G), Subgroup.zpowers t⁆ ≠ ⊥ := by
  by_contra hno
  push Not at hno
  apply htF
  have hle : CFSG.fittingSubgroup G ≤ Subgroup.centralizer {t} := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun r => ?_
    have hr : r.1.1.Prime := Nat.prime_of_mem_primeFactors r.1.2
    haveI : Fact r.1.1.Prime := ⟨hr⟩
    by_cases hr2 : r.1.1 = 2
    · rw [hr2, hO2]
      exact bot_le
    · haveI := CFSG.LieType.BorelTits.pCore_normal (G := G) r.1.1
      have hsub : CFSG.pCore r.1.1 G ≤ CFSG.Open.pCoreOf r.1.1 (⊤ : Subgroup G) :=
        CFSG.LieType.BorelTits.le_pCoreOf _ le_top inferInstance (CFSG.LieType.BorelTits.pCore_isPGroup _)
      have h1 := hno _ hr hr2
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff, Subgroup.zpowers_le,
        Subgroup.mem_centralizer_iff] at h1
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h1 x (hsub hx)
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem exists_inverted_of_not_mem_alphaSet {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} (hfaith : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) {t : G} (ht : t * t = 1) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqα : q ∉ alphaSet G) (hOt : ⁅CFSG.Open.pCoreOf q (⊤ : Subgroup G), Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ c : G, t * c * t⁻¹ = c⁻¹ ∧ Odd (orderOf c) ∧ ∀ v : V, ρ c v = v → v = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hKn : (CFSG.Open.pCoreOf q (⊤ : Subgroup G)).Normal :=
    show ((CFSG.pCore q ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).Normal from inferInstance
  haveI hRn : (CFSG.Open.pCoreOf q (commutator G)).Normal :=
    show ((CFSG.pCore q ↥(commutator G)).map (commutator G).subtype).Normal from inferInstance
  have hKp : IsPGroup q (CFSG.Open.pCoreOf q (⊤ : Subgroup G)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup q ⊤
  obtain ⟨x, hxK, hxt⟩ : ∃ x ∈ CFSG.Open.pCoreOf q (⊤ : Subgroup G), x * t ≠ t * x := by
    by_contra h
    push Not at h
    apply hOt
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff, Subgroup.zpowers_le,
      Subgroup.mem_centralizer_iff]
    exact h
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = x * t * x⁻¹ * t⁻¹ := ⟨_, rfl⟩
  have hcK : c ∈ CFSG.Open.pCoreOf q (⊤ : Subgroup G) := by
    have h1 := hKn.conj_mem _ (Subgroup.inv_mem _ hxK) t
    have h2 := Subgroup.mul_mem _ hxK h1
    rw [hcdef, show x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) by group]
    exact h2
  have hcG : c ∈ commutator G := by
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top t)
    rw [commutatorElement_def, ← commutator_def] at h
    rw [hcdef]
    exact h
  have hcR : c ∈ CFSG.Open.pCoreOf q (commutator G) :=
    CFSG.LieType.BorelTits.le_pCoreOf q (N := CFSG.Open.pCoreOf q (⊤ : Subgroup G) ⊓ commutator G) inf_le_right
      inferInstance (hKp.to_le inf_le_left) (Subgroup.mem_inf.mpr ⟨hcK, hcG⟩)
  haveI hRcyc : IsCyclic ↥(CFSG.Open.pCoreOf q (commutator G)) := by
    refine CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H.isCyclic_of_pRank_le_one hq hq2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup q (commutator G)) ?_
    by_contra h
    push Not at h
    exact hqα ⟨hq, h⟩
  have hc1 : c ≠ 1 := by
    intro h
    apply hxt
    rw [hcdef, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h
  haveI : (Subgroup.zpowers c).Normal := by
    have h := CFSG.GorensteinWalter.normalizer_le_normalizer_of_le_cyclic hRcyc (Subgroup.zpowers_le.mpr hcR)
    rw [Subgroup.normalizer_eq_top] at h
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)
  have hfixc := CFSG.LinearAlgebra.CoprimeActions.IrreducibleNormalFixedSpace.fixedSpace_eq_bot ρ hfaith hirr
    (Subgroup.zpowers c) (by rwa [Ne, Subgroup.zpowers_eq_bot])
  refine ⟨c, ?_, ?_, fun v hv => ?_⟩
  · have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    calc t * c * t⁻¹ = t * x * t * x⁻¹ * (t * t)⁻¹ := by rw [hcdef]; group
      _ = t * x * t⁻¹ * x⁻¹ := by rw [ht, inv_one, mul_one, ht']
      _ = c⁻¹ := by rw [hcdef]; group
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hKp) ⟨c, hcK⟩
    rw [← Subgroup.orderOf_mk c hcK, hk]
    exact (hq.odd_of_ne_two hq2).pow
  · have hv' : v ∈ fixedSubmodule ρ (Subgroup.zpowers c) := mem_fixedSubmodule_zpowers ρ hv
    have hv0 : v ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← hfixc]
      exact hv'
    exact (Submodule.mem_bot _).mp hv0

end CFSG.LocalAnalysis.RankThreeUC.Section5.InvolutionDisplacementReduction

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem two_mul_card_Delta_le_finrank (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    2 * Nat.card ↥(Delta p P ρ) ≤ Module.finrank (ZMod 2) V := by
  classical
  haveI : FiniteDimensional (ZMod 2) V :=
    CFSG.LinearAlgebra.CoprimeActions.IrreducibleFiniteGroupFiniteDimensional.finiteDimensional_of_irreducible
      ρ hc.faithfulBinaryIrreducibleAction.irreducible
  haveI : Fintype ↥(Delta p P ρ) := Fintype.ofFinite _
  have hdec := isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hdec
  choose f hf hfW using fun E : ↥(Delta p P ρ) =>
    PNoncentralizingInvolutionDisplacement.exists_linearIndependent_pair hc E.2
  rw [Nat.card_eq_fintype_card]
  exact InvolutionDisplacementReduction.two_mul_card_le_finrank hdec.1 f hf hfW

theorem lt_commRank_of_not_mem_alphaSet (hc : BinaryActionRankCounterexample G p P T B e ρ) {t : G}
    (ht : orderOf t = 2) {q : ℕ} (hq : q.Prime) (hqα : q ∉ alphaSet G)
    (hOt : ⁅CFSG.Open.pCoreOf q (⊤ : Subgroup G), Subgroup.zpowers t⁆ ≠ ⊥) : e + 1 < commRank ρ t := by
  have hF := hc.faithfulBinaryIrreducibleAction
  haveI : FiniteDimensional (ZMod 2) V :=
    CFSG.LinearAlgebra.CoprimeActions.IrreducibleFiniteGroupFiniteDimensional.finiteDimensional_of_irreducible
      ρ hF.irreducible
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hq2 : q ≠ 2 := by
    rintro rfl
    apply hOt
    have hle : CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) ≤ CFSG.pCore 2 G :=
      CFSG.LieType.BorelTits.le_pCore 2
        (show ((CFSG.pCore 2 ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).Normal from inferInstance)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤)
    rw [pCore_eq_bot_of_faithful_irreducible 2 ρ hF.faithful hF.irreducible, le_bot_iff] at hle
    rw [hle, Subgroup.commutator_bot_left]
  obtain ⟨c, htc, hodd, hfix⟩ := InvolutionDisplacementReduction.exists_inverted_of_not_mem_alphaSet hF.faithful
    hF.irreducible htt hq hq2 hqα hOt
  have h1 := InvolutionDisplacementReduction.finrank_le_two_mul_commRank ρ htc hodd hfix
  have h2 := two_mul_card_Delta_le_finrank hc
  have h3 := lt_card_Delta hc
  omega

end CFSG.LocalAnalysis.RankThreeUC.Section5
