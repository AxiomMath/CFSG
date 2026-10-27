module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.OddOrder.ChiefFactorFaithfulLinearImage
public import CFSG.FeitThompson.OddOrder.DerivedPGroupInvariantAlternatingForm
import CFSG.FeitThompson.OddOrder.PrimeDimNoInvariantAlternatingForm
import CFSG.FeitThompson.Representations.TypeThreeFourChiefKernelDerived
import CFSG.FeitThompson.Representations.TypeThreeFourChiefKernelCentralized
import CFSG.FeitThompson.Local.CoreCentralizerTypeIIIOrIVDerived
import CFSG.FeitThompson.Representations.TypeThreeFourCorePrimeGroup
import CFSG.FeitThompson.OddOrder.PConfigChiefFactorLinearModel
import CFSG.FeitThompson.Local.TypeIIHallCoreElementaryAbelian
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson Prep06

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep05
open CFSG.FeitThompson.ChiefFactorFaithfulImage
open CFSG.FeitThompson.ChiefFactorLinearAction
open scoped commutatorElement

universe u

theorem prep06_hallCoreIn_eq_hallCoreOf {G : Type*} [Group G] (M : Subgroup G) :
    (Prep06.hallCoreIn M : Subgroup G) = hallCoreOf M := (rfl)

theorem isMulCommutative_quotient_of_commutator_le' {X : Type*} [Group X] {C : Subgroup X}
    (hC : C.Normal) (hle : _root_.commutator X ≤ C) :
    letI := hC
    IsMulCommutative (X ⧸ C) := by
  let _ := hC
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.2 hle

theorem factorLinearImage_eq_map {L : Type*} [Group L] {Hm H₀ D : Subgroup L}
    [Hm.Normal] [H₀.Normal] (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (e : (↥Hm ⧸ H₀.subgroupOf Hm) ≃* Multiplicative V) :
    factorLinearImage p Hm H₀ D e = D.map (factorLinearAut p Hm H₀ e) := by
  ext f
  rw [mem_factorLinearImage, Subgroup.mem_map]

noncomputable def factorAbelianizationMulEquiv {L : Type*} [Group L] {Hm H₀ : Subgroup L}
    [Hm.Normal] [H₀.Normal] (h : H₀.subgroupOf Hm = _root_.commutator ↥Hm) :
    (↥Hm ⧸ H₀.subgroupOf Hm) ≃* Multiplicative (Additive (Abelianization ↥Hm)) :=
  (QuotientGroup.quotientMulEquivOfEq h).trans
    (MulEquiv.multiplicativeAdditive (Abelianization ↥Hm)).symm

theorem factorAbelianizationMulEquiv_mk {L : Type*} [Group L] {Hm H₀ : Subgroup L}
    [H₀.Normal] [Hm.Normal] (h : H₀.subgroupOf Hm = _root_.commutator ↥Hm) (x : ↥Hm) :
    Multiplicative.toAdd (factorAbelianizationMulEquiv h (QuotientGroup.mk x))
      = Additive.ofMul (Abelianization.of x) := (rfl)

theorem factorLinearAut_eq_abelianizationLinearAut {L : Type*} [Group L] {Hm H₀ E : Subgroup L}
    [Hm.Normal] [H₀.Normal] (hEN : E ≤ normalizer (Hm : Set L)) (p : ℕ)
    [Module (ZMod p) (Additive (Abelianization ↥Hm))]
    (h : H₀.subgroupOf Hm = _root_.commutator ↥Hm) (u : ↥E) :
    factorLinearAut p Hm H₀ (factorAbelianizationMulEquiv h) (u : L)
      = abelianizationLinearAut p (conjOnNormalized Hm hEN) u := by
  refine LinearEquiv.toLinearMap_injective (LinearMap.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := exists_ofMul_abelianizationOf v
  have h1 := factorLinearAut_apply p (factorAbelianizationMulEquiv h) (u : L)
    (QuotientGroup.mk x)
  rw [factorAbelianizationMulEquiv_mk] at h1
  change (factorLinearAut p Hm H₀ (factorAbelianizationMulEquiv h)) (u : L)
      (Additive.ofMul (Abelianization.of x))
    = (abelianizationLinearAut p (conjOnNormalized Hm hEN)) u
      (Additive.ofMul (Abelianization.of x))
  rw [h1, abelianizationLinearAut_ofMul_of, factorConjAut_mk, factorAbelianizationMulEquiv_mk]
  refine congrArg Additive.ofMul (congrArg Abelianization.of (Subtype.ext ?_))
  rw [conjOnNormalized_apply_coe, MulAut.conjNormal_apply]

theorem eq_zero_of_isFaithfulImageSetup {L : Type*} [Group L] [Finite L] [Group.IsSolvable L]
    {Hm A Um B H₀ : Subgroup L} {b : L} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [Hm.Normal] [H₀.Normal] (hs : IsFaithfulImageSetup Hm A Um B H₀ b q)
    [Module (ZMod p) (Additive (Abelianization ↥Hm))]
    (hmod : H₀.subgroupOf Hm = _root_.commutator ↥Hm)
    (hUnorm : Um ≤ normalizer (Hm : Set L)) (hqodd : Odd q) (hUodd : Odd (Nat.card ↥Um))
    {β : Additive (Abelianization ↥Hm) →ₗ[ZMod p]
      Additive (Abelianization ↥Hm) →ₗ[ZMod p] ZMod p}
    (hβalt : β.IsAlt)
    (hβinv : ∀ u : ↥Um, ∀ v w, β (abelianizationLinearAut p (conjOnNormalized Hm hUnorm) u v)
      (abelianizationLinearAut p (conjOnNormalized Hm hUnorm) u w) = β v w) :
    β = 0 := by
  have hp : p.Prime := Fact.out
  set e := factorAbelianizationMulEquiv (Hm := Hm) (H₀ := H₀) hmod with he
  set D := factorLinearImage p Hm H₀ Um e with hDdef
  have hinvD : ∀ d ∈ D, ∀ v w, β (d v) (d w) = β v w := by
    intro d hd v w
    rw [hDdef, mem_factorLinearImage] at hd
    obtain ⟨g, hg, rfl⟩ := hd
    have h := hβinv ⟨g, hg⟩ v w
    rw [← factorLinearAut_eq_abelianizationLinearAut hUnorm p hmod ⟨g, hg⟩] at h
    exact h
  have hAodd : Odd (Nat.card ↥D) := by
    refine hUodd.of_dvd_nat ?_
    rw [hDdef, factorLinearImage_eq_map]
    exact Subgroup.card_map_dvd Um _
  refine bilinForm_eq_zero_of_odd_of_isAlt_of_invariant (q := q) (p := p) (D := D)
    (Ne.symm (hs.ne_q p e hp)) hqodd (hs.finrank_eq p e hp)
    (hs.factorLinearImage_U_ne_bot p e hp) (hs.isMulCommutative_factorLinearImage_U p e)
    hAodd (hs.orderOf_factorLinearAut_b p e hp) (hs.mem_normalizer_factorLinearImage p e)
    ?_ ?_ ?_ (fun v => hβalt v) hinvD
  · intro W hW
    have h := (isIrreducible_linearGroupRep_iff.1
      (hs.isIrreducible_factorLinearImage_A p e)).2 W
    rw [hs.factorLinearImage_A_eq p e] at h
    exact h hW
  · intro d hd hcomm
    have h : d ∈ D ⊓ centralizer ({factorLinearAut p Hm H₀ e b} : Set _) :=
      Subgroup.mem_inf.2 ⟨hd, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
    rw [hDdef, hs.inf_centralizer_eq_bot p e, Subgroup.mem_bot] at h
    exact h
  · rw [← invariants_zpowers_eq_eqLocus]
    exact hs.finrank_invariants p e

theorem commutator_eq_bot_of_isFaithfulImageSetup {L : Type*} [Group L] [Finite L]
    [Group.IsSolvable L] {Hm A Um B H₀ : Subgroup L} {b : L} {p q a : ℕ}
    [Hm.Normal] [H₀.Normal] (hs : IsFaithfulImageSetup Hm A Um B H₀ b q)
    (hp : p.Prime) (hq : q.Prime) (hqodd : Odd q) (ha1 : 1 ≤ a)
    (hcard : Nat.card ↥Hm = p ^ a) (hUnorm : Um ≤ normalizer (Hm : Set L))
    (hmod : H₀.subgroupOf Hm = _root_.commutator ↥Hm)
    (hfix : ∀ u : ↥Um, ∀ t ∈ _root_.commutator ↥Hm, conjOnNormalized Hm hUnorm u t = t)
    (hUodd : Odd (Nat.card ↥Um))
    (hexp : ∀ y : Additive (Abelianization ↥Hm), p • y = 0) :
    _root_.commutator ↥Hm = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have inst : Module (ZMod p) (Additive (Abelianization ↥Hm)) := AddCommGroup.zmodModule hexp
  by_contra hne
  obtain ⟨β, hβne, hβalt, hβinv⟩ :=
    exists_ne_zero_isAlt_invariant_bilinForm_of_commutator_ne_bot (p := p) (a := a)
      hp ha1 hcard hne (conjOnNormalized Hm hUnorm) hfix
  exact hβne (eq_zero_of_isFaithfulImageSetup hs hmod hUnorm hqodd hUodd hβalt hβinv)

theorem commutator_hallCoreOf_eq_bot {G : Type u} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hfitting : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (hprime : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    ⁅hallCoreOf M, hallCoreOf M⁆ = ⊥ := by
  have : Fintype G := Fintype.ofFinite G
  have hG6 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hpprime, hqprime, -, hqodd, -, hUne, -, -, -, -, -, -, -, -,
      ⟨H₀, hH₀CU, hlayer⟩, hall⟩ :=
    FPF_type_iii_iv_chief_data hprime G hG M U W₁ W₂ hM htype hc _ _ rfl rfl
  obtain ⟨⟨-, -, hpow, -⟩, -⟩ := hall H₀ hH₀CU hlayer
  have hH₀eq : H₀ = ⁅hallCoreOf M, hallCoreOf M⁆ :=
    FPF_type_iii_iv_chief_kernel_is_derived hfitting hprime G hG M U W₁ W₂ hM htype hc
      H₀ hH₀CU hlayer
  have hUH₀ : ⁅U, H₀⁆ = ⊥ :=
    FPF_type_iii_iv_chief_kernel_centralized hprime G hG M U W₁ W₂ hM htype hc H₀ hH₀CU hlayer
  obtain ⟨a, ha1, hacard⟩ :=
    FPF_type_iii_iv_core_is_prime_group hfitting hprime G hG6 M U W₁ W₂ hM htype hc
  rw [Prep06.hallCoreIn_eq, ← hallCoreOf_eq] at hacard
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hHle : hallCoreOf M ≤ M := hallCoreOf_le M
  have hUleM : U ≤ M := hc.le_M_E
  have hHsub : (hallCoreOf M).subgroupOf M = hallCore ↥M := by
    rw [hallCoreOf_eq]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hcardHm : Nat.card ↥(hallCore ↥M) = Nat.card ↥W₂ ^ a := by
    rw [← hHsub, natCard_subgroupOf hHle, hacard]
  have hH₀m : H₀.subgroupOf M = ⁅hallCore ↥M, hallCore ↥M⁆ := by
    rw [hH₀eq, ← hHsub, commutator_subgroupOf hHle hHle]
  have hH₀mm : (H₀.subgroupOf M).subgroupOf (hallCore ↥M)
      = _root_.commutator ↥(hallCore ↥M) := by
    rw [hH₀m, ← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (hallCore ↥M).subtype_injective]
  have hmemHm : ∀ x : ↥(hallCore ↥M), ((x : ↥M) : G) ∈ hallCoreOf M := fun x => by
    rw [hallCoreOf_eq]; exact ⟨(x : ↥M), x.2, rfl⟩
  have hpowm : ∀ x : ↥(hallCore ↥M), x ^ Nat.card ↥W₂ ∈ _root_.commutator ↥(hallCore ↥M) := by
    intro x
    rw [← hH₀mm]
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ?_)
    have h := hpow _ (hmemHm x)
    simpa [SubmonoidClass.coe_pow] using h
  have hzero : ∀ y : Additive (Abelianization ↥(hallCore ↥M)), Nat.card ↥W₂ • y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := exists_ofMul_abelianizationOf y
    change Additive.ofMul ((Abelianization.of x) ^ Nat.card ↥W₂) = 0
    rw [← map_pow,
      show Abelianization.of (x ^ Nat.card ↥W₂) = 1 from by
        rw [← MonoidHom.mem_ker, Abelianization.ker_of]; exact hpowm x]
    rfl
  have hUnorm : U.subgroupOf M ≤ normalizer ((hallCore ↥M : Subgroup ↥M) : Set ↥M) :=
    le_normalizer_of_normal
  have hfix : ∀ u : ↥(U.subgroupOf M), ∀ t ∈ _root_.commutator ↥(hallCore ↥M),
      conjOnNormalized (hallCore ↥M) hUnorm u t = t := by
    intro u t ht
    refine Subtype.ext (Subtype.ext ?_)
    rw [conjOnNormalized_apply_coe]
    have htG : ((t : ↥M) : G) ∈ H₀ := by
      rw [← hH₀mm] at ht
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 ht)
    have huG : ((u : ↥M) : G) ∈ U := Subgroup.mem_subgroupOf.1 u.2
    have h := Subgroup.commutator_mem_commutator huG htG
    rw [hUH₀, Subgroup.mem_bot, commutatorElement_def] at h
    have h2 : ((u : ↥M) : G) * ((t : ↥M) : G) * ((u : ↥M) : G)⁻¹ = ((t : ↥M) : G) := by
      have := mul_eq_one_iff_eq_inv.1 h
      simpa using this
    simpa using h2
  have hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ := natCard_subgroupOf hc.le_M_W₁
  have hcfg := hc.isPTypeConfig hsolvM hqprime hUne
  have hchief : IsChiefFactor (hallCore ↥M) (H₀.subgroupOf M) :=
    isChiefFactor_of_isChiefLayer hlayer
  have := hchief.normal_den
  have hCUm : hallCore ↥M ⊓ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M)
      ≤ H₀.subgroupOf M := by
    rw [centralizerIn_eq] at hH₀CU
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    rw [← hHsub, Subgroup.mem_subgroupOf] at hx1
    rw [← subgroupOf_centralizer M U hUleM, Subgroup.mem_subgroupOf] at hx2
    exact Subgroup.mem_subgroupOf.2 (hH₀CU (Subgroup.mem_inf.2 ⟨hx1, hx2⟩))
  obtain ⟨b, hbB, hb1, -⟩ := exists_zpowers_eq_of_prime_natCard
    (B := W₁.subgroupOf M) (hcard1 ▸ hqprime)
  have hs := hcfg.isFaithfulImageSetup hcard1 hchief hCUm hbB hb1
  have hUodd : Odd (Nat.card ↥(U.subgroupOf M)) := by
    rw [natCard_subgroupOf hUleM]
    exact hG.odd_natCard.of_dvd_nat (Subgroup.card_subgroup_dvd_card U)
  have hbot := commutator_eq_bot_of_isFaithfulImageSetup hs hpprime hqprime hqodd ha1
    hcardHm hUnorm hH₀mm hfix hUodd hzero
  have h1 : (⁅hallCore ↥M, hallCore ↥M⁆ : Subgroup ↥M) = ⊥ := by
    have h := congrArg (Subgroup.map (hallCore ↥M).subtype) hbot
    rwa [Subgroup.map_subtype_commutator, Subgroup.map_bot] at h
  have h2 := congrArg (Subgroup.map M.subtype) h1
  rwa [Subgroup.map_commutator, Subgroup.map_bot, ← hallCoreOf_eq] at h2

theorem FPF_type_iii_iv_core_elementary_chief_kernel_trivial
    (hfitting : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (hprime : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc
  rw [prep06_hallCoreIn_eq_hallCoreOf M]
  have hfin : Finite G := Finite.of_fintype G
  have hG5 : IsMinimalSimpleOdd G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  set p : ℕ := Nat.card ↥W₂ with hp
  set q : ℕ := Nat.card ↥W₁ with hq
  obtain ⟨hpprime, -, -, -, -, -, -, -, -, -, -, hCUlt, -, -, ⟨H₀, hH₀CU, hlayer⟩, hall⟩ :=
    FPF_type_iii_iv_chief_data hprime G hG5 M U W₁ W₂ hM htype hc p q rfl rfl
  obtain ⟨⟨-, -, hpow, hrel⟩, -⟩ := hall H₀ hH₀CU hlayer
  rw [centralizerIn_eq] at hCUlt hH₀CU
  have hHbot : ⁅hallCoreOf M, hallCoreOf M⁆ = ⊥ :=
    commutator_hallCoreOf_eq_bot hG5 hM htype hc hfitting hprime
  have hkernel : ∀ K : Subgroup G, hallCoreOf M ⊓ centralizer (U : Set G) ≤ K →
      IsChiefLayer M K (hallCoreOf M) → K = ⊥ := by
    intro K hKCU hKlayer
    rw [FPF_type_iii_iv_chief_kernel_is_derived hfitting hprime G hG5 M U W₁ W₂ hM htype hc
      K (by rw [centralizerIn_eq]; exact hKCU) hKlayer, hHbot]
  have hH₀bot : H₀ = ⊥ := hkernel H₀ hH₀CU hlayer
  have hcard : Nat.card ↥(hallCoreOf M) = p ^ q := by
    rw [← hrel, hH₀bot, Subgroup.relIndex_bot_left]
  have helem : IsElementaryAbelian p (hallCoreOf M) := by
    refine isElementaryAbelian_iff.2 ⟨commutator_self_eq_bot_iff.1 hHbot, fun x hx => ?_⟩
    have h := hpow x hx
    rw [hH₀bot, Subgroup.mem_bot] at h
    exact h
  have hCUeq : U ⊓ centralizer ((hallCoreOf M : Subgroup G) : Set G) = ⁅U, U⁆ := by
    have h := FPF_type_iii_iv_core_centralizer_derived hfitting G hG M U W₁ W₂ hM htype hc
    rwa [prep06_hallCoreIn_eq_hallCoreOf M] at h
  have hCsub : (U ⊓ centralizer ((hallCoreOf M : Subgroup G) : Set G)).subgroupOf U
      = _root_.commutator ↥U := by
    rw [hCUeq, ← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective U.subtype_injective]
  have hCnormal :
      ((U ⊓ centralizer ((hallCoreOf M : Subgroup G) : Set G)).subgroupOf U).Normal := by
    rw [hCsub]; infer_instance
  refine ⟨nonempty_mulEquiv_pi_of_isElementaryAbelian hpprime helem hcard, hcard, hHbot, ?_,
    ?_, hCUeq, hCnormal, ?_, ?_⟩
  ·
    exact le_antisymm (hH₀bot ▸ hH₀CU) bot_le
  ·
    intro K hKle hKnorm hKCU hKlt hKmax
    refine hkernel K hKCU ⟨hKnorm, hKlt, fun N hN hKN hNH => ?_⟩
    by_cases h1 : N = K
    · exact Or.inl h1
    by_cases h2 : N = hallCoreOf M
    · exact Or.inr h2
    · exact absurd ⟨lt_of_le_of_ne hKN (Ne.symm h1), lt_of_le_of_ne hNH h2⟩ (hKmax N hN)
  ·
    refine QuotientGroup.nontrivial_iff.2 fun htop => ?_
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hCUlt.ne (le_antisymm inf_le_left htop)
  ·
    exact isMulCommutative_quotient_of_commutator_le' hCnormal (le_of_eq hCsub.symm)

end CFSG.FeitThompson.Proofs
