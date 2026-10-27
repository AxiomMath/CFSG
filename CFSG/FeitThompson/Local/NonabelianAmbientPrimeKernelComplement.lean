module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Local.ThreeFactorPrimeKernelComplement
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
import CFSG.FeitThompson.Local.TauTwoFactorContainsPlaneRegularActions
import CFSG.FeitThompson.Local.NonabelianAmbientSylowCentralizingKernel
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.NonconjugateIntersectionPrimeCentralization
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.SplitPrimeKernelFreeComplement
import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep03 (IsAmbient IsPlaneSetup IsSemidirect
  IsSylowOf IsSylowTop cent cent1)

universe u

variable {G : Type u} [Group G]

theorem le_normalizer_subgroupOf' {E D X : Subgroup G} (h : X ≤ normalizer (D : Set G)) :
    X.subgroupOf E ≤ normalizer ((D.subgroupOf E : Subgroup ↥E) : Set ↥E) := fun x hx =>
  Subgroup.mem_normalizer_iff.2 fun y => by
    simpa [mem_subgroupOf] using
      Subgroup.mem_normalizer_iff.1 (h (mem_subgroupOf.1 hx)) (y : G)

theorem isComplement'_subgroupOf' {E A B : Subgroup G} (hAE : A ≤ E) (hBE : B ≤ E)
    (hnorm : E ≤ normalizer (A : Set G)) (hsup : A ⊔ B = E) (hinf : A ⊓ B = ⊥) :
    (A.subgroupOf E).IsComplement' (B.subgroupOf E) := by
  have : (A.subgroupOf E).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).2 hnorm
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 ?_) ?_
  · change (A ⊓ B).subgroupOf E = ⊥
    rw [hinf, Subgroup.bot_subgroupOf]
  · rw [← Subgroup.normal_mul (A.subgroupOf E) (B.subgroupOf E),
      ← Subgroup.subgroupOf_sup hAE hBE, hsup, Subgroup.subgroupOf_self, Subgroup.coe_top]

theorem sup_inf_of_isComplement'_subgroupOf {E A B : Subgroup G} (hAE : A ≤ E) (hBE : B ≤ E)
    (h : (A.subgroupOf E).IsComplement' (B.subgroupOf E)) : A ⊔ B = E ∧ A ⊓ B = ⊥ :=
  ⟨by rw [← Subgroup.map_subgroupOf_eq_of_le hAE, ← Subgroup.map_subgroupOf_eq_of_le hBE,
      ← Subgroup.map_sup, h.isCompl.sup_eq_top, map_subtype_top],
   by rw [← Subgroup.map_subgroupOf_eq_of_le hAE, ← Subgroup.map_subgroupOf_eq_of_le hBE,
      ← Subgroup.map_inf _ _ _ E.subtype_injective, h.isCompl.inf_eq_bot, Subgroup.map_bot]⟩

theorem subgroupOf_sup₃ {E E₃ P₀ E₁ : Subgroup G} (h3 : E₃ ≤ E) (h0 : P₀ ≤ E) (h1 : E₁ ≤ E) :
    (E₃ ⊔ (P₀ ⊔ E₁)).subgroupOf E
      = E₃.subgroupOf E ⊔ (P₀.subgroupOf E ⊔ E₁.subgroupOf E) := by
  rw [Subgroup.subgroupOf_sup h3 (sup_le h0 h1), Subgroup.subgroupOf_sup h0 h1]

theorem mem_of_orderOf_eq_of_isHallPiSubgroup [Finite G] {π : Set ℕ} {E X : Subgroup G} {q : ℕ}
    {z : G} (hq : q.Prime) (hqπ : q ∈ π) (hz : orderOf z = q) (hzE : z ∈ E)
    [(X.subgroupOf E).Normal] (hXhall : IsHallPiSubgroup π (X.subgroupOf E)) (hXE : X ≤ E) :
    z ∈ X := by
  have h1 : IsPiSubgroup π ((zpowers z).subgroupOf E) := by
    refine isPiSubgroup_iff.2 fun r hr => ?_
    rw [natCard_subgroupOf_eq (zpowers_le.2 hzE), Nat.card_zpowers, hz,
      hq.primeFactors, Finset.mem_singleton] at hr
    exact hr ▸ hqπ
  have h3 := Subgroup.map_mono (f := E.subtype) (hXhall.le_of_isPiSubgroup h1)
  rw [Subgroup.map_subgroupOf_eq_of_le (zpowers_le.2 hzE),
    Subgroup.map_subgroupOf_eq_of_le hXE] at h3
  exact h3 (Subgroup.mem_zpowers z)

theorem mem_inf_centralizer_zpowers {S : Subgroup G} {z h : G} (hhS : h ∈ S)
    (hcomm : Commute z h) : h ∈ S ⊓ centralizer ((zpowers z : Subgroup G) : Set G) := by
  refine mem_inf.2 ⟨hhS, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  obtain ⟨k, rfl⟩ := hg
  exact (hcomm.zpow_left k).eq

theorem not_dvd_natCard_of_isTauHallSplitting [Finite G] {p : ℕ} (hp : p.Prime)
    {M E E₁ E₂ E₃ : Subgroup G} (hsplit : _root_.CFSG.FeitThompson.IsTauHallSplitting M E E₁ E₂ E₃)
    (hE₂card : Nat.card ↥E₂ = p ^ (Nat.card ↥E).factorization p) :
    ¬ p ∣ Nat.card ↥E₃ ∧ ¬ p ∣ Nat.card ↥E₁ := by
  have hcardE : Nat.card ↥E = Nat.card ↥E₃ * (Nat.card ↥E₂ * Nat.card ↥E₁) := by
    rw [← hsplit.inner.natCard_eq_mul, ← hsplit.outer.natCard_eq_mul]
  have hfacsum : (Nat.card ↥E).factorization p
      = (Nat.card ↥E₃).factorization p
        + ((Nat.card ↥E).factorization p + (Nat.card ↥E₁).factorization p) := by
    conv_lhs => rw [hcardE]
    rw [Nat.factorization_mul Nat.card_pos.ne' (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'),
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp [hE₂card, hp.factorization_pow]
  exact ⟨fun hd => absurd (show (Nat.card ↥E₃).factorization p = 0 by omega)
      (hp.factorization_pos_of_dvd Nat.card_pos.ne' hd).ne',
    fun hd => absurd (show (Nat.card ↥E₁).factorization p = 0 by omega)
      (hp.factorization_pos_of_dvd Nat.card_pos.ne' hd).ne'⟩

theorem exists_invariant_isCyclic_complement [Finite G] {p : ℕ} (hp : p.Prime)
    {P A₀ Y B : Subgroup G} (hPab : IsMulCommutative ↥P) (hA₀P : A₀ ≤ P) (hYP : Y ≤ P)
    (hA₀card : Nat.card ↥A₀ = p) (hYcyc : IsCyclic ↥Y) (hsup : A₀ ⊔ Y = P) (hinf : A₀ ⊓ Y = ⊥)
    (hBP : B ≤ normalizer (P : Set G)) (hBA₀ : B ≤ normalizer (A₀ : Set G))
    (hBcard : ¬ p ∣ Nat.card ↥B) :
    ∃ P₀ : Subgroup G, P₀ ≤ P ∧ B ≤ normalizer (P₀ : Set G) ∧ IsCyclic ↥P₀ ∧
      A₀ ⊔ P₀ = P ∧ A₀ ⊓ P₀ = ⊥ ∧ Nat.card ↥P₀ = Nat.card ↥Y := by
  have := hPab
  let _ : CommGroup ↥P := IsMulCommutative.instCommGroup
  have : IsCyclic ↥(Y.subgroupOf P) := isCyclic_subgroupOf hYP hYcyc
  set α : ↥B →* MulAut ↥P := conjOnNormalized P hBP with hα
  have hA₀card' : Nat.card ↥(A₀.subgroupOf P) = p := by
    rw [natCard_subgroupOf_eq hA₀P, hA₀card]
  have hprod : ((A₀.subgroupOf P : Subgroup ↥P) : Set ↥P)
      * ((Y.subgroupOf P : Subgroup ↥P) : Set ↥P) = Set.univ := by
    rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hA₀P hYP, hsup, Subgroup.subgroupOf_self,
      Subgroup.coe_top]
  have hinf' : A₀.subgroupOf P ⊓ Y.subgroupOf P = ⊥ := by
    change (A₀ ⊓ Y).subgroupOf P = ⊥
    rw [hinf, Subgroup.bot_subgroupOf]
  have hBcop : (Nat.card ↥B).Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hBcard).symm
  have hstable : ∀ b : ↥B, ∀ x ∈ A₀.subgroupOf P, α b x ∈ A₀.subgroupOf P := by
    intro b x hx
    have h1 : ((α b x : ↥P) : G) = (b : G) * (x : G) * (b : G)⁻¹ :=
      conjOnNormalized_apply_coe hBP b x
    refine mem_subgroupOf.2 ?_
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.1 (hBA₀ b.2) (x : G)).1 (mem_subgroupOf.1 hx)
  obtain ⟨Q, hinvQ, hcycQ, hprodQ, hinfQ, hcardQ⟩ :=
    exists_invariant_isCyclic_of_natCard_eq_prime hp hA₀card' hprod hinf' hBcop α
      (map_eq_of_invariant α hstable)
  have hsupQ : A₀.subgroupOf P ⊔ Q = ⊤ := by
    refine top_le_iff.1 fun z _ => ?_
    have hz : z ∈ ((A₀.subgroupOf P : Subgroup ↥P) : Set ↥P) * (Q : Set ↥P) := by
      rw [hprodQ]; trivial
    obtain ⟨a, ha, q, hq, rfl⟩ := hz
    exact Subgroup.mul_mem_sup ha hq
  refine ⟨Q.map P.subtype, Subgroup.map_subtype_le _, ?_, isCyclic_map_subtype hcycQ, ?_, ?_, ?_⟩
  · intro b hb
    rw [FreeCore.mem_normalizer_iff_map]
    have hcomp : (MulAut.conj b).toMonoidHom.comp P.subtype
        = P.subtype.comp ((α ⟨b, hb⟩ : ↥P ≃* ↥P) : ↥P →* ↥P) := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, Subgroup.coe_subtype]
      exact (conjOnNormalized_apply_coe hBP ⟨b, hb⟩ x).symm
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hinvQ ⟨b, hb⟩]
  · rw [← Subgroup.map_subgroupOf_eq_of_le hA₀P, ← Subgroup.map_sup, hsupQ, map_subtype_top]
  · rw [← Subgroup.map_subgroupOf_eq_of_le hA₀P,
      ← Subgroup.map_inf _ _ _ P.subtype_injective, hinfQ, Subgroup.map_bot]
  · rw [Subgroup.card_subtype, hcardQ, natCard_subgroupOf_eq hYP]

theorem isThreeFactorPrimeKernelSetup_subgroupOf [Finite G] {p : ℕ} (hp : p.Prime)
    {M E E₁ E₂ E₃ A₀ P₀ : Subgroup G}
    (hsplit : _root_.CFSG.FeitThompson.IsTauHallSplitting M E E₁ E₂ E₃)
    (hE₂card : Nat.card ↥E₂ = p ^ (Nat.card ↥E).factorization p)
    (hE₃nd : ¬ p ∣ Nat.card ↥E₃) (hE₁nd : ¬ p ∣ Nat.card ↥E₁)
    (hEnormA₀ : E ≤ normalizer (A₀ : Set G)) (hA₀card : Nat.card ↥A₀ = p)
    (hA₀E₂ : A₀ ≤ E₂) (hP₀E₂ : P₀ ≤ E₂) (hE₁P₀ : E₁ ≤ normalizer (P₀ : Set G))
    (hsupA : A₀ ⊔ P₀ = E₂) (hinfA : A₀ ⊓ P₀ = ⊥) :
    IsThreeFactorPrimeKernelSetup p (E₃.subgroupOf E) (E₂.subgroupOf E) (E₁.subgroupOf E)
      (A₀.subgroupOf E) (P₀.subgroupOf E) :=
  { prime := hp
    normal_E3 := hsplit.outer.normal_subgroupOf
    isComplement_E3 := by
      have h := isComplement'_subgroupOf' hsplit.le_E₃ (sup_le hsplit.le_E₂ hsplit.le_E₁)
        hsplit.outer.le_normalizer hsplit.outer.sup_eq hsplit.outer.inf_eq_bot
      rwa [Subgroup.subgroupOf_sup hsplit.le_E₂ hsplit.le_E₁] at h
    E1_le_normalizer_P := le_normalizer_subgroupOf' (le_sup_right.trans hsplit.inner.le_normalizer)
    inf_P_E1 := by
      change (E₂ ⊓ E₁).subgroupOf E = ⊥
      rw [hsplit.inner.inf_eq_bot, Subgroup.bot_subgroupOf]
    isPGroup_P := IsPGroup.of_card (by rw [natCard_subgroupOf_eq hsplit.le_E₂, hE₂card])
    not_dvd_card_E3 := by rw [natCard_subgroupOf_eq hsplit.le_E₃]; exact hE₃nd
    not_dvd_card_E1 := by rw [natCard_subgroupOf_eq hsplit.le_E₁]; exact hE₁nd
    normal_A0 := (Subgroup.normal_subgroupOf_iff_le_normalizer (hA₀E₂.trans hsplit.le_E₂)).2
      hEnormA₀
    card_A0 := by rw [natCard_subgroupOf_eq (hA₀E₂.trans hsplit.le_E₂), hA₀card]
    A0_le_P := fun x hx => mem_subgroupOf.2 (hA₀E₂ (mem_subgroupOf.1 hx))
    P0_le_P := fun x hx => mem_subgroupOf.2 (hP₀E₂ (mem_subgroupOf.1 hx))
    E1_le_normalizer_P0 := le_normalizer_subgroupOf' hE₁P₀
    sup_A0_P0 := by
      rw [← Subgroup.subgroupOf_sup (hA₀E₂.trans hsplit.le_E₂) (hP₀E₂.trans hsplit.le_E₂), hsupA]
    inf_A0_P0 := by
      change (A₀ ⊓ P₀).subgroupOf E = ⊥
      rw [hinfA, Subgroup.bot_subgroupOf] }

theorem exists_prime_kernel_complement
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₇ : Statements.FPL_low_rank_sylow_central_product.{u})
    (h₉ : Statements.FTS_proper_subgroup_p_length_one.{u})
    (G : Type u) [Group G] [Fintype G] (hG : IsAmbient G)
    (p : ℕ) (M A E : Subgroup G) (hsetup : IsPlaneSetup G p M A E)
    (hnonab : ∃ Q : Subgroup G, IsSylowTop p Q ∧ ¬ IsMulCommutative ↥Q)
    (A₀ : Subgroup G) (hA₀ : A₀ = cent A (sigmaCore M : Set G)) :
    ∃ E₀ : Subgroup G, IsSemidirect E A₀ E₀ ∧ p ∣ Nat.card ↥E₀ ∧
      ∀ h ∈ sigmaCore M, h ≠ 1 →
        ∀ r ∈ (Nat.card ↥(cent1 E₀ h)).primeFactors, r ∈ tau1Primes M := by
  have hp : p.Prime := hsetup.prime
  have hfp := Fact.mk hp
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hG' : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hG02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    ⟨hsetup.decomp.2.2.2.1, hsetup.decomp.2.2.1, disjoint_iff.2 hsetup.decomp.2.2.2.2⟩
  have hosA : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hsetup.isCoatom, hsemi⟩
  have hAE : A ≤ E := hsetup.le_E_A
  have hEM : E ≤ M := hsemi.right_le
  have hpS : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hdvd =>
    hsetup.notMem_sigma (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))
  have hfacME : (Nat.card ↥M).factorization p = (Nat.card ↥E).factorization p := by
    rw [hsemi.natCard_eq_mul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hpS]
  have hEσ : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥E → q ∉ sigmaPrimes M := by
    intro q hq hqE
    obtain ⟨hHallOf, -, -⟩ := h₁ G hG02 M hsetup.isCoatom
    refine hHallOf.2.notMem_of_mem_primeFactors_index q (Nat.mem_primeFactors.2 ⟨hq, ?_, ?_⟩)
    · rw [index_subgroupOf_left_eq hsemi]; exact hqE
    · rw [index_subgroupOf_left_eq hsemi]; exact Nat.card_pos.ne'
  have hnonab4 : ∃ Q : Subgroup G, _root_.CFSG.FeitThompson.IsSylowSubgroup p Q ∧
      ¬ IsMulCommutative ↥Q := by
    obtain ⟨Q, hQ, hQnc⟩ := hnonab
    exact ⟨Q, (_root_.CFSG.FeitThompson.isSylowSubgroup_iff_natCard hp).2 hQ, hQnc⟩
  have hτ₂ : tauTwoPrimes M = {p} :=
    FNI_nonabelian_ambient_single_rank_two_prime h₃ h₅ h₆ h₉ G hG p M A E hsetup hnonab
  obtain ⟨E₁, E₂, E₃, hsplit, hne⟩ := FNI_sigma_complement_three_factors h₁ G hG' M E hsc
  obtain ⟨hAE₂, hreg⟩ :=
    FNI_sigma_complement_regular_factors h₃ h₄ h₅ G hG' p M A E E₁ E₂ E₃ hosA hsc hAE
      hsplit.toIsTauHallSplitting
  have hE₂card : Nat.card ↥E₂ = p ^ (Nat.card ↥E).factorization p := by
    refine natCard_eq_pow_factorization_of_isHallSubgroup_singleton hp hsplit.le_E₂ ?_
    rw [isHallSubgroup_iff_isHallPiSubgroup, ← hτ₂]
    exact hsplit.isHall_E₂
  have hE₂syl : _root_.CFSG.FeitThompson.IsSylowIn p E E₂ :=
    (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hsplit.le_E₂).2 hE₂card
  obtain ⟨⟨Y, hYbot, hYcyc, hYdir, hYcent⟩, hPcent⟩ :=
    FNI_nonabelian_ambient_sylow_centralizing_kernel h₁ h₂ h₃ h₄ h₅ h₇ G hG' p M A E hosA hsc
      hAE hnonab4 E₂ hE₂syl hAE₂
  obtain ⟨A₀', hA₀'A, hA₀'card, hA₀'cent, hline, hA₀'eq, hA₀'M, hMnorm⟩ :=
    h₂ G hG' p M A E hosA hsc hAE hnonab4
  have hA₀eq : A₀ = A₀' := by rw [hA₀, hA₀'eq]; rfl
  rw [hA₀eq]
  rw [← hA₀'eq] at hYdir
  have hE₂ab : IsMulCommutative ↥E₂ := ((h₅ G hG' p M A hosA).2.2.1 E₂
    ((_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp (hsplit.le_E₂.trans hEM)).2
      (by rw [hE₂card, hfacME]))).1
  obtain ⟨hE₃nd, hE₁nd⟩ :=
    not_dvd_natCard_of_isTauHallSplitting hp hsplit.toIsTauHallSplitting hE₂card
  obtain ⟨P₀, hP₀E₂, hE₁P₀, hP₀cyc, hsupA, hinfA, hP₀card⟩ :=
    exists_invariant_isCyclic_complement hp hE₂ab hYdir.left_le hYdir.right_le hA₀'card hYcyc
      hYdir.sup_eq hYdir.inf_eq_bot (le_sup_right.trans hsplit.inner.le_normalizer)
      (hsplit.le_E₁.trans (hEM.trans hMnorm)) hE₁nd
  have hkernel := isThreeFactorPrimeKernelSetup_subgroupOf hp hsplit.toIsTauHallSplitting hE₂card
    hE₃nd hE₁nd (hEM.trans hMnorm) hA₀'card hYdir.left_le hP₀E₂ hE₁P₀ hsupA hinfA
  set E₀ : Subgroup G := E₃ ⊔ (P₀ ⊔ E₁) with hE₀def
  have hP₀E : P₀ ≤ E := hP₀E₂.trans hsplit.le_E₂
  have hE₀E : E₀ ≤ E := sup_le hsplit.le_E₃ (sup_le hP₀E hsplit.le_E₁)
  have hA₀E : A₀' ≤ E := hYdir.left_le.trans hsplit.le_E₂
  have hsub := subgroupOf_sup₃ hsplit.le_E₃ hP₀E hsplit.le_E₁
  obtain ⟨hsupE, hinfE⟩ := sup_inf_of_isComplement'_subgroupOf hA₀E hE₀E
    (by rw [hE₀def, hsub]; exact hkernel.isComplement'_A0)
  refine ⟨E₀, ⟨hA₀E, hE₀E, hEM.trans hMnorm, hsupE, hinfE⟩, ?_, ?_⟩
  ·
    have hord := hkernel.ordProj_card_sup
    rw [← hsub, natCard_subgroupOf_eq hE₀E, natCard_subgroupOf_eq hP₀E, hP₀card] at hord
    refine (hp.dvd_iff_one_le_factorization Nat.card_pos.ne').2 ?_
    rcases Nat.eq_zero_or_pos ((Nat.card ↥E₀).factorization p) with h | h
    · rw [h, pow_zero] at hord
      exact absurd hord.symm fun hh => hYbot (Subgroup.card_eq_one.1 hh)
    · exact h
  ·
    intro h hhS hh1 q hq
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.1 hq
    obtain ⟨z, hzmem, hzord⟩ := exists_mem_orderOf_eq_of_dvd hqp hqdvd
    obtain ⟨hzE₀, hzc⟩ := mem_inf.1 hzmem
    have hzE : z ∈ E := hE₀E hzE₀
    have hz1 : z ≠ 1 := fun hz => by
      rw [hz, orderOf_one] at hzord; exact hqp.one_lt.ne hzord
    have hcomm : Commute z h := Subgroup.mem_centralizer_singleton_iff.1 hzc
    have hqE : q ∣ Nat.card ↥E := by rw [← hzord]; exact Subgroup.orderOf_dvd_natCard _ hzE
    have hqσ : q ∉ sigmaPrimes M := hEσ q hqp hqE
    by_contra hqτ₁
    have hqτ₂ : q ∉ tauTwoPrimes M := by
      rw [hτ₂]
      intro hqeq
      have hqp' : q = p := hqeq
      have hWcard : Nat.card ↥(zpowers z) = p := by rw [Nat.card_zpowers, hzord, hqp']
      have hWne : zpowers z ≠ A₀' := by
        intro hW
        have hzA : z ∈ A₀' := hW ▸ Subgroup.mem_zpowers z
        have hmem : z ∈ (⊥ : Subgroup G) := hinfE ▸ mem_inf.2 ⟨hzA, hzE₀⟩
        exact hz1 (by simpa using hmem)
      have hcon := (hline (zpowers z) (zpowers_le.2 hzE) hWcard hWne).1
      have hmem := mem_inf_centralizer_zpowers hhS hcomm
      rw [hcon] at hmem
      exact hh1 (by simpa using hmem)
    have hqM : q ∣ Nat.card ↥M := hqE.trans (Subgroup.card_dvd_of_le hEM)
    have hqτ₃ : q ∈ tau3Primes M :=
      (mem_sigmaPrimes_or_mem_tau3Primes hG.not_isMulCommutative hG.odd_natCard
        hG.forall_isSolvable hsetup.isCoatom hqp hqM hqτ₁ hqτ₂).resolve_left hqσ
    have hE₃normal : (E₃.subgroupOf E).Normal := hsplit.outer.normal_subgroupOf
    have hzE₃ : z ∈ E₃ := mem_of_orderOf_eq_of_isHallPiSubgroup hqp hqτ₃ hzord hzE
      hsplit.isHall_E₃ hsplit.le_E₃
    have hcon := hreg z hz1 (Or.inl hzE₃)
    have hmem : h ∈ sigmaCore M ⊓ centralizer ({z} : Set G) :=
      mem_inf.2 ⟨hhS, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm.eq⟩
    rw [hcon] at hmem
    exact hh1 (by simpa using hmem)

theorem FNI_nonabelian_ambient_prime_kernel_complement
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₇ : Statements.FPL_low_rank_sylow_central_product.{u})
    (_h₈ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₉ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_nonabelian_ambient_prime_kernel_complement.{u} := by
  intro G _ _ hG p M A E hsetup hnonab A₀ hA₀
  have hp : p.Prime := hsetup.prime
  have hfp := Fact.mk hp
  have hG' : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    ⟨hsetup.decomp.2.2.2.1, hsetup.decomp.2.2.1, disjoint_iff.2 hsetup.decomp.2.2.2.2⟩
  have hosA : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hsetup.isCoatom, hsemi⟩
  have hAE : A ≤ E := hsetup.le_E_A
  have hEM : E ≤ M := hsemi.right_le
  have hpS : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hdvd =>
    hsetup.notMem_sigma (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))
  have hfacME : (Nat.card ↥M).factorization p = (Nat.card ↥E).factorization p := by
    rw [hsemi.natCard_eq_mul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hpS]
  have hsylab : ∀ P : Subgroup G, IsSylowOf p P E → IsMulCommutative ↥P := by
    intro P hP
    refine ((h₅ G hG' p M A hosA).2.2.1 P ?_).1
    rw [_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp (hP.1.trans hEM), hP.2, hfacME]
  obtain ⟨A₀', hA₀'A, hA₀'card, hA₀'cent, hline, hA₀'eq, hA₀'M, hMnorm⟩ :=
    h₂ G hG' p M A E hosA hsc hAE
      (by obtain ⟨Q, hQ, hQnc⟩ := hnonab
          exact ⟨Q, (_root_.CFSG.FeitThompson.isSylowSubgroup_iff_natCard hp).2 hQ, hQnc⟩)
  have hA₀eq : A₀ = A₀' := by rw [hA₀, hA₀'eq]; rfl
  subst hA₀eq
  exact ⟨hA₀'card, hMnorm, by rw [hA₀'eq]; exact inf_le_right, hsylab,
    exists_prime_kernel_complement h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₉ G hG p M A E hsetup hnonab A₀ hA₀⟩

end

end CFSG.FeitThompson.Proofs
