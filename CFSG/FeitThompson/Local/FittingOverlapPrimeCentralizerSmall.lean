module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NonTIFittingNilpotentCoreBetaExclusion
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise _root_.CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G] {M X L : Subgroup G} {g : G} {p : ℕ}

theorem exists_isSylowProduct (Z : Subgroup G) (π : Set ℕ) :
    ∃ Y : Subgroup G, IsSylowProduct Y Z π := by
  classical
  have hQ : ∀ q : ℕ, ∃ Q : Subgroup G, IsSylowSubgroupIn Q Z q := by
    intro q
    by_cases hq : q.Prime
    · have := Fact.mk hq
      obtain ⟨S⟩ : Nonempty (Sylow q ↥Z) := inferInstance
      refine ⟨(S : Subgroup ↥Z).map Z.subtype, Subgroup.map_subtype_le _, ?_⟩
      rw [Subgroup.card_map_of_injective Z.subtype_injective, S.card_eq_multiplicity]
    · refine ⟨⊥, bot_le, ?_⟩
      rw [Nat.factorization_eq_zero_of_not_prime _ hq]
      simp
  choose Q hQ using hQ
  exact ⟨_, Q, fun q _ _ => hQ q, rfl⟩

theorem isNilpotent_sigmaCore_and_hallCoreIn_eq_and_le
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFBGAmbient G) (hsetup : IsFittingOverlapSetup M X g) :
    Group.IsNilpotent ↥(sigmaCore M) ∧ hallCoreIn M = sigmaCore M ∧ X ≤ sigmaCore M := by
  obtain ⟨Y, hY⟩ := exists_isSylowProduct (mixedFitting M) {q : ℕ | q.Prime ∧ q ∉ sigmaPrimes M}
  obtain ⟨hnil, hHS, hXS, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FBG_nonti_fitting_nilpotent_core_and_beta_exclusion h₁ h₂ h₃ h₅
      G hG M X g hsetup Y hY
  exact ⟨hnil, hHS, hXS⟩

omit [Finite G] in
theorem le_centralizer_self_of_natCard_eq_prime (hp : p.Prime) (hL : Nat.card ↥L = p) :
    L ≤ centralizer (L : Set G) := by
  have := Fact.mk hp
  have hcomm : IsMulCommutative ↥L := (isCyclic_of_prime_card hL).isMulCommutative
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥L) ⟨x, hx⟩)

omit [Finite G] in
theorem centralizerWithin_ne_bot_of_le (hp : p.Prime) (hL : Nat.card ↥L = p)
    (hLH : L ≤ hallCoreIn M) : centralizerWithin (hallCoreIn M) L ≠ ⊥ := by
  have hLC : L ≤ centralizerWithin (hallCoreIn M) L :=
    le_inf hLH (le_centralizer_self_of_natCard_eq_prime hp hL)
  intro hbot
  have hLbot : L = ⊥ := le_bot_iff.1 (hbot ▸ hLC)
  rw [hLbot, Subgroup.card_bot] at hL
  exact hp.one_lt.ne' hL.symm

theorem not_centralizer_le_of_isFittingOverlapSetup (hG : IsFBGAmbient G)
    (hsetup : IsFittingOverlapSetup M X g) (hp : p.Prime) (hLX : L ≤ X)
    (hLcard : Nat.card ↥L = p) (hXS : X ≤ sigmaCore M) :
    ¬ (centralizer (L : Set G) : Subgroup G) ≤ M := by
  have := hG.isSimpleGroup
  intro hCM
  have hLp : IsPGroup p ↥L := IsPGroup.of_card (n := 1) (by simpa using hLcard)
  have hpσ : p ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 ((isPiSubgroup_sigmaCore M).of_le (hLX.trans hXS)) p
      (Nat.mem_primeFactors.2 ⟨hp, hLcard ▸ dvd_rfl, by rw [hLcard]; exact hp.pos.ne'⟩)
  have hLM : L ≤ MulAut.conj (1 : G) • M := by
    simpa using (hLX.trans hXS).trans (sigmaCore_le M)
  have hLMg : L ≤ MulAut.conj g⁻¹ • M := by
    have hXc : X ≤ conjSubgroup (mixedFitting M) g := hsetup.eq ▸ inf_le_right
    refine (hLX.trans hXc).trans ?_
    rw [conjSubgroup_eq, conj_smul_eq_map_conj]
    exact Subgroup.map_mono (mixedFitting_le M)
  obtain ⟨c, hc, hconj⟩ := exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes
    hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hsetup.isCoatom hpσ hLp hLM hLMg
  have hcfix : MulAut.conj c • M = M :=
    mem_normalizer_iff_conj_smul_eq.1 (M.le_normalizer (hCM hc))
  have hgM : MulAut.conj g⁻¹ • M = M := by
    rw [← hconj]
    simpa using hcfix
  refine hsetup.notMem ?_
  have hg' : g ∈ normalizer (M : Set G) := by
    simpa using (normalizer (M : Set G)).inv_mem (mem_normalizer_iff_conj_smul_eq.2 hgM)
  rwa [normalizer_coe_eq_of_isCoatom hG.not_isMulCommutative hsetup.isCoatom] at hg'

theorem not_exists_isUniqueMaximalOvergroup_of_not_centralizer_le
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    {C : Subgroup G} (hM : IsCoatom M) (hCM : C ≤ M) (hCL : C ≤ centralizer (L : Set G))
    (hCG : ¬ (centralizer (L : Set G) : Subgroup G) ≤ M) (hLne : L ≠ ⊥) :
    ¬ ∃ N : Subgroup G, IsUniqueMaximalOvergroup C N := by
  rintro ⟨N, hN⟩
  have hNM : M = N := hN.eq_of_isCoatom hM hCM
  obtain ⟨y, hyL⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hLne
  have hy1 : (y : G) ≠ 1 := fun h => hyL (Subtype.ext h)
  have hCyt : (centralizer (L : Set G) : Subgroup G) ≠ ⊤ := by
    intro htop
    have : (centralizer ({(y : G)} : Set G) : Subgroup G) = ⊤ :=
      top_le_iff.1 (htop ▸ Subgroup.centralizer_le (by simp))
    exact absurd this (centralizer_singleton_lt_top hna hy1).ne
  exact hCG (hNM ▸ hN.le_of_ne_top hCL hCyt)

theorem isMulCommutative_of_isNilpotent_of_forall_natCard_eq (A : Type*) [Group A] [Finite A]
    [Group.IsNilpotent A]
    (h : ∀ q : ℕ, q.Prime → ∀ Q : Subgroup A, Nat.card ↥Q = q ^ (Nat.card A).factorization q →
      IsMulCommutative ↥Q) : IsMulCommutative A := by
  obtain ⟨P, -, hcard, ⟨e⟩⟩ := exists_mulEquiv_pi_normal_sylow A
  have hab : ∀ q : (Nat.card A).primeFactors, ∀ a b : ↥(P q), a * b = b * a := by
    intro q a b
    have := h q (Nat.prime_of_mem_primeFactors q.2) (P q) (hcard q)
    exact mul_comm' a b
  refine IsMulCommutative.of_comm fun x y => ?_
  have hpi : e.symm x * e.symm y = e.symm y * e.symm x := funext fun q => hab q _ _
  calc x * y = e (e.symm x * e.symm y) := by rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
    _ = e (e.symm y * e.symm x) := by rw [hpi]
    _ = y * x := by rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]

theorem isMulCommutative_of_not_exists_isUniqueMaximalOvergroup
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (hGm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G)
    {C : Subgroup G} (hCnil : Group.IsNilpotent ↥C) (hCtop : C ≠ ⊤)
    (hC : ¬ ∃ N : Subgroup G, IsUniqueMaximalOvergroup C N) : IsMulCommutative ↥C := by
  have := hCnil
  refine isMulCommutative_of_isNilpotent_of_forall_natCard_eq ↥C fun q hq Q hQcard => ?_
  set Q' : Subgroup G := Q.map C.subtype with hQ'
  have hQQ' : IsMulCommutative ↥Q' ↔ IsMulCommutative ↥Q :=
    ⟨fun _ => ⟨⟨fun a b => (Subgroup.equivMapOfInjective Q C.subtype
        C.subtype_injective).injective (by rw [map_mul, map_mul, mul_comm'])⟩⟩,
     fun _ => ⟨⟨fun a b => (Subgroup.equivMapOfInjective Q C.subtype
        C.subtype_injective).symm.injective (by rw [map_mul, map_mul, mul_comm'])⟩⟩⟩
  rw [← hQQ']
  by_contra hab
  have hQ'card : Nat.card ↥Q' = q ^ (Nat.card ↥C).factorization q := by
    rw [hQ', Subgroup.card_map_of_injective C.subtype_injective, hQcard]
  have ha : 1 ≤ (Nat.card ↥C).factorization q := by
    rcases Nat.eq_zero_or_pos ((Nat.card ↥C).factorization q) with h0 | h
    · rw [h0, pow_zero] at hQ'card
      exact absurd (Subgroup.eq_bot_of_card_eq _ hQ'card ▸
        (inferInstance : IsMulCommutative ↥(⊥ : Subgroup G))) hab
    · exact h
  obtain ⟨N, ⟨hN, hQN⟩, huniq⟩ := h₄ G hGm q _ Q' hq ha hQ'card hab
  exact hC ⟨N, (⟨hN, hQN, fun N' hN' hQN' => huniq N' ⟨hN', hQN'⟩⟩ :
    IsUniqueMaximalOvergroup Q' N).mono (Subgroup.map_subtype_le _) hCtop⟩

theorem centralizerWithin_hallCoreIn_properties_of_isFittingOverlapSetup
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFBGAmbient G) (hsetup : IsFittingOverlapSetup M X g) (hp : p.Prime) (hLX : L ≤ X)
    (hLcard : Nat.card ↥L = p) :
    centralizerWithin (hallCoreIn M) L ≠ ⊥ ∧
      IsMulCommutative ↥(centralizerWithin (hallCoreIn M) L) ∧
      maxElementaryAbelianPRank ↥(centralizerWithin (hallCoreIn M) L) ≤ 2 ∧
      (¬ ∃ N : Subgroup G, IsUniqueMaximalOvergroup (centralizerWithin (hallCoreIn M) L) N) ∧
      ¬ (centralizer (L : Set G) : Subgroup G) ≤ M := by
  have := hG.isSimpleGroup
  obtain ⟨hSnil, hHS, hXS⟩ :=
    isNilpotent_sigmaCore_and_hallCoreIn_eq_and_le h₁ h₂ h₃ h₅ hG hsetup
  have hLH : L ≤ hallCoreIn M := by rw [hHS]; exact hLX.trans hXS
  set C : Subgroup G := centralizerWithin (hallCoreIn M) L with hC
  have hCM : C ≤ M := (centralizerWithin_le _ _).trans (hallCoreIn_le M)
  have hCL : C ≤ centralizer (L : Set G) := inf_le_right
  have hCtop : C ≠ ⊤ := fun h => hsetup.isCoatom.1 (top_le_iff.1 (h ▸ hCM))
  have hCS : C ≤ sigmaCore M := by rw [hC, ← hHS]; exact centralizerWithin_le _ _
  have hCnil : Group.IsNilpotent ↥C := isNilpotent_of_le_of_isNilpotent hCS hSnil
  have hLne : L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hLcard
    exact hp.one_lt.ne' hLcard.symm
  have hne : C ≠ ⊥ := centralizerWithin_ne_bot_of_le hp hLcard hLH
  have hCG : ¬ (centralizer (L : Set G) : Subgroup G) ≤ M :=
    not_centralizer_le_of_isFittingOverlapSetup hG hsetup hp hLX hLcard hXS
  have hnu : ¬ ∃ N : Subgroup G, IsUniqueMaximalOvergroup C N :=
    not_exists_isUniqueMaximalOvergroup_of_not_centralizer_le hG.not_isMulCommutative
      hsetup.isCoatom hCM hCL hCG hLne
  have hGm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hab : IsMulCommutative ↥C :=
    isMulCommutative_of_not_exists_isUniqueMaximalOvergroup h₄ hGm hCnil hCtop hnu
  have hrank : maxElementaryAbelianPRank ↥C ≤ 2 := by
    by_contra hr
    exact hnu (exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank
      hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hCtop (by omega))
  exact ⟨hne, hab, hrank, hnu, hCG⟩

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson

universe u

theorem FBG_fitting_overlap_prime_centralizer_small
    (h₁ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₅ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_fitting_overlap_prime_centralizer_small.{u} :=
  fun _ _ _ hG _ _ _ hsetup _ hp _ hLX hLcard =>
    centralizerWithin_hallCoreIn_properties_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₅ hG hsetup hp
      hLX hLcard

end

end CFSG.FeitThompson.Proofs
