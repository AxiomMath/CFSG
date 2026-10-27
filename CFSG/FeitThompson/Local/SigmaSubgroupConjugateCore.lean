module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideComplement
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow
import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.SigmaNormalizerNonconjugateMaximal
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.PComplSubgroupNormalizedBySylow
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.ConjugateAffineIntersection
import CFSG.FeitThompson.Foundations.NormalContainsMinimalNormal
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G] {q : ℕ}

theorem conjSub_le_of_le_conj_smul {A P : Subgroup G} {g : G} (h : A ≤ MulAut.conj g • P) :
    conjSub g A ≤ P := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := hx
  have h2 := h ha
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  simpa [MulAut.conj] using h2

theorem conjSub_inv_eq_conj_smul (g : G) (Y : Subgroup G) :
    conjSub g⁻¹ Y = MulAut.conj g • Y := by
  rw [show conjSub g⁻¹ Y = MulAut.conj g⁻¹⁻¹ • Y from rfl, inv_inv]

theorem natCard_conjSub (g : G) (Y : Subgroup G) : Nat.card (conjSub g Y) = Nat.card Y :=
  natCard_map_conj_inv Y g

theorem isPiSubgroup_conjSub {π : Set ℕ} {Y : Subgroup G} (g : G) (h : IsPiSubgroup π Y) :
    IsPiSubgroup π (conjSub g Y) := by
  rw [isPiSubgroup_iff] at h ⊢; rwa [natCard_conjSub]

theorem conjSub_ne_bot {Y : Subgroup G} (g : G) (h : Y ≠ ⊥) : conjSub g Y ≠ ⊥ := fun hc =>
  h (Subgroup.card_eq_one.1 (by rw [← natCard_conjSub g Y, hc]; simp))

theorem conjSub_le_normalizer_conjSub {Y A : Subgroup G} (g : G)
    (h : Y ≤ normalizer (A : Set G)) :
    conjSub g Y ≤ normalizer ((conjSub g A : Subgroup G) : Set G) :=
  map_le_normalizer_map_of_le_normalizer _ h

theorem isPGroup_conjSub {A : Subgroup G} (g : G) (h : IsPGroup q ↥A) :
    IsPGroup q ↥(conjSub g A) :=
  h.of_equiv (A.equivMapOfInjective (MulAut.conj g⁻¹ : G →* G) (MulAut.conj g⁻¹).injective)

theorem mem_of_isPGroup_of_ne_bot [Finite G] {π : Set ℕ} {A : Subgroup G} (hq : q.Prime)
    (hAbot : A ≠ ⊥) (hAq : IsPGroup q ↥A) (hA : IsPiSubgroup π A) : q ∈ π := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hAq
  have hn0 : n ≠ 0 := fun h0 => hAbot (Subgroup.card_eq_one.1 (by rw [hn, h0, pow_zero]))
  refine isPiSubgroup_iff.1 hA q ?_
  rw [hn, Nat.primeFactors_pow _ hn0, hq.primeFactors]
  simp

theorem ne_top_of_isPiSubgroup_sigmaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) {M : Subgroup G} (hM : IsCoatom M)
    {Y : Subgroup G} (hY : IsPiSubgroup (sigmaPrimes M) Y) : Y ≠ ⊤ := by
  intro hYtop
  have hHall : IsHallSubgroup (sigmaPrimes M) (sigmaCore M) :=
    isHallSubgroup_sigmaCore hna hodd hsolv hM
  have hne : (sigmaCore M).index ≠ 1 := fun hc =>
    hM.1 (top_le_iff.1 (Subgroup.index_eq_one.1 hc ▸ sigmaCore_le M))
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  refine isPiNumber_iff.1 hHall.index p
    (Nat.mem_primeFactors.2 ⟨hp, hpd, Subgroup.index_ne_zero_of_finite⟩)
    (isPiSubgroup_iff.1 hY p (Nat.mem_primeFactors.2 ⟨hp, ?_, Nat.card_pos.ne'⟩))
  rw [hYtop, Subgroup.card_top]
  exact hpd.trans ((sigmaCore M).index_dvd_card)

theorem exists_minimal_normal_pGroup_le [Finite G] {Y : Subgroup G} (hYbot : Y ≠ ⊥)
    [Group.IsSolvable ↥Y] :
    ∃ (r : ℕ) (A : Subgroup G), r.Prime ∧ A ≤ Y ∧ A ≠ ⊥ ∧ IsPGroup r ↥A ∧
      Y ≤ normalizer (A : Set G) := by
  have : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).2 hYbot
  obtain ⟨A', hA'norm, hA'bot, hA'min⟩ := exists_normal_ne_bot_forall_lt_eq_bot (G := ↥Y)
  have := hA'norm
  obtain ⟨r, d, hr, hd, hcard⟩ :=
    exists_prime_card_eq_pow_of_isSolvable_of_forall_normal_lt_eq_bot hA'bot hA'min
  refine ⟨r, A'.map Y.subtype, hr, Subgroup.map_subtype_le _, ?_,
    IsPGroup.of_card (by rw [Subgroup.card_subtype, hcard]),
    le_normalizer_map_subtype_of_normal hA'norm⟩
  intro hc
  rw [← Subgroup.card_eq_one, Subgroup.card_subtype, hcard] at hc
  have : d = 0 := (Nat.pow_eq_one.1 hc).resolve_left hr.ne_one
  omega

theorem exists_conjSub_le_sigmaCore_of_isPGroup [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) {M A : Subgroup G} (hM : IsCoatom M)
    (hq : q.Prime) (hqM : q ∈ sigmaPrimes M) (hAq : IsPGroup q ↥A) :
    ∃ g : G, conjSub g A ≤ sigmaCore M := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hPS, hPcard⟩ := exists_subgroup_le_natCard_eq_pow_factorization hq (sigmaCore M)
  have hfac : (Nat.card ↥(sigmaCore M)).factorization q = (Nat.card G).factorization q :=
    (isHallSubgroup_sigmaCore hna hodd hsolv hM).factorization_natCard_eq hqM
  rw [hfac] at hPcard
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup hPcard hAq
  exact ⟨g, (conjSub_le_of_le_conj_smul hg).trans hPS⟩

theorem exists_conjSub_le_of_isHallSubgroup_compl [Finite G] {T J Y : Subgroup G}
    [Group.IsSolvable ↥T]
    (hJ : IsHallSubgroup ((sigmaPrimes T)ᶜ) (J.subgroupOf T)) (hYT : Y ≤ T)
    (hY : IsPiSubgroup ((sigmaPrimes T)ᶜ) Y) : ∃ t : G, conjSub t Y ≤ J := by
  obtain ⟨E, hE, hYE⟩ :=
    exists_isHallSubgroup_ge_of_isPiSubgroup (isPiSubgroup_subgroupOf hYT hY)
  obtain ⟨t, ht⟩ := exists_conj_smul_eq_of_isHallSubgroup hE hJ
  refine ⟨(t : G)⁻¹, ?_⟩
  rw [conjSub_inv_eq_conj_smul]
  refine le_of_subgroupOf_le (Subgroup.conj_smul_le_of_le hYT t) ?_
  rw [← Subgroup.conj_smul_subgroupOf hYT t, ← ht]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hYE

theorem FTS_sigma_subgroup_conjugate_core
    (h₁ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₃ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₄ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_sigma_subgroup_conjugate_core.{u} := by
  intro G _ _ hG M hM Y hYbot hYπ
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable_of_ne_top
  have _hfin : Fintype G := Fintype.ofFinite G
  have hG02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hodd, hG.isSimpleGroup, hna, hsolv⟩
  have hHallM : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M) :=
    (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM).isHallPiSubgroup
  have key : ∀ Z : Subgroup G, Z ≤ M → IsPiSubgroup (sigmaPrimes M) Z → Z ≤ sigmaCore M :=
    fun Z hZM hZ => le_sigmaCore_of_isPiSubgroup_of_isHallPiSubgroup hHallM hZM hZ
  have hYtop : Y ≠ ⊤ := ne_top_of_isPiSubgroup_sigmaPrimes hna hodd hsolv hM hYπ
  have : Group.IsSolvable ↥Y := hsolv Y hYtop
  obtain ⟨q, A, hq, hAY, hAbot, hAq, hYA⟩ := exists_minimal_normal_pGroup_le hYbot
  have hqM : q ∈ sigmaPrimes M := mem_of_isPGroup_of_ne_bot hq hAbot hAq (hYπ.of_le hAY)
  obtain ⟨h, hA⟩ := exists_conjSub_le_sigmaCore_of_isPGroup hna hodd hsolv hM hq hqM hAq
  set Y' := conjSub h Y with hY'
  set A' := conjSub h A with hA'
  have hA'bot : A' ≠ ⊥ := conjSub_ne_bot h hAbot
  have hA'q : IsPGroup q ↥A' := isPGroup_conjSub h hAq
  have hY'A' : Y' ≤ normalizer ((A' : Subgroup G) : Set G) := conjSub_le_normalizer_conjSub h hYA
  have hY'π : IsPiSubgroup (sigmaPrimes M) Y' := isPiSubgroup_conjSub h hYπ
  have hA'M : A' ≤ M := hA.trans (sigmaCore_le M)
  by_cases hcase : normalizer ((A' : Subgroup G) : Set G) ≤ M
  ·
    exact ⟨h, key Y' (hY'A'.trans hcase) hY'π⟩
  ·
    have hA'lt : A' < ⊤ := lt_of_le_of_ne le_top fun hc => hM.1 (top_le_iff.1 (hc ▸ hA'M))
    have hNlt : normalizer ((A' : Subgroup G) : Set G) < ⊤ :=
      normalizer_lt_top_of_isSimpleGroup (bot_lt_iff_ne_bot.2 hA'bot) hA'lt
    obtain ⟨T, hT, hNT⟩ := exists_isCoatom_ge_of_ne_top hNlt.ne
    have hMT : M ≠ T := fun hc => hcase (hc ▸ hNT)
    have hnc : ∀ g : G, T ≠ conjSub g M := by
      intro g hg
      refine not_exists_conj_smul_eq_of_normalizer_le hna hodd hsolv hM hT hMT hqM
        (bot_lt_iff_ne_bot.2 hA'bot) hA'M hA'q hNT ⟨g⁻¹, ?_⟩
      rw [hg]; rfl
    have hsep : sigmaPrimes M ∩ sigmaPrimes T = ∅ := h₄ G hG M T hM hT hnc
    have hqT : q ∉ sigmaPrimes T := fun hc => by
      have hmem : q ∈ sigmaPrimes M ∩ sigmaPrimes T := ⟨hqM, hc⟩
      rw [hsep] at hmem; exact hmem
    obtain ⟨-, -, hsd⟩ :=
      FBG_sigma_prime_normalizer_outside_complement h₁ h₂ h₃ G hG02 M T hM hT
        hMT q hq hqM A' hA'M hA'bot hA'q hNT hqT
    have : Group.IsSolvable ↥T := hsolv T hT.1
    have hJ : IsHallSubgroup ((sigmaPrimes T)ᶜ) ((M ⊓ T).subgroupOf T) :=
      isHallSubgroup_subgroupOf_of_isInternalSemidirectProduct
        (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hT) hsd
    have hY'T : Y' ≤ T := hY'A'.trans hNT
    have hY'compl : IsPiSubgroup ((sigmaPrimes T)ᶜ) Y' :=
      hY'π.mono fun p hp hpT => by
        have hmem : p ∈ sigmaPrimes M ∩ sigmaPrimes T := ⟨hp, hpT⟩
        rw [hsep] at hmem; exact hmem
    obtain ⟨t, htle⟩ := exists_conjSub_le_of_isHallSubgroup_compl hJ hY'T hY'compl
    refine ⟨h * t, ?_⟩
    rw [← conjSub_conjSub t h Y]
    exact key _ (htle.trans inf_le_left) (isPiSubgroup_conjSub t hY'π)

end

end CFSG.FeitThompson.Proofs
