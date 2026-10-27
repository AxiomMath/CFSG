module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
import CFSG.FeitThompson.Local.InvariantMaximalPrimeSubgroupsConjugate
import CFSG.FeitThompson.Local.ExceptionalPlaneMaximalElementaryAbelian
import CFSG.FeitThompson.Local.MaximalElementaryAbelianConstrained
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.FixedMaximalElementaryAbelianTrivialAction
import CFSG.FeitThompson.Local.NonuniqueScnControlsNormalizers
import CFSG.FeitThompson.Local.AbelianSylowRankTwoLocalConstraint
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.OddOrder.SigmaSylowTransporterFusion
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.Local.SupportedPlaneSylowNormalizer
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

variable {G : Type*} [Group G] [Finite G] {p q : ℕ}

theorem factorization_natCard_eq_of_isHallPiSubgroup {π : Set ℕ} {H : Subgroup G} (hq : q.Prime)
    (hH : IsHallPiSubgroup π H) (hqπ : q ∈ π) :
    (Nat.card ↥H).factorization q = (Nat.card G).factorization q := by
  have hqi : ¬ q ∣ H.index := fun hdvd =>
    hH.notMem_of_mem_primeFactors_index q
      (Nat.mem_primeFactors.2 ⟨hq, hdvd, Subgroup.index_ne_zero_of_finite⟩) hqπ
  have hsum : (Nat.card G).factorization q
      = (Nat.card ↥H).factorization q + H.index.factorization q := by
    rw [← Subgroup.card_mul_index H,
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
    simp
  rw [hsum, Nat.factorization_eq_zero_of_not_dvd hqi, Nat.add_zero]

theorem mem_maximalNormalizedPSubgroups_of_natCard {A Q : Subgroup G} (hq : q.Prime)
    (hcard : Nat.card ↥Q = q ^ (Nat.card G).factorization q)
    (hA : A ≤ normalizer (Q : Set G)) : Q ∈ maximalNormalizedPSubgroups A q := by
  have := Fact.mk hq
  refine mem_maximalNormalizedPSubgroups_of_forall (IsPGroup.of_card hcard) hA ?_
  intro R hR _ hQR
  exact (Sylow.ofCard Q hcard).is_maximal' hR (by rw [Sylow.coe_ofCard]; exact hQR)

omit [Finite G] in
theorem map_conj_inv_map_conj (Y : Subgroup G) (g : G) :
    (Y.map (MulAut.conj g⁻¹ : G →* G)).map (MulAut.conj g : G →* G) = Y := by
  have h : ((MulAut.conj (g : G) : G →* G).comp (MulAut.conj g⁻¹ : G →* G)) = MonoidHom.id G := by
    ext x; simp [MulAut.conj, mul_assoc]
  rw [Subgroup.map_map, h, Subgroup.map_id]

omit [Finite G] in
theorem map_conj_map_conj_inv (Y : Subgroup G) (g : G) :
    (Y.map (MulAut.conj g : G →* G)).map (MulAut.conj g⁻¹ : G →* G) = Y := by
  simpa using map_conj_inv_map_conj Y g⁻¹

theorem isConstrained_of_maximal_isElementaryAbelianSubgroup
    (hodd : Odd (Nat.card G)) (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H)
    (hlen : ∀ H : Subgroup G, H ≠ ⊤ → HasPLengthLeOne p ↥H) (hp : p.Prime) {A : Subgroup G}
    (hAbot : A ≠ ⊥) (hApg : IsPGroup p ↥A)
    (hA : Maximal (IsElementaryAbelianSubgroup p) A) : IsConstrained A := by
  have hπcompl : subgroupPrimeSupportCompl A = {r : ℕ | r.Prime ∧ r ≠ p} :=
    subgroupPrimeSupportCompl_eq_of_isPGroup hp hApg hAbot
  rw [isConstrained_iff]
  intro H hH hAH Y hYH hYpi hAY
  have hcop : p.Coprime (Nat.card ↥Y) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hmem := isPiSubgroup_iff.1 hYpi p (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩)
    rw [hπcompl] at hmem
    exact hmem.2 rfl
  have hle := le_map_pComplCore_of_maximal_of_le_normalizer hodd hp hAbot hA
    (hsolv H hH.ne) (hlen H hH.ne) hAH hYH hcop hAY
  rw [hπcompl]
  rwa [pComplCore_eq_piCore] at hle

theorem FTS_exceptional_invariant_sylow_separation
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_exceptional_invariant_sylow_separation.{u} := by
  intro G _ _ hG p M A₀ A P hc q hqσ g hgM _hAMg Q₁ Q₂ hQ₁ hQ₂ hAQ₁ hAQ₂
  have := hG.isSimpleGroup
  have : Fintype G := Fintype.ofFinite G
  have hp : p.Prime := hc.prime
  have := Fact.mk hp
  have hq : q.Prime := prime_of_mem_sigmaPrimes hqσ
  have hM : IsCoatom M := hc.isCoatom
  have hMin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hMin8 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hqp : q ≠ p := fun h => hc.notMem_sigmaPrimes (h ▸ hqσ)
  have hAea : IsElementaryAbelian p A :=
    isElementaryAbelian_of_nonempty_mulEquiv_pi hc.isElementaryAbelianPlane
  have hAcard : Nat.card ↥A = p ^ 2 := hc.isElementaryAbelianPlane.natCard hp.ne_zero
  have hAbot : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    exact hp.one_lt.ne' (by nlinarith [hAcard, hp.two_le])
  have hAM : A ≤ M := hc.le_of_A.trans hc.le_of_P
  obtain ⟨-, -, hCAM, hAmax⟩ := exceptional_maximal_plane hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable hM hp hc.notMem_sigmaPrimes hc.natCard_A₀ hc.le_of_A₀
    hc.le_of_A hc.le_of_P hc.isSylowSubgroupOf.2 hAea hAcard hc.normalizer_le
  have hAmax' : Maximal (IsElementaryAbelianSubgroup p) A := by
    rw [maximal_isElementaryAbelianSubgroup_iff, ← maximal_isElementaryAbelian_iff]
    refine ⟨hAea, fun E hE hAE => ?_⟩
    rcases lt_or_eq_of_le hAE with h | h
    · exact absurd h (hAmax E hE)
    · exact h.ge
  have hlen : ∀ H : Subgroup G, H ≠ ⊤ → HasPLengthLeOne p ↥H := fun H hH =>
    hasPLengthLeOne_of_not_dvd_index_comap hp (h₂ G hMin8 p hp H hH)
  have hcon : IsConstrained A := isConstrained_of_maximal_isElementaryAbelianSubgroup
    hG.odd_natCard hG.isSolvable hlen hp hAbot hAea.isPGroup hAmax'
  have hAbot' : ⊥ < A := bot_lt_iff_ne_bot.2 hAbot
  have hAtop : A < ⊤ := lt_of_le_of_lt hAM (lt_top_iff_ne_top.2 hM.1)
  have hqπ : q ∉ subgroupPrimeSupport A := by
    rw [subgroupPrimeSupport_eq_singleton_of_isPGroup hp hAea.isPGroup hAbot]
    exact hqp
  obtain ⟨-, hHall, -⟩ := h₁ G hMin M hM
  have hfacS : (Nat.card ↥(sigmaCore M)).factorization q = (Nat.card G).factorization q :=
    factorization_natCard_eq_of_isHallPiSubgroup hq hHall hqσ
  have hQ₁card : Nat.card ↥Q₁ = q ^ (Nat.card G).factorization q := by rw [hQ₁.2, hfacS]
  have hQ₂card : Nat.card ↥Q₂ = q ^ (Nat.card G).factorization q := by
    rw [hQ₂.2, natCard_conjBy, hfacS]
  have hQ₁mem : Q₁ ∈ maximalNormalizedPSubgroups A q :=
    mem_maximalNormalizedPSubgroups_of_natCard hq hQ₁card hAQ₁
  have hQ₂mem : Q₂ ∈ maximalNormalizedPSubgroups A q :=
    mem_maximalNormalizedPSubgroups_of_natCard hq hQ₂card hAQ₂
  have hQ₁M : Q₁ ≤ M := hQ₁.1.trans (sigmaCore_le M)
  have hQ₂notM : ¬ Q₂ ≤ M := by
    intro hQ₂M
    have hQ₂g : Q₂.map (MulAut.conj g : G →* G) ≤ M := by
      refine le_trans (Subgroup.map_mono hQ₂.1) ?_
      rw [conjBy, conj_smul_eq_map_conj, map_conj_inv_map_conj]
      exact sigmaCore_le M
    have hcard : Nat.card ↥(Q₂.map (MulAut.conj g : G →* G))
        = q ^ (Nat.card ↥M).factorization q := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hQ₂card,
        factorization_eq_of_mem_sigmaPrimes hqσ]
    exact hgM (mem_of_map_conj_inv_le hqσ hQ₂g hcard
      (by rw [map_conj_map_conj_inv]; exact hQ₂M))
  have hnoconj : ∀ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q₁ ≠ Q₂ := by
    intro k hk heq
    refine hQ₂notM ?_
    rw [← heq, conj_smul_eq_map_conj]
    have hkM : k ∈ M := hCAM (constrainedCentralizerCore_le_centralizer A hk)
    exact le_trans (Subgroup.map_mono hQ₁M) (map_conj_eq_self (M.inv_mem hkM)).le
  refine ⟨?_, ?_⟩
  ·
    by_contra hne
    have hQ₁inf : (Q₁ ⊓ M : Subgroup G) ≠ ⊥ := by
      rw [inf_eq_left.2 hQ₁M]
      exact fun h => hne (by rw [h]; simp)
    have hQ₂inf : (Q₂ ⊓ M : Subgroup G) ≠ ⊥ := fun h =>
      hne (le_bot_iff.1 (h ▸ le_inf inf_le_right (inf_le_left.trans hQ₁M)))
    obtain ⟨k, hk, hkeq⟩ := exists_mem_constrainedCentralizerCore_conj_inv_smul_eq
      hG.isSolvable hAbot' hAtop hcon hq hqπ hQ₁mem hQ₂mem (lt_top_iff_ne_top.2 hM.1) hAM
      hQ₁inf hQ₂inf
    exact hnoconj k hk hkeq
  ·
    intro X hXA hXcard
    by_contra hcontra
    rw [not_or] at hcontra
    obtain ⟨h1, h2⟩ := hcontra
    have hXbot : X ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hXcard
      exact hp.one_lt.ne hXcard
    have hXp : IsPGroup p ↥X := IsPGroup.of_card (by rw [hXcard, pow_one])
    have hAX : A ≤ centralizer (X : Set G) := fun a ha =>
      mem_centralizer_iff.2 fun x hx => hAea.mul_comm (hXA hx) ha
    have hCXtop : centralizer (X : Set G) < ⊤ :=
      lt_of_le_of_lt (centralizer_le_normalizer _)
        (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hp hXbot hXp)
    obtain ⟨k, hk, hkeq⟩ := exists_mem_constrainedCentralizerCore_conj_inv_smul_eq
      hG.isSolvable hAbot' hAtop hcon hq hqπ hQ₁mem hQ₂mem hCXtop hAX h1 h2
    exact hnoconj k hk hkeq

end

end CFSG.FeitThompson.Proofs
