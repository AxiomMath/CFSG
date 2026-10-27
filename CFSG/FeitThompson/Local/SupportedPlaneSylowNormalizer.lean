module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
import CFSG.FeitThompson.Local.FiniteNilpotentSubnormal
import CFSG.FeitThompson.Local.SubnormalConstrainedTransitivity
import CFSG.FeitThompson.Local.MaximalElementaryAbelianConstrained
import CFSG.FeitThompson.Local.SubnormalNormalizerFactorization
import CFSG.FeitThompson.Local.ThompsonTransitivityRankThreeScn
import CFSG.FeitThompson.Local.CentralPlaneConstrainedTransitivity
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson

universe u

variable {G : Type*} [Group G] [Finite G] {p q : ℕ}

omit [Finite G] in
theorem subgroupPrimeSupport_eq_singleton {A : Subgroup G} (hp : p.Prime)
    (hAcard : Nat.card A = p ^ 2) : subgroupPrimeSupport A = {p} := by
  rw [subgroupPrimeSupport_def, hAcard, Nat.primeFactors_prime_pow two_ne_zero hp]
  simp

omit [Finite G] in
theorem subgroupPrimeSupportCompl_eq_of_card {A : Subgroup G} (hp : p.Prime)
    (hAcard : Nat.card A = p ^ 2) :
    subgroupPrimeSupportCompl A = {r : ℕ | r.Prime ∧ r ≠ p} := by
  ext r
  simp [mem_subgroupPrimeSupportCompl_iff, subgroupPrimeSupport_eq_singleton hp hAcard]

theorem hasPLengthLeOne_of_not_dvd_index_comap (hp : p.Prime) {H : Subgroup G}
    (h : ¬ p ∣ (Subgroup.comap (QuotientGroup.mk' (pComplCore p ↥H))
        (pCore p (↥H ⧸ pComplCore p ↥H))).index) :
    HasPLengthLeOne p ↥H := by
  have := Fact.mk hp
  rw [hasPLengthLeOne_iff_not_dvd_index]
  rwa [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at h

theorem isConstrained_of_maximal_plane (hodd : Odd (Nat.card G)) (hp : p.Prime) {A : Subgroup G}
    (hA : Maximal (IsElementaryAbelianSubgroup p) A) (hAcard : Nat.card A = p ^ 2)
    (hA0 : A ≠ ⊥) (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hlen : ∀ H : Subgroup G, H ≠ ⊤ → HasPLengthLeOne p ↥H) :
    IsConstrained A := by
  have hpA : p ∈ subgroupPrimeSupport A := by
    rw [subgroupPrimeSupport_eq_singleton hp hAcard]; rfl
  refine isConstrained_iff.2 fun H hH hAH Y hYH hY hAY => ?_
  have hcop : p.Coprime (Nat.card Y) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd =>
      (mem_subgroupPrimeSupportCompl_iff.1 (isPiSubgroup_iff.1 hY p
        (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))).2 hpA
  have h := le_map_pComplCore_of_maximal_of_le_normalizer hodd hp hA0 hA (hsolv H hH.ne)
    (hlen H hH.ne) hAH hYH hcop hAY
  rwa [pComplCore_eq_piCore, ← subgroupPrimeSupportCompl_eq_of_card (A := A) hp hAcard] at h

omit [Finite G] in
theorem mem_maximalNormalizedPSubgroups_smul {N Q : Subgroup G} (σ : MulAut G)
    (hQ : Q ∈ maximalNormalizedPSubgroups N q) :
    (σ • Q : Subgroup G) ∈ maximalNormalizedPSubgroups (σ • N : Subgroup G) q := by
  have key : ∀ (τ : MulAut G) (R : Subgroup G),
      normalizer ((τ • R : Subgroup G) : Set G) = τ • normalizer (R : Set G) := by
    intro τ R
    rw [show (τ • R) = R.map τ.toMonoidHom from rfl,
      show (τ • normalizer (R : Set G)) = (normalizer (R : Set G)).map τ.toMonoidHom from rfl,
      Subgroup.map_equiv_normalizer_eq]
  have hstep : ∀ (τ : MulAut G) (M R : Subgroup G), IsPGroup q R → M ≤ normalizer (R : Set G) →
      IsPGroup q (τ • R : Subgroup G) ∧
        (τ • M : Subgroup G) ≤ normalizer ((τ • R : Subgroup G) : Set G) := by
    intro τ M R hR hMR
    refine ⟨hR.of_equiv (Subgroup.equivSMul τ R), ?_⟩
    rw [key τ R]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hMR
  obtain ⟨h1, h2⟩ := hstep σ N Q (isPGroup_of_mem hQ) (le_normalizer_of_mem hQ)
  refine mem_maximalNormalizedPSubgroups_of_forall h1 h2 fun R hR hNR hQR => ?_
  obtain ⟨h3, h4⟩ := hstep σ⁻¹ (σ • N : Subgroup G) R hR hNR
  rw [inv_smul_smul] at h4
  have hQR' : Q ≤ (σ⁻¹ • R : Subgroup G) := by
    have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := σ⁻¹).2 hQR
    rwa [inv_smul_smul] at this
  have := eq_of_mem_of_le hQ h3 h4 hQR'
  rw [← this, smul_inv_smul]

theorem FTS_supported_plane_sylow_normalizer
    (h₁ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_supported_plane_sylow_normalizer.{u} := by
  intro G _ _ hG p q hp hq hpq A hA Q _hQp _hAQ hQmem hqC
  have hsimple := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hsolv := hG.isSolvable_of_ne_top
  have hodd := hG.odd_natCard
  obtain ⟨hAmax, hAcard⟩ := hA
  have hpf : Fact p.Prime := ⟨hp⟩
  have hA0 : A ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hAcard
    exact absurd hAcard (by simpa using (Nat.one_lt_pow two_ne_zero hp.one_lt).ne)
  have hAp : IsPGroup p A := hAmax.prop.isPGroup
  have hAtop : A < ⊤ := lt_top_of_isPGroup hna hp hA0 hAp
  have hπA : subgroupPrimeSupport A = {p} := subgroupPrimeSupport_eq_singleton hp hAcard
  have hqπ : q ∉ subgroupPrimeSupport A := by rw [hπA]; exact fun h => hpq h.symm
  have hlen : ∀ H : Subgroup G, H ≠ ⊤ → HasPLengthLeOne p ↥H := fun H hH =>
    hasPLengthLeOne_of_not_dvd_index_comap hp (h₂ G ⟨hsimple, hna, hodd, hsolv⟩ p hp H hH)
  have hcon : IsConstrained A := isConstrained_of_maximal_plane hodd hp hAmax hAcard hA0 hsolv hlen
  have hconj := exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_natCard_eq_sq
    hna hsolv (bot_lt_iff_ne_bot.2 hA0) hAtop hcon hq hqπ hqC hp (le_refl A)
    (Subgroup.le_centralizer A (h := hAmax.prop.isMulCommutative)) hAcard hAmax.prop.pow_eq_one
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  have hSp : IsPGroup p (S : Subgroup G) := S.isPGroup'
  have hS0 : (S : Subgroup G) ≠ ⊥ := fun h => hA0 (le_bot_iff.1 (h ▸ hAS))
  have hStop : (S : Subgroup G) < ⊤ := lt_top_of_isPGroup hna hp hS0 hSp
  have hSπ : IsPiSubgroup (subgroupPrimeSupport A) (S : Subgroup G) := by
    rw [hπA]; exact (isPiSubgroup_singleton_iff hp _).2 hSp
  have hsnS : (A.subgroupOf (S : Subgroup G)).IsSubnormal :=
    have : Group.IsNilpotent (S : Subgroup G) := hSp.isNilpotent
    isSubnormal_of_finite_of_isNilpotent _
  have hsubset := (isConstrainedTransitive_of_isSubnormal hodd hsimple hna hsolv
    (bot_lt_iff_ne_bot.2 hA0) hAtop hcon hq hqπ hAS hStop hSπ hsnS hconj).1
  obtain ⟨Q₀, hQ₀⟩ := maximalNormalizedPSubgroups_nonempty (S : Subgroup G) q
  obtain ⟨c, hcK, hceq⟩ := hconj Q₀ (hsubset hQ₀) Q hQmem
  have hcC : c ∈ centralizer (A : Set G) := constrainedCentralizerCore_le_centralizer A hcK
  have hcA : (MulAut.conj c⁻¹ • A : Subgroup G) = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (centralizer_le_normalizer _ (inv_mem hcC))
  set P : Subgroup G := MulAut.conj c⁻¹ • (S : Subgroup G) with hPdef
  have hAP : A ≤ P := by
    rw [hPdef, ← hcA]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hAS
  have hQP : Q ∈ maximalNormalizedPSubgroups P q := by
    rw [hPdef, ← hceq]
    exact mem_maximalNormalizedPSubgroups_smul _ hQ₀
  have hPcoe : ((c⁻¹ • S : Sylow p G) : Subgroup G) = P := Sylow.coe_subgroup_smul
  have hPp : IsPGroup p P := hPcoe ▸ (c⁻¹ • S : Sylow p G).isPGroup'
  have hP0 : P ≠ ⊥ := fun h => hA0 (le_bot_iff.1 (h ▸ hAP))
  have hPtop : P < ⊤ := lt_top_of_isPGroup hna hp hP0 hPp
  have hPπ : IsPiSubgroup (subgroupPrimeSupport A) P := by
    rw [hπA]; exact (isPiSubgroup_singleton_iff hp _).2 hPp
  have hsnP : (A.subgroupOf P).IsSubnormal :=
    have : Group.IsNilpotent P := hPp.isNilpotent
    isSubnormal_of_finite_of_isNilpotent _
  obtain ⟨hfact, -, hcomm⟩ := normalizer_factorization_and_inf_commutator_le hodd hsimple hna
    hsolv (bot_lt_iff_ne_bot.2 hA0) hAtop hcon hq hqπ hAP hPtop hPπ hsnP hconj hQP
  have hPN : P ≤ ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ := by
    have : Fintype G := Fintype.ofFinite G
    refine h₁ G ⟨hodd, hsimple, hna, hsolv⟩ p hp P hP0 ⟨le_top, ?_⟩
    rw [Subgroup.card_top, ← hPcoe]
    exact (c⁻¹ • S : Sylow p G).card_eq_multiplicity
  refine ⟨c⁻¹ • S, hPcoe ▸ hAP, ?_, ?_⟩
  · rw [hPcoe, show CFSG.FeitThompson.Prep09.pComplCoreIn p (centralizer (P : Set G))
      = CFSG.FeitThompson.pComplCoreIn p (centralizer (P : Set G)) from
      (CFSG.FeitThompson.pComplCoreIn_eq p _).symm,
      ← constrainedCentralizerCore_eq_pComplCoreIn_centralizer hp hPp hP0]
    exact hfact
  · rw [hPcoe]
    exact le_trans (le_inf le_rfl hPN) hcomm

end

end CFSG.FeitThompson.Proofs
