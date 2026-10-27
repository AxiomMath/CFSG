module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Representations.TypeIAlternativesFrobeniusDadeCoherence
import CFSG.FeitThompson.Representations.CrossMaximalFirstWitnessValue
import CFSG.FeitThompson.Representations.DadeIntegerParameterNormBounds
import CFSG.FeitThompson.Representations.CentralActionCasesComplementOrderBound
import CFSG.FeitThompson.Representations.TypeISupportingGroupConfiguration
import CFSG.FeitThompson.Representations.TypeIIIIVChiefLayerNoncoherence
import CFSG.FeitThompson.Local.CommonPrimeFixedCoreFittingEnvelope
import CFSG.FeitThompson.Representations.TypeIFrobeniusCoherentFamily
import CFSG.FeitThompson.Representations.TypeISecondWitnessComparison
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep05
open scoped ComplexOrder Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rhoHallCore_eq (M : Subgroup G) (χ : G → ℂ) :
    letI := Fintype.ofFinite G
    rhoHallCore M χ = dadeAverage ((hallCoreOf M : Set G) \ {1}) (sigSignalizer M) χ := (rfl)

theorem rhoHall_eq' (M : Subgroup G) (χ : G → ℂ) :
    letI := Fintype.ofFinite G
    rhoHall M χ = dadeAverage (fixedSet M (hallCoreOf M)) (sigSignalizer M) χ := (rfl)

theorem isDadeData_sdiff_hallCoreOf
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M) :
    IsDadeData M ((hallCoreOf M : Set G) \ {1}) (sigSignalizer M) := by
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, -, -, hdade, -, -, -⟩ := h₇ G hG09 M hM hIM
  have hdade' : IsDadeData M (fixedSet M (hallCoreOf M)) (sigSignalizer M) := by
    rw [sigSignalizer_eq_sigmaSignalizerOn, fixedSet_eq_coreFixedSet]; exact hdade
  refine hdade'.of_subset (fun k hk => mem_fixedSet_of_mem_hallCoreOf hk.1 hk.2) ?_
  intro a ha y hy
  have haM : a ∈ M := hallCoreOf_le M ha.1
  have hnrm : ((hallCoreOf M).subgroupOf M).Normal := normal_subgroupOf_hallCoreOf M
  have hconj : (⟨y, hy⟩ : ↥M) * ⟨a, haM⟩ * (⟨y, hy⟩ : ↥M)⁻¹ ∈ (hallCoreOf M).subgroupOf M :=
    hnrm.conj_mem ⟨a, haM⟩ (Subgroup.mem_subgroupOf.2 ha.1) ⟨y, hy⟩
  have hmem : y * a * y⁻¹ ∈ hallCoreOf M := by
    have h := Subgroup.mem_subgroupOf.1 hconj
    simpa using h
  refine ⟨hmem, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hcon
  refine ha.2 ?_
  have h2 : y⁻¹ * (y * a * y⁻¹) * y = a := by group
  rw [hcon] at h2
  simp only [mul_one, inv_mul_cancel] at h2
  exact h2.symm

theorem isDadeData_fixedSet
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M) :
    IsDadeData M (fixedSet M (hallCoreOf M)) (sigSignalizer M) := by
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, -, -, hdade, -, -, -⟩ := h₇ G hG09 M hM hIM
  rw [sigSignalizer_eq_sigmaSignalizerOn, fixedSet_eq_coreFixedSet]; exact hdade

theorem isClassFun_rhoHallCore
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M)
    {Ψ : G → ℂ} (hΨ : Ψ ∈ virtualChars G) :
    IsClassFun (fun m : ↥M => rhoHallCore M Ψ (m : G)) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hD := isDadeData_sdiff_hallCoreOf h₇ hG hM hIM
  have hcf : Ψ ∈ classFun G := virtualChars_le_classFun hΨ
  refine isClassFun_iff.2 fun y m => ?_
  have hcoe : ((y * m * y⁻¹ : ↥M) : G) = (y : G) * (m : G) * (y : G)⁻¹ := by
    push_cast; rfl
  simp only [hcoe, rhoHallCore_eq]
  exact dadeAverage_conj hD hcf y.2 (m : G)

theorem rhoHallCore_apply_eq_rhoHall_apply (M : Subgroup G) (Ψ : G → ℂ) {k : G}
    (hk : k ∈ hallCoreOf M) (hk1 : k ≠ 1) : rhoHallCore M Ψ k = rhoHall M Ψ k := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  rw [rhoHallCore_eq, rhoHall_eq',
    dadeAverage_apply_of_mem (A := (hallCoreOf M : Set G) \ {1}) ⟨hk, hk1⟩,
    dadeAverage_apply_of_mem (A := fixedSet M (hallCoreOf M))
      (mem_fixedSet_of_mem_hallCoreOf hk hk1)]

theorem fixedSet_eq_sdiff_of_frobenius {N E : Subgroup G}
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E) :
    fixedSet N (hallCoreOf N) = (hallCoreOf N : Set G) \ {1} := by
  have _ : ((hallCoreOf N).subgroupOf N).Normal := normal_subgroupOf_hallCoreOf N
  have hfreeG : ∀ u ∈ E, u ≠ 1 → hallCoreOf N ⊓ centralizer ({u} : Set G) = ⊥ :=
    fun u hu hu1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hfree hu hu1
  ext a
  simp only [mem_fixedSet, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    centralizerIn_eq, centralizer_coe_zpowers]
  constructor
  · rintro ⟨haN, ha1, hcent⟩
    refine ⟨?_, ha1⟩
    by_contra hnot
    exact hcent (inf_centralizer_singleton_eq_bot_of_mem_of_notMem hsemi.coe_eq_mul.symm
      hsemi.inf_eq_bot hfreeG haN hnot)
  · rintro ⟨haH, ha1⟩
    refine ⟨hallCoreOf_le N haH, ha1, fun hbot => ha1 ?_⟩
    have hmem : a ∈ hallCoreOf N ⊓ centralizer ({a} : Set G) :=
      ⟨haH, mem_centralizer_singleton_iff.2 rfl⟩
    rw [hbot] at hmem
    simpa using hmem

theorem isSetup_of_frobenius
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {N : Subgroup G} (hN : IsCoatom N) (hIN : IsTypeI N)
    {E : Subgroup G} (hEN : E ≤ N) (hEbot : E ≠ ⊥)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E) :
    letI : Fintype G := Fintype.ofFinite G
    FrobeniusDade.IsSetup N (hallCoreOf N) E (sigSignalizer N) := by
  let _ : Fintype G := Fintype.ofFinite G
  exact
    { odd_card := (odd_natCard_lt_natCard_of_ne_top hG.odd_natCard hN.1).2
      le_left := hallCoreOf_le N
      le_right := hEN
      le_normalizer := hsemi.le_normalizer
      sup_eq := hsemi.sup_eq
      inf_eq_bot := hsemi.inf_eq_bot
      ne_bot_left := hallCoreOf_ne_bot hIN
      ne_bot_right := hEbot
      free := fun u hu hu1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hfree hu hu1
      isNilpotent := isNilpotent_hallCoreOf N
      isDadeData := isDadeData_sdiff_hallCoreOf h₇ hG hN hIN }

theorem hallIndFam_eq_indFam (N : Subgroup G) :
    letI : Fintype ↥N := Fintype.ofFinite _
    hallIndFam N
      = indFam ((hallCoreOf N).subgroupOf N) (nonprincipalIrr ↥((hallCoreOf N).subgroupOf N)) := by
  let _ : Fintype ↥N := Fintype.ofFinite _
  have hle : hallCoreOf N ≤ N := hallCoreOf_le N
  ext f
  simp only [hallIndFam, Set.mem_image, Set.mem_ofPred_eq, mem_indFam, mem_nonprincipalIrr]
  constructor
  · rintro ⟨θ, ⟨hθ, hθ1⟩, rfl⟩
    refine ⟨θ ∘ (Subgroup.subgroupOfEquivOfLe hle), ⟨?_, ?_⟩, ?_⟩
    · exact FrobeniusInduction.mem_Irr_comp_mulEquiv hθ (Subgroup.subgroupOfEquivOfLe hle)
    · intro hcon
      refine hθ1 ?_
      funext y
      have h := congrFun hcon ((Subgroup.subgroupOfEquivOfLe hle).symm y)
      simpa using h
    · exact (indBetween_eq_indClassFun N _ hle θ).symm
  · rintro ⟨ψ, ⟨hψ, hψ1⟩, rfl⟩
    refine ⟨ψ ∘ (Subgroup.subgroupOfEquivOfLe hle).symm, ⟨?_, ?_⟩, ?_⟩
    · exact FrobeniusInduction.mem_Irr_comp_mulEquiv hψ (Subgroup.subgroupOfEquivOfLe hle).symm
    · intro hcon
      refine hψ1 ?_
      funext y
      have h := congrFun hcon ((Subgroup.subgroupOfEquivOfLe hle) y)
      simpa using h
    · rw [indBetween_eq_indClassFun N _ hle]
      congr 1

theorem finite_hallIndFam (N : Subgroup G) : (hallIndFam N).Finite := by
  classical
  let _ : Fintype ↥N := Fintype.ofFinite _
  have himg : indFam ((hallCoreOf N).subgroupOf N)
      (nonprincipalIrr ↥((hallCoreOf N).subgroupOf N))
      = indClassFun ((hallCoreOf N).subgroupOf N) ''
        (nonprincipalIrr ↥((hallCoreOf N).subgroupOf N)) := by
    ext f
    rw [mem_indFam, Set.mem_image]
  rw [hallIndFam_eq_indFam N, himg]
  exact Set.Finite.image _
    ((finite_Irr (G := ↥((hallCoreOf N).subgroupOf N))).subset
      (fun χ hχ => (mem_nonprincipalIrr.1 hχ).1))

theorem sdiff_eq_image_subgroupOf (N : Subgroup G) :
    ((hallCoreOf N : Set G) \ {1})
      = (fun x : ↥N => (x : G)) '' (((hallCoreOf N).subgroupOf N : Set ↥N) \ {1}) := by
  ext g
  refine ⟨?_, ?_⟩
  · rintro ⟨hg, hg1⟩
    refine ⟨⟨g, hallCoreOf_le N hg⟩, ⟨Subgroup.mem_subgroupOf.2 hg, ?_⟩, rfl⟩
    simp only [Set.mem_singleton_iff]
    intro hcon
    exact hg1 (OneMemClass.coe_eq_one.mpr hcon)
  · rintro ⟨y, ⟨hy, hy1⟩, rfl⟩
    refine ⟨Subgroup.mem_subgroupOf.1 hy, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hcon
    exact hy1 (OneMemClass.coe_eq_one.mp hcon)

theorem isTypeI_alternatives {N E : Subgroup G} (hIN : IsTypeI N) (hEN : E ≤ N)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E) :
    ((∀ g : G, (fun x => g⁻¹ * x * g) '' ((hallCoreOf N : Set G) \ {1})
          = (hallCoreOf N : Set G) \ {1} ↔ g ∈ N) ∧
        ∀ g ∉ N, ((hallCoreOf N : Set G) \ {1}) ∩
          (fun x => g⁻¹ * x * g) '' ((hallCoreOf N : Set G) \ {1}) = ∅) ∨
      IsMulCommutative ↥(hallCoreOf N) ∨
      ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(hallCoreOf N) → Monoid.exponent ↥E ∣ p - 1 := by
  have hsub : (hallCoreOf N).subgroupOf N = hallCore ↥N := subgroupOf_hallCoreOf N
  have hsharp : hallCoreSharp N = (hallCoreOf N : Set G) \ {1} := by
    rw [hallCoreSharp_eq, hallCoreOf_eq]
  obtain ⟨E₀, hFrob, halt⟩ := hIN.exists_isFrobeniusType
  rcases halt with hti | ⟨habel, -⟩ | ⟨hexp, -⟩
  · refine Or.inl ⟨fun g => ?_, fun g hg => ?_⟩
    · rw [← hsharp, ← mem_normalizer_iff_conjInv_image_eq, hti.normalizer_eq]
    · rw [← hsharp]
      exact Set.disjoint_iff_inter_eq_empty.1 (hti.disjoint_image_conj_inv hg)
  · refine Or.inr (Or.inl ?_)
    have := habel
    rw [hallCoreOf_eq]
    infer_instance
  · refine Or.inr (Or.inr fun p hp hpd => ?_)
    have hexpE₀ : Monoid.exponent ↥E₀ = Monoid.exponent ↥E := by
      have hn : (hallCore ↥N).Normal := hallCore_normal
      have h1 : (↥N ⧸ hallCore ↥N) ≃* ↥E₀ := hFrob.isComplement'.symm.QuotientMulEquiv
      have hcompl : (hallCore ↥N).IsComplement' (E.subgroupOf N) :=
        hsub ▸ isComplement'_subgroupOf_of_isInternalSemidirectProduct hsemi
      have h2 : (↥N ⧸ hallCore ↥N) ≃* ↥(E.subgroupOf N) := hcompl.symm.QuotientMulEquiv
      rw [(Monoid.exponent_eq_of_mulEquiv h1).symm.trans (Monoid.exponent_eq_of_mulEquiv h2),
        Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEN)]
    rw [← hexpE₀]
    exact hexp p (Nat.mem_primeFactors.2 ⟨hp, (natCard_hallCoreOf N) ▸ hpd, Nat.card_pos.ne'⟩)

theorem relIndex_hallCoreOf_eq_natCard {N E : Subgroup G}
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E) :
    (hallCoreOf N).relIndex N = Nat.card ↥E := by
  have h1 : Nat.card ↥(hallCoreOf N) * (hallCoreOf N).relIndex N = Nat.card ↥N := by
    rw [Subgroup.relIndex,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hallCoreOf_le N)).toEquiv]
    exact Subgroup.card_mul_index _
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans hsemi.natCard_eq_mul)

theorem exists_mem_hallIndFam_degree
    {N : Subgroup G} (hIN : IsTypeI N) {E : Subgroup G}
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E) :
    ∃ ζ : ↥N → ℂ, ζ ∈ hallIndFam N ∧ ζ ∈ Irr ↥N ∧ ζ 1 = (Nat.card ↥E : ℂ) := by
  classical
  let _ : Fintype ↥N := Fintype.ofFinite _
  have hsub : (hallCoreOf N).subgroupOf N = hallCore ↥N := subgroupOf_hallCoreOf N
  have hK : ((hallCoreOf N).subgroupOf N).Normal := normal_subgroupOf_hallCoreOf N
  have hsolv : Group.IsSolvable ↥((hallCoreOf N).subgroupOf N) :=
    hsub ▸ (inferInstance : Group.IsSolvable ↥(hallCore ↥N))
  have hne : (hallCoreOf N).subgroupOf N ≠ ⊥ := hsub ▸ hIN.hallCore_ne_bot
  have hcompl : ((hallCoreOf N).subgroupOf N).IsComplement' (E.subgroupOf N) :=
    isComplement'_subgroupOf_of_isInternalSemidirectProduct hsemi
  have hC' : ∀ u ∈ E.subgroupOf N, u ≠ 1 →
      (hallCoreOf N).subgroupOf N ⊓ Subgroup.centralizer {u} = ⊥ :=
    free_subgroupOf (hallCoreOf_le N)
      (fun v hv hv1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hfree hv hv1)
  obtain ⟨θ, hθ, hθne, -, hθirr, hdeg⟩ :=
    exists_mem_Irr_indClassFun_mem_Irr_index (H := (hallCoreOf N).subgroupOf N)
      (E := E.subgroupOf N) hne hcompl.mul_eq (disjoint_iff.1 hcompl.disjoint) hC'
  refine ⟨indClassFun ((hallCoreOf N).subgroupOf N) θ, ?_, hθirr, ?_⟩
  · rw [hallIndFam_eq_indFam N]
    exact (mem_indFam _).2 ⟨θ, mem_nonprincipalIrr.2 ⟨hθ, hθne⟩, rfl⟩
  · rw [hdeg, ← Subgroup.relIndex, relIndex_hallCoreOf_eq_natCard hsemi]

theorem exists_mem_hallIndFam_isCoherentAt
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {N : Subgroup G} (hN : IsCoatom N) (hIN : IsTypeI N)
    {E : Subgroup G} (hEN : E ≤ N) (hEbot : E ≠ ⊥)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E) :
    ∃ ζ : ↥N → ℂ, ζ ∈ hallIndFam N ∧ ζ ∈ Irr ↥N ∧ ζ 1 = (Nat.card ↥E : ℂ) ∧
      ∃ _hζ : ζ ∈ Submodule.span ℤ (hallIndFam N),
      ∃ ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ),
        IsCoherentAt N (hallIndFam N) (tauHall N) ν := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ↥N := Fintype.ofFinite _
  obtain ⟨ζ, hζS, hζIrr, hζ1⟩ := exists_mem_hallIndFam_degree hIN hsemi hfree
  refine ⟨ζ, hζS, hζIrr, hζ1, Submodule.subset_span hζS, ?_⟩
  have hc := isSetup_of_frobenius h₇ hG hN hIN hEN hEbot hsemi hfree
  have hfam : hc.family = hallIndFam N := (hallIndFam_eq_indFam N).symm
  have hcast : ∀ f : ↥N → ℂ, f ∈ Submodule.span ℤ (hallIndFam N) →
      f ∈ Submodule.span ℤ hc.family := fun f hf => by rw [hfam]; exact hf
  obtain ⟨ν₀, hν₀⟩ := isCoherent_iff.1 (hc.isCoherent_tau (isTypeI_alternatives hIN hEN hsemi))
  refine ⟨AddMonoidHom.mk'
    (fun f => (ν₀ ⟨(f : ↥N → ℂ), hcast (f : ↥N → ℂ) f.2⟩ : G → ℂ)) ?_, ?_, ?_, ?_⟩
  · intro f g
    have h : (⟨((f + g : Submodule.span ℤ (hallIndFam N)) : ↥N → ℂ),
          hcast _ (f + g).2⟩ : Submodule.span ℤ hc.family)
        = ⟨(f : ↥N → ℂ), hcast _ f.2⟩ + ⟨(g : ↥N → ℂ), hcast _ g.2⟩ := rfl
    rw [h, map_add]
    rfl
  · intro f
    exact (ν₀ _).2
  · intro f g
    simp only [AddMonoidHom.mk'_apply]
    rw [cfIP_eq_cfInner, cfIP_eq_cfInner]
    exact hν₀.inner_eq _ _
  · intro f hf1
    simp only [AddMonoidHom.mk'_apply]
    have hf0 : (f : ↥N → ℂ) ∈ charSpanZero hc.family :=
      mem_charSpanZero.2 ⟨hcast _ f.2, hf1⟩
    have hz : (⟨(f : ↥N → ℂ), hcast _ f.2⟩ : Submodule.span ℤ hc.family)
        = Submodule.inclusion (charSpanZero_le hc.family) ⟨(f : ↥N → ℂ), hf0⟩ := rfl
    rw [hz, hν₀.eq_on_zero, hc.coe_tau, tauHall,
      fixedSet_eq_sdiff_of_frobenius hsemi hfree, extendZero_eq_extendByZero]
    exact dadeMapFun_eq_dadeSupportExtension hc.isDadeData
      (hc.mem_dadeDomain_of_mem_charSpanZero hc.family_subset_indFam_Irr hf0)

theorem centralizer_le_normalizer_zpowers (x : G) :
    centralizer ({x} : Set G) ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have hgx : Commute g x := mem_centralizer_singleton_iff.1 hg
  have key : ∀ k : ℤ, g * x ^ k * g⁻¹ = x ^ k := by
    intro k; rw [(hgx.zpow_right k).eq]; group
  have key2 : ∀ k : ℤ, g⁻¹ * x ^ k * g = x ^ k := by
    intro k
    calc g⁻¹ * x ^ k * g = g⁻¹ * (g * x ^ k * g⁻¹) * g := by rw [key k]
      _ = x ^ k := by group
  intro n
  refine ⟨?_, ?_⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, by rw [key k]⟩
  · rintro ⟨k, hk⟩
    have hk' : x ^ k = g * n * g⁻¹ := hk
    refine ⟨k, ?_⟩
    change x ^ k = n
    have hn : n = g⁻¹ * (x ^ k) * g := by rw [hk']; group
    rw [hn, key2 k]

theorem zpowers_pow_eq {p a : ℕ} (hp : p.Prime) {x : G} (hxord : orderOf x = p)
    (ha1 : 1 ≤ a) (ha2 : a ≤ p - 1) : zpowers (x ^ a) = zpowers x := by
  have hap : a < p := by have := hp.two_le; omega
  have hcop : Nat.Coprime p a := (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega)
  have hord : orderOf (x ^ a) = p := by
    rw [orderOf_pow, hxord, Nat.Coprime.gcd_eq_one hcop, Nat.div_one]
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_)
  · exact (Subgroup.zpowers_le).2 (pow_mem (Subgroup.mem_zpowers x) a)
  · rw [Nat.card_zpowers, Nat.card_zpowers, hord, hxord]

theorem p_ge_three (hG : IsMinimalSimpleOdd G) {p : ℕ} (hp : p.Prime) {x : G}
    (hxord : orderOf x = p) : 3 ≤ p := by
  have hdvd : p ∣ Nat.card G := by rw [← hxord]; exact orderOf_dvd_natCard x
  have hodd := hG.odd_natCard
  rw [Nat.odd_iff] at hodd
  have hp2 : p ≠ 2 := by intro h2; rw [h2] at hdvd; omega
  have := hp.two_le
  rcases Nat.lt_or_ge p 3 with hlt | hge
  · omega
  · exact hge

theorem sigSignalizer_eq_inf
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {N : Subgroup G} (hN : IsCoatom N) (hIN : IsTypeI N)
    {M : Subgroup G} (hM : IsCoatom M)
    {y : G} (hyJ : y ∈ hallCoreOf N) (hy1 : y ≠ 1)
    (hcy : ¬ centralizer ({y} : Set G) ≤ N) (hcM : centralizer ({y} : Set G) ≤ M) :
    sigSignalizer N y = hallCoreOf M ⊓ centralizer ({y} : Set G) := by
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, -, -, -, -, -, hiv⟩ := h₇ G hG09 N hN hIN
  have hyA : y ∈ Prep09.coreFixedSet (Prep09.hallCoreIn N) N := by
    rw [← fixedSet_eq_coreFixedSet]
    exact mem_fixedSet_of_mem_hallCoreOf hyJ hy1
  obtain ⟨-, T, hT, -, -, -, -, -, hsig, -⟩ := hiv y hyA hcy
  have hTM : M = T := hT.eq_of_isCoatom hM hcM
  subst hTM
  rw [sigSignalizer_eq_sigmaSignalizerOn, hsig]
  rfl

theorem sigSignalizer_ne_bot
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {N : Subgroup G} (hN : IsCoatom N) (hIN : IsTypeI N)
    {y : G} (hyJ : y ∈ hallCoreOf N) (hy1 : y ≠ 1)
    (hcy : ¬ centralizer ({y} : Set G) ≤ N) :
    sigSignalizer N y ≠ ⊥ := by
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, hstr, -, -, -, -, -⟩ := h₇ G hG09 N hN hIN
  have hyA : y ∈ Prep09.coreFixedSet (Prep09.hallCoreIn N) N := by
    rw [← fixedSet_eq_coreFixedSet]
    exact mem_fixedSet_of_mem_hallCoreOf hyJ hy1
  obtain ⟨-, -, hprod, -⟩ := hstr y hyA
  rw [sigSignalizer_eq_sigmaSignalizerOn]
  intro hbot
  refine hcy fun g hg => ?_
  have hg' : g ∈ ((Prep09.sigmaSignalizerOn N y : Set G) * (Prep09.centIn N {y} : Set G)) := by
    rw [hprod]; exact hg
  obtain ⟨q, hq, r, hr, rfl⟩ := Set.mem_mul.1 hg'
  have hq1 : q = 1 := by rw [hbot] at hq; simpa using hq
  subst hq1
  simpa using (hr.1 : r ∈ N)

theorem dadeAverage_eq_of_forall (A : Set G) (R : G → Subgroup G) (χ : G → ℂ) {y : G}
    (hy : y ∈ A) (hconst : ∀ r ∈ R y, χ (r * y) = χ y) :
    letI := Fintype.ofFinite G
    dadeAverage A R χ y = χ y := by
  classical
  let _ := Fintype.ofFinite G
  rw [dadeAverage_apply_of_mem hy]
  have hsum : ∑ u : ↥(R y), χ ((u : G) * y) = (Nat.card ↥(R y) : ℂ) * χ y := by
    rw [Finset.sum_congr rfl (fun (v : ↥(R y)) _ => hconst (v : G) v.2)]
    simp [Nat.card_eq_fintype_card, mul_comm]
  rw [hsum]
  have hpos : (Nat.card ↥(R y) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥(R y))).ne'
  field_simp

theorem dadeAverage_apply_eq_zeta
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {N : Subgroup G} (hN : IsCoatom N) (hIN : IsTypeI N)
    {E : Subgroup G} (hEN : E ≤ N) (hEbot : E ≠ ⊥)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E)
    {p h e : ℕ} (hh : h = Nat.card ↥(hallCoreOf N)) (he : e = Nat.card ↥E)
    (hp3 : 3 ≤ p) (hph : p ^ 2 ≤ h) (hep : 2 * e ≤ p + 1)
    {ζ : ↥N → ℂ} (hζS : ζ ∈ hallIndFam N) (hζIrr : ζ ∈ Irr ↥N) (hζ1 : ζ 1 = (e : ℂ))
    (hζ : ζ ∈ Submodule.span ℤ (hallIndFam N))
    {ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ)}
    (hν : IsCoherentAt N (hallIndFam N) (tauHall N) ν)
    {Ψ : G → ℂ} (hΨ : Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ))
    {y : G} (hyJ : y ∈ hallCoreOf N) (hy1 : y ≠ 1) :
    rhoHallCore N Ψ y = ζ ⟨y, hallCoreOf_le N hyJ⟩ := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ↥N := Fintype.ofFinite _
  have hHn : ((hallCoreOf N).subgroupOf N).Normal := normal_subgroupOf_hallCoreOf N
  have hfin : Finite ↥(hallIndFam N) := (finite_hallIndFam N).to_subtype
  have hACC : ambientCoreCentralizerSupport ((hallCoreOf N).subgroupOf N)
      = fixedSet N (hallCoreOf N) := by
    rw [fixedSet_eq_ambientCoreCentralizerSupport, subgroupOf_hallCoreOf]
  have hD : IsDadeData N (ambientCoreCentralizerSupport ((hallCoreOf N).subgroupOf N))
      (sigSignalizer N) := by
    rw [hACC]; exact isDadeData_fixedSet h₇ hG hN hIN
  have hAP : ambientPuncturedCore ((hallCoreOf N).subgroupOf N)
      = (hallCoreOf N : Set G) \ {1} :=
    (ambientPuncturedCore_eq_image hD rfl).trans (sdiff_eq_image_subgroupOf N).symm
  set ξ : ↥(hallIndFam N) → (↥N → ℂ) := fun k => (k : ↥N → ℂ) with hξdef
  have hrange : Set.range ξ = hallIndFam N := Subtype.range_coe
  have hcast : ∀ f : ↥N → ℂ, f ∈ Submodule.span ℤ (Set.range ξ) →
      f ∈ Submodule.span ℤ (hallIndFam N) := by
    intro f hf; rwa [hrange] at hf
  have hadd : ∀ f g : ↥(Submodule.span ℤ (Set.range ξ)),
      (⟨((f + g : ↥(Submodule.span ℤ (Set.range ξ))) : ↥N → ℂ), hcast _ (f + g).2⟩ :
          ↥(Submodule.span ℤ (hallIndFam N)))
        = ⟨(f : ↥N → ℂ), hcast _ f.2⟩ + ⟨(g : ↥N → ℂ), hcast _ g.2⟩ := fun f g => rfl
  let ν' : ↥(Submodule.span ℤ (Set.range ξ)) →+ ↥(virtualChars G) :=
    AddMonoidHom.mk' (fun f => ⟨ν ⟨(f : ↥N → ℂ), hcast _ f.2⟩, hν.mem_virtualChars _⟩) (by
      intro f g
      apply Subtype.ext
      change (ν ⟨((f + g : ↥(Submodule.span ℤ (Set.range ξ))) : ↥N → ℂ), _⟩ : G → ℂ) = _
      rw [hadd f g, map_add]
      rfl)
  let τ' : ↥(charSpanZero (Set.range ξ)) →+ ↥(virtualChars G) :=
    ν'.comp (Submodule.inclusion (charSpanZero_le (Set.range ξ))).toAddMonoidHom
  have hνc : IsCoherentWith (Set.range ξ) τ' ν' := by
    refine ⟨?_, ?_⟩
    · intro f g
      change cfInner (ν ⟨(f : ↥N → ℂ), _⟩ : G → ℂ) (ν ⟨(g : ↥N → ℂ), _⟩ : G → ℂ)
        = cfInner (f : ↥N → ℂ) (g : ↥N → ℂ)
      rw [← cfIP_eq_cfInner, ← cfIP_eq_cfInner]
      exact hν.isometry _ _
    · intro f
      rfl
  have hτ : ∀ (f : ↥(charSpanZero (Set.range ξ)))
      (F : ↥(dadeDomain N (ambientCoreCentralizerSupport ((hallCoreOf N).subgroupOf N)))),
      (f : ↥N → ℂ) = (F : ↥N → ℂ) → ((τ' f : ↥(virtualChars G)) : G → ℂ)
        = ((dadeMap hD F : ↥(classFun G)) : G → ℂ) := by
    intro f F hfF
    have hmem := mem_charSpanZero.1 f.2
    have h0 : (ν ⟨(f : ↥N → ℂ), hcast _ hmem.1⟩ : G → ℂ) = tauHall N (f : ↥N → ℂ) :=
      hν.eq_tau ⟨(f : ↥N → ℂ), hcast _ hmem.1⟩ hmem.2
    change (ν ⟨(f : ↥N → ℂ), _⟩ : G → ℂ) = _
    rw [h0, coe_dadeMap hD F, ← hfF, tauHall_eq_dadeMapFun, ← hACC]
  have hnp : nonprincipalIrr ↥((hallCoreOf N).subgroupOf N)
      = Irr ↥((hallCoreOf N).subgroupOf N) \ {1} := by
    ext χ
    rw [mem_nonprincipalIrr]
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  have hS : Set.range ξ
      = indFam ((hallCoreOf N).subgroupOf N) (Irr ↥((hallCoreOf N).subgroupOf N) \ {1}) := by
    rw [hrange, hallIndFam_eq_indFam N, hnp]
  have hinj : Function.Injective ξ := fun a b hab => Subtype.ext hab
  have hc := isSetup_of_frobenius h₇ hG hN hIN hEN hEbot hsemi hfree
  have hS2 : (Set.range ξ).Nontrivial := by
    rw [hrange, hallIndFam_eq_indFam N]; exact hc.family_nontrivial
  have hcard : Nat.card ↥((hallCoreOf N).subgroupOf N) = Nat.card ↥(hallCoreOf N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hallCoreOf_le N)).toEquiv
  have hidx : ((hallCoreOf N).subgroupOf N).index = Nat.card ↥E := by
    rw [← relIndex_hallCoreOf_eq_natCard hsemi]; rfl
  have hζ1' : ξ ⟨ζ, hζS⟩ 1 = (((hallCoreOf N).subgroupOf N).index : ℂ) := by
    rw [hidx, ← he]; exact hζ1
  have key := dadeAverage_ambientPuncturedCore_coherentImage_eq
    (H := (hallCoreOf N).subgroupOf N) (ξ := ξ) (k₀ := ⟨ζ, hζS⟩) (τ := τ') (ν := ν')
    hD hS hinj hνc hτ hζIrr hζ1' hS2 (p := (p : ℤ)) (by exact_mod_cast hp3)
    (by rw [hcard, ← hh]; exact_mod_cast hph)
    (by rw [hidx, ← he]; exact_mod_cast hep)
    (x := ⟨y, hallCoreOf_le N hyJ⟩) (Subgroup.mem_subgroupOf.2 hyJ)
    (by simp only [ne_eq, Subtype.ext_iff]; simpa using hy1)
  have himg : CrossFamilyProjection.coherentImage ξ ν' ⟨ζ, hζS⟩ = Ψ := by
    rw [CrossFamilyProjection.coherentImage_apply, hΨ]
    rfl
  rw [himg, hAP] at key
  rw [rhoHallCore_eq, key]

theorem coherentImage_apply_mul_eq_of_cross_maximal
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_complement_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M N : Subgroup G} (hM : IsCoatom M) (hN : IsCoatom N)
    (hIM : IsTypeI M) (hIN : IsTypeI N)
    {E : Subgroup G} (hEN : E ≤ N) (hEbot : E ≠ ⊥)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E)
    (hnotFrob : ¬ ∃ B : Subgroup G, B ≤ M ∧
      FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) B ∧
      IsFixedPointFreeOn (hallCoreOf M) B)
    {p : ℕ} (hp : p.Prime) {x : G} (hxJ : x ∈ hallCoreOf N) (hx1 : x ≠ 1) (hxM : x ∈ M)
    (hxK : x ∉ hallCoreOf M) (hxord : orderOf x = p)
    (hnorm : normalizer ((zpowers x : Subgroup G) : Set G) ≤ M)
    (hcent : ¬ centralizer ({x} : Set G) ≤ N)
    {h e : ℕ} (hh : h = Nat.card ↥(hallCoreOf N)) (he : e = Nat.card ↥E)
    (hph : p ^ 2 ≤ h) (hep : 2 * e ≤ p + 1)
    {ζ : ↥N → ℂ} (hζS : ζ ∈ hallIndFam N) (hζIrr : ζ ∈ Irr ↥N) (hζ1 : ζ 1 = (e : ℂ))
    (hζ : ζ ∈ Submodule.span ℤ (hallIndFam N))
    {ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ)}
    (hν : IsCoherentAt N (hallIndFam N) (tauHall N) ν)
    {Ψ : G → ℂ} (hΨ : Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ)) :
    ∀ a : ℕ, 1 ≤ a → a ≤ p - 1 → ∀ k ∈ hallCoreOf M,
      ∀ hxa : x ^ a ∈ N, Ψ (x ^ a * k) = ζ ⟨x ^ a, hxa⟩ := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hp3 : 3 ≤ p := p_ge_three hG hp hxord
  have hΨmem : Ψ ∈ virtualChars G := by rw [hΨ]; exact hν.mem_virtualChars _
  have hΨcf : Ψ ∈ classFun G := virtualChars_le_classFun hΨmem
  have hmul : ∀ y ∈ fixedSet M (hallCoreOf M), y ∉ hallCoreOf M →
      ∀ k ∈ hallCoreOf M, Ψ (y * k) = Ψ y := fun y hy hyK k hk =>
    coherentImage_apply_mul_hallCoreOf_eq h₁ h₂ h₃ h₄ h₅ h₆ h₇
      hG hN hIN hEN hEbot hsemi hfree hν hζS hζIrr hζ hΨ hM hIM hnotFrob hy hyK k hk
  intro a ha1 ha2 k hk hxa
  have hzp : zpowers (x ^ a) = zpowers x := zpowers_pow_eq hp hxord ha1 ha2
  have hyJ : x ^ a ∈ hallCoreOf N := pow_mem hxJ a
  have hxzp : x ∈ zpowers (x ^ a) := by rw [hzp]; exact Subgroup.mem_zpowers x
  have hy1 : x ^ a ≠ 1 := by
    intro hcon
    have hb : zpowers (x ^ a) = ⊥ := by rw [hcon]; exact Subgroup.zpowers_one_eq_bot
    rw [hb] at hxzp
    exact hx1 (by simpa using hxzp)
  have hcentyx : centralizer ({x ^ a} : Set G) = centralizer ({x} : Set G) := by
    rw [← centralizer_coe_zpowers, ← centralizer_coe_zpowers, hzp]
  have hcy : ¬ centralizer ({x ^ a} : Set G) ≤ N := by rw [hcentyx]; exact hcent
  have hcM : centralizer ({x ^ a} : Set G) ≤ M := by
    rw [hcentyx]
    exact le_trans (centralizer_le_normalizer_zpowers x) hnorm
  have hyM : x ^ a ∈ M := pow_mem hxM a
  have hyK : x ^ a ∉ hallCoreOf M := fun hcon => hxK ((Subgroup.zpowers_le).2 hcon hxzp)
  have hsig := sigSignalizer_eq_inf h₇ hG hN hIN hM hyJ hy1 hcy hcM
  have hsigne := sigSignalizer_ne_bot h₇ hG hN hIN hyJ hy1 hcy
  have hyfix : x ^ a ∈ fixedSet M (hallCoreOf M) := by
    refine mem_fixedSet.2 ⟨hyM, hy1, ?_⟩
    rw [centralizerIn_eq, centralizer_coe_zpowers, ← hsig]
    exact hsigne
  have hconst : ∀ r ∈ sigSignalizer N (x ^ a), Ψ (r * (x ^ a)) = Ψ (x ^ a) := by
    intro r hr
    rw [hsig] at hr
    have hconj : IsConj (r * x ^ a) (x ^ a * r) := by
      refine ⟨⟨x ^ a, (x ^ a)⁻¹, by group, by group⟩, ?_⟩
      simp only [SemiconjBy]
      group
    rw [classFun.apply_eq_of_isConj hΨcf hconj, hmul (x ^ a) hyfix hyK r hr.1]
  have hval : Ψ (x ^ a) = ζ ⟨x ^ a, hallCoreOf_le N hyJ⟩ := by
    have hrho := dadeAverage_apply_eq_zeta h₇ hG hN hIN hEN hEbot hsemi hfree hh he hp3 hph hep
      hζS hζIrr hζ1 hζ hν hΨ hyJ hy1
    rw [← hrho, rhoHallCore_eq]
    exact (dadeAverage_eq_of_forall ((hallCoreOf N : Set G) \ {1}) (sigSignalizer N) Ψ
      ⟨hyJ, by simpa using hy1⟩ hconst).symm
  rw [hmul (x ^ a) hyfix hyK k hk, hval]

theorem one_sub_div_le_cfIP_rhoHallCore
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {N : Subgroup G} (hN : IsCoatom N) (hIN : IsTypeI N)
    {E : Subgroup G} (hEN : E ≤ N) (hEbot : E ≠ ⊥)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E)
    {h e : ℕ} (hh : h = Nat.card ↥(hallCoreOf N)) (he : e = Nat.card ↥E)
    {ζ : ↥N → ℂ} (hζS : ζ ∈ hallIndFam N) (hζIrr : ζ ∈ Irr ↥N) (hζ1 : ζ 1 = (e : ℂ))
    (hζ : ζ ∈ Submodule.span ℤ (hallIndFam N))
    {ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ)}
    (hν : IsCoherentAt N (hallIndFam N) (tauHall N) ν)
    {Ψ : G → ℂ} (hΨ : Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ)) :
    1 - (e : ℂ) / (h : ℂ) ≤
      cfIP (fun n : ↥N => rhoHallCore N Ψ (n : G)) (fun n : ↥N => rhoHallCore N Ψ (n : G)) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ↥N := Fintype.ofFinite _
  have hHn : ((hallCoreOf N).subgroupOf N).Normal := normal_subgroupOf_hallCoreOf N
  have hsub : (hallCoreOf N).subgroupOf N = hallCore ↥N := subgroupOf_hallCoreOf N
  have hD : IsDadeData N ((hallCoreOf N : Set G) \ {1}) (sigSignalizer N) :=
    isDadeData_sdiff_hallCoreOf h₇ hG hN hIN
  have hA : ((hallCoreOf N : Set G) \ {1})
      = (fun x : ↥N => (x : G)) '' (((hallCoreOf N).subgroupOf N : Set ↥N) \ {1}) :=
    sdiff_eq_image_subgroupOf N
  set ξ : ↥(hallIndFam N) → (↥N → ℂ) := fun k => (k : ↥N → ℂ) with hξdef
  have hrange : Set.range ξ = hallIndFam N := Subtype.range_coe
  have hcast : ∀ f : ↥N → ℂ, f ∈ Submodule.span ℤ (Set.range ξ) →
      f ∈ Submodule.span ℤ (hallIndFam N) := by
    intro f hf; rwa [hrange] at hf
  have hadd : ∀ f g : ↥(Submodule.span ℤ (Set.range ξ)),
      (⟨((f + g : ↥(Submodule.span ℤ (Set.range ξ))) : ↥N → ℂ), hcast _ (f + g).2⟩ :
          ↥(Submodule.span ℤ (hallIndFam N)))
        = ⟨(f : ↥N → ℂ), hcast _ f.2⟩ + ⟨(g : ↥N → ℂ), hcast _ g.2⟩ := fun f g => rfl
  let ν' : ↥(Submodule.span ℤ (Set.range ξ)) →+ ↥(virtualChars G) :=
    AddMonoidHom.mk' (fun f => ⟨ν ⟨(f : ↥N → ℂ), hcast _ f.2⟩, hν.mem_virtualChars _⟩) (by
      intro f g
      apply Subtype.ext
      change (ν ⟨((f + g : ↥(Submodule.span ℤ (Set.range ξ))) : ↥N → ℂ), _⟩ : G → ℂ) = _
      rw [hadd f g, map_add]
      rfl)
  let τ' : ↥(charSpanZero (Set.range ξ)) →+ ↥(virtualChars G) :=
    ν'.comp (Submodule.inclusion (charSpanZero_le (Set.range ξ))).toAddMonoidHom
  have hνc : IsCoherentWith (Set.range ξ) τ' ν' := by
    refine ⟨?_, ?_⟩
    · intro f g
      change cfInner (ν ⟨(f : ↥N → ℂ), _⟩ : G → ℂ) (ν ⟨(g : ↥N → ℂ), _⟩ : G → ℂ)
        = cfInner (f : ↥N → ℂ) (g : ↥N → ℂ)
      rw [← cfIP_eq_cfInner, ← cfIP_eq_cfInner]
      exact hν.isometry _ _
    · intro f
      rfl
  have hτ : ∀ (f : ↥(charSpanZero (Set.range ξ)))
      (F : ↥(dadeDomain N ((hallCoreOf N : Set G) \ {1}))),
      (f : ↥N → ℂ) = (F : ↥N → ℂ) → ((τ' f : ↥(virtualChars G)) : G → ℂ)
        = ((dadeMap hD F : ↥(classFun G)) : G → ℂ) := by
    intro f F hfF
    have hmem := mem_charSpanZero.1 f.2
    have h0 : (ν ⟨(f : ↥N → ℂ), hcast _ hmem.1⟩ : G → ℂ) = tauHall N (f : ↥N → ℂ) :=
      hν.eq_tau ⟨(f : ↥N → ℂ), hcast _ hmem.1⟩ hmem.2
    change (ν ⟨(f : ↥N → ℂ), _⟩ : G → ℂ) = _
    rw [h0, coe_dadeMap hD F, ← hfF, tauHall_eq_dadeMapFun,
      fixedSet_eq_sdiff_of_frobenius hsemi hfree]
  have hnp : nonprincipalIrr ↥((hallCoreOf N).subgroupOf N)
      = Irr ↥((hallCoreOf N).subgroupOf N) \ {1} := by
    ext χ
    rw [mem_nonprincipalIrr]
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  have hS : Set.range ξ
      = indFam ((hallCoreOf N).subgroupOf N) (Irr ↥((hallCoreOf N).subgroupOf N) \ {1}) := by
    rw [hrange, hallIndFam_eq_indFam N, hnp]
  have hinj : Function.Injective ξ := fun a b hab => Subtype.ext hab
  have hc := isSetup_of_frobenius h₇ hG hN hIN hEN hEbot hsemi hfree
  have hS2 : (Set.range ξ).Nontrivial := by
    rw [hrange, hallIndFam_eq_indFam N]; exact hc.family_nontrivial
  have hcard : Nat.card ↥((hallCoreOf N).subgroupOf N) = Nat.card ↥(hallCoreOf N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hallCoreOf_le N)).toEquiv
  have hidx : ((hallCoreOf N).subgroupOf N).index = Nat.card ↥E := by
    rw [← relIndex_hallCoreOf_eq_natCard hsemi]; rfl
  have hζ1' : ξ ⟨ζ, hζS⟩ 1 = (((hallCoreOf N).subgroupOf N).index : ℂ) := by
    rw [hidx, ← he]; exact hζ1
  have hodd : Odd (Nat.card ↥N) := (odd_natCard_lt_natCard_of_ne_top hG.odd_natCard hN.1).2
  have hVne : (hallCoreOf N).subgroupOf N ≠ ⊥ := hsub ▸ hIN.hallCore_ne_bot
  have hfree' : ∀ u ∈ E.subgroupOf N, u ≠ 1 →
      (hallCoreOf N).subgroupOf N ⊓ Subgroup.centralizer {u} = ⊥ :=
    free_subgroupOf (hallCoreOf_le N)
      (fun v hv hv1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hfree hv hv1)
  have h2 : 2 * Nat.card ↥(E.subgroupOf N) ≤ Nat.card ↥((hallCoreOf N).subgroupOf N) - 1 :=
    two_mul_natCard_le_natCard_sub_one hodd hVne hfree'
  have hEcard : Nat.card ↥(E.subgroupOf N) = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hbound : 2 * ((hallCoreOf N).subgroupOf N).index + 1
      ≤ Nat.card ↥((hallCoreOf N).subgroupOf N) := by
    rw [hidx, ← hEcard]
    have hpos : 0 < Nat.card ↥((hallCoreOf N).subgroupOf N) := Nat.card_pos
    omega
  have key := NormalInducedFamily.one_sub_index_div_card_le_cfInner_self_dadeAverage_coherentImage
    (H := (hallCoreOf N).subgroupOf N) (ξ := ξ) (k₀ := ⟨ζ, hζS⟩) (τ := τ') (ν := ν')
    hD hA hS hinj hνc hτ hζIrr hζ1' hS2 hbound
  have himg : CrossFamilyProjection.coherentImage ξ ν' ⟨ζ, hζS⟩ = Ψ := by
    rw [CrossFamilyProjection.coherentImage_apply, hΨ]
    rfl
  rw [himg] at key
  set F : ↥N → ℂ := fun n : ↥N => rhoHallCore N Ψ (n : G) with hFdef
  have hFeq : (fun y : ↥N =>
      dadeAverage ((hallCoreOf N : Set G) \ {1}) (sigSignalizer N) Ψ (y : G)) = F := rfl
  rw [hFeq, hcard, hidx, ← hh, ← he] at key
  have hre : cfInner F F = (((cfInner F F).re : ℝ) : ℂ) := by
    have hx : cfInner F F = (((Nat.card ↥N : ℝ)⁻¹ * ∑ x, Complex.normSq (F x) : ℝ) : ℂ) := by
      rw [cfInner_def]; push_cast; simp [Complex.mul_conj]
    rw [hx]; simp
  have hlhs : (1 : ℂ) - (e : ℂ) / (h : ℂ) = ((1 - (e : ℝ) / (h : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [cfIP_eq_cfInner, hre, hlhs, Complex.real_le_real]
  exact key

theorem FPF_type_i_supporting_character_configuration
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₃ : Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₄ : Statements.FTS_sigma_prime_separation.{u})
    (h₅ : Statements.FTS_type_I_complement_structure.{u})
    (h₆ : Statements.FTS_type_I_core_kappa_identity.{u})
    (h₇ : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FPF_type_i_supporting_character_configuration.{u} := by
  intro G _ _ hG M N hM hN hIM hIN E hEN hEbot hsemi hfree hnotFrob p hp x hxJ hx1 hxM hxK hxord
    hnorm hcent h e hh he hph hep
  obtain ⟨ζ, hζS, hζIrr, hζ1, hζ, ν, hν⟩ :=
    exists_mem_hallIndFam_isCoherentAt h₇ hG hN hIN hEN hEbot hsemi hfree
  refine ⟨ζ, hζS, hζIrr, by rw [hζ1, he], hζ, ν, hν, ?_⟩
  intro Ψ hΨ
  have hΨmem : Ψ ∈ virtualChars G := by rw [hΨ]; exact hν.mem_virtualChars _
  obtain ⟨hpt, hne, hconst⟩ :=
    FPF_type_i_second_witness_comparison h₁ h₂ h₃ h₄ h₅ h₆ h₇ G hG M N hM hN hIM hIN E hEN hEbot
      hsemi hfree hnotFrob ν hν ζ hζS hζIrr hζ Ψ hΨ
  refine ⟨?_, ?_, isClassFun_rhoHallCore h₇ hG hM hIM hΨmem,
    isClassFun_rhoHallCore h₇ hG hN hIN hΨmem, ?_, hne, hconst, ?_⟩
  · rw [hΨ]; exact isSignedIrr_of_isCoherentAt hν hζIrr hζ
  · exact coherentImage_apply_mul_eq_of_cross_maximal h₁ h₂ h₃ h₄ h₅ h₆ h₇ hG hM hN hIM hIN
      hEN hEbot hsemi hfree hnotFrob hp hxJ hx1 hxM hxK hxord hnorm hcent hh he hph hep
      hζS hζIrr (by rw [hζ1, he]) hζ hν hΨ
  · intro k hk hk1
    rw [rhoHallCore_apply_eq_rhoHall_apply M Ψ hk hk1]
    exact hpt k hk hk1
  · exact one_sub_div_le_cfIP_rhoHallCore h₇ hG hN hIN hEN hEbot hsemi hfree
      hh he hζS hζIrr (by rw [hζ1, he]) hζ hν hΨ

end CFSG.FeitThompson.Proofs

end
