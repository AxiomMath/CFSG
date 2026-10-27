module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
import CFSG.FeitThompson.Representations.TypeIAlternativesFrobeniusDadeCoherence
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
import CFSG.FeitThompson.Representations.CentralActionCasesComplementOrderBound
import CFSG.FeitThompson.Representations.TISetDadeData
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Representations.DadeInductionExtendedSupportTypeII

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson

universe u

variable {G : Type*} [Group G] [Finite G]

theorem dadeMapFun_eq_dadeSupportExtension {L : Subgroup G} {A : Set G} {J : G → Subgroup G}
    (hD : IsDadeData L A J) {f : ↥L → ℂ} (hf : f ∈ dadeDomain L A) :
    dadeMapFun L A J f = dadeSupportExtension A J (extendByZero L f) :=
  (coe_dadeMap hD ⟨f, hf⟩).symm.trans (dadeMap_apply_coe hD ⟨f, hf⟩)

theorem FCH_type_I_frobenius_coherent_family
    (h₁ : Statements.FPF_type_I_frobenius.{u})
    (h₂ : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FCH_type_I_frobenius_coherent_family.{u} := by
  classical
  intro G _ _ hG L hL hI
  let _ : Fintype ↥L := CFSG.FeitThompson.subgroupFintype L
  have hG5 : Prep05.IsMinimalSimpleOdd G :=
    { odd_natCard := hG.odd_natCard
      isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      isSolvable_of_ne_top := hG.forall_isSolvable }
  have hG9 : Prep09.IsMinimalSimpleOddOrder G :=
    { odd_natCard := hG.odd_natCard
      isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      isSolvable_of_ne_top := hG.forall_isSolvable }
  obtain ⟨E, hEL, hEbot, hsemi, hfree⟩ := h₁ G hG5 L hL hI
  obtain ⟨hsig, -, -, -, -, hdade, -, -, -⟩ := h₂ G hG9 L hL hI
  have hHL : Prep03.hallCoreIn L ≤ L := Subgroup.map_subtype_le _
  have hsub : (Prep03.hallCoreIn L).subgroupOf L = hallCore ↥L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hnormal : ((Prep03.hallCoreIn L).subgroupOf L).Normal := by
    rw [hsub]; exact hallCore_normal
  have hmul : ((Prep03.hallCoreIn L : Set G)) * ((E : Set G)) = (L : Set G) :=
    hsemi.coe_eq_mul.symm
  have hdisj : Prep03.hallCoreIn L ⊓ E = ⊥ := hsemi.inf_eq_bot
  have hfreeG : ∀ e ∈ E, e ≠ 1 → Prep03.hallCoreIn L ⊓ centralizer ({e} : Set G) = ⊥ := by
    intro e he he1
    have h := hfree e he he1
    rwa [Prep05.centralizerIn_eq, centralizer_coe_zpowers] at h
  have hHne : Prep03.hallCoreIn L ≠ ⊥ := fun h =>
    hI.hallCore_ne_bot ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h)
  have hcard : Nat.card ↥(Prep03.hallCoreIn L) = Nat.card ↥(hallCore ↥L) :=
    (Nat.card_congr ((hallCore ↥L).equivMapOfInjective _ L.subtype_injective).toEquiv).symm
  have hA : {a : G | a ∈ L ∧ a ≠ 1 ∧ Prep03.cent1 (Prep03.hallCoreIn L) a ≠ ⊥}
      = (Prep03.hallCoreIn L : Set G) \ {1} := by
    have := hnormal
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
      Prep03.cent1]
    constructor
    · rintro ⟨haL, ha1, hcent⟩
      refine ⟨?_, ha1⟩
      by_contra hnot
      exact hcent (inf_centralizer_singleton_eq_bot_of_mem_of_notMem hmul hdisj hfreeG haL hnot)
    · rintro ⟨haH, ha1⟩
      refine ⟨hHL haH, ha1, fun hbot => ha1 ?_⟩
      have hmem : a ∈ Prep03.hallCoreIn L ⊓ centralizer ({a} : Set G) :=
        ⟨haH, mem_centralizer_singleton_iff.2 rfl⟩
      rw [hbot] at hmem
      simpa using hmem
  have hAeq : Prep09.coreFixedSet (Prep09.hallCoreIn L) L
      = (Prep03.hallCoreIn L : Set G) \ {1} := hA
  have hdade' : IsDadeData L ((Prep03.hallCoreIn L : Set G) \ {1}) Prep03.sigR := by
    rw [← hAeq]
    refine isDadeData_congr hdade fun a ha => ?_
    rw [hAeq] at ha
    have ha1 : a ≠ 1 := by simpa using ha.2
    rw [Prep09.sigmaSignalizerOn_of_mem (hsig ▸ ha.1) ha1]
    rfl
  have hc : FrobeniusDade.IsSetup L (Prep03.hallCoreIn L) E Prep03.sigR :=
    { odd_card := (odd_natCard_lt_natCard_of_ne_top hG.odd_natCard hL.1).2
      le_left := hHL
      le_right := hEL
      le_normalizer := hsemi.le_normalizer
      sup_eq := hsemi.sup_eq
      inf_eq_bot := hdisj
      ne_bot_left := hHne
      ne_bot_right := hEbot
      free := hfreeG
      isNilpotent := isNilpotent_hallCoreIn L
      isDadeData := hdade' }
  have hfam : hc.family = Prep03.hallIndFamily L := by
    change indFam ((Prep03.hallCoreIn L).subgroupOf L)
      (nonprincipalIrr ↥((Prep03.hallCoreIn L).subgroupOf L)) = Prep03.hallIndFamily L
    rw [hsub]
    ext f
    simp only [Prep03.hallIndFamily, Set.mem_ofPred_eq, mem_indFam, mem_nonprincipalIrr]
    exact ⟨fun ⟨θ, ⟨hθ, hθ1⟩, h⟩ => ⟨θ, hθ, hθ1, h⟩, fun ⟨θ, hθ, hθ1, h⟩ => ⟨θ, ⟨hθ, hθ1⟩, h⟩⟩
  have halt :
      ((∀ g : G, (fun x => g⁻¹ * x * g) '' ((Prep03.hallCoreIn L : Set G) \ {1})
            = (Prep03.hallCoreIn L : Set G) \ {1} ↔ g ∈ L) ∧
          ∀ g ∉ L, ((Prep03.hallCoreIn L : Set G) \ {1}) ∩
            (fun x => g⁻¹ * x * g) '' ((Prep03.hallCoreIn L : Set G) \ {1}) = ∅) ∨
        IsMulCommutative ↥(Prep03.hallCoreIn L) ∨
        ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(Prep03.hallCoreIn L) →
          Monoid.exponent ↥E ∣ p - 1 := by
    have hsharp : hallCoreSharp L = (Prep03.hallCoreIn L : Set G) \ {1} := hallCoreSharp_eq L
    obtain ⟨E₀, hFrob, halt⟩ := hI.exists_isFrobeniusType
    rcases halt with hti | ⟨habel, -⟩ | ⟨hexp, -⟩
    · refine Or.inl ⟨fun g => ?_, fun g hg => ?_⟩
      · rw [← hsharp, ← mem_normalizer_iff_conjInv_image_eq, hti.normalizer_eq]
      · rw [← hsharp]
        exact Set.disjoint_iff_inter_eq_empty.1 (hti.disjoint_image_conj_inv hg)
    · refine Or.inr (Or.inl ?_)
      have := habel
      rw [Prep03.hallCoreIn]
      infer_instance
    · refine Or.inr (Or.inr fun p hp hpd => ?_)
      have hexpE₀ : Monoid.exponent ↥E₀ = Monoid.exponent ↥E := by
        have hn : (hallCore ↥L).Normal := hallCore_normal
        have h1 : (↥L ⧸ hallCore ↥L) ≃* ↥E₀ := hFrob.isComplement'.symm.QuotientMulEquiv
        have h2 : (↥L ⧸ hallCore ↥L) ≃* ↥(E.subgroupOf L) := by
          have h := hc.isComplement'_core
          rw [show hc.core = hallCore ↥L from hsub] at h
          exact h.symm.QuotientMulEquiv
        rw [(Monoid.exponent_eq_of_mulEquiv h1).symm.trans (Monoid.exponent_eq_of_mulEquiv h2),
          Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEL)]
      rw [← hexpE₀]
      exact hexp p (Nat.mem_primeFactors.2 ⟨hp, hcard ▸ hpd, Nat.card_pos.ne'⟩)
  have hrel : (Prep03.hallCoreIn L).relIndex L = Nat.card ↥E := by
    have h1 : Nat.card ↥(Prep03.hallCoreIn L) * (Prep03.hallCoreIn L).relIndex L
        = Nat.card ↥L := by
      rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
      exact Subgroup.card_mul_index _
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans hsemi.natCard_eq_mul)
  have h3 : 1 < Nat.card ↥(Prep03.hallCoreIn L) := by
    have : Nontrivial ↥(Prep03.hallCoreIn L) := (Subgroup.nontrivial_iff_ne_bot _).2 hHne
    exact Finite.one_lt_card
  have h4 : 1 < (Prep03.hallCoreIn L).relIndex L := by
    rw [hrel]
    have : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot _).2 hEbot
    exact Finite.one_lt_card
  have h5 : 2 * (Prep03.hallCoreIn L).relIndex L ≤ Nat.card ↥(Prep03.hallCoreIn L) - 1 := by
    have := hnormal
    have hVne : (Prep03.hallCoreIn L).subgroupOf L ≠ ⊥ := by
      rw [hsub]; exact hI.hallCore_ne_bot
    have key := two_mul_natCard_le_natCard_sub_one (E := E.subgroupOf L) hc.odd_card hVne
      (free_subgroupOf hHL hfreeG)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv, ← hrel] at key
  have hcoh : ∃ ν : (↥L → ℂ) → (G → ℂ),
      Prep03.IsCoherentOn (Prep03.hallIndFamily L) (fun f => Prep03.tauHall L f) ν := by
    obtain ⟨ν, hν⟩ := isCoherent_iff.1 (hc.isCoherent_tau halt)
    refine ⟨fun f => if h : f ∈ Submodule.span ℤ (Prep03.hallIndFamily L)
        then (ν ⟨f, hfam ▸ h⟩ : G → ℂ) else 0, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
    · intro f hf g hg
      simp only [dif_pos hf, dif_pos hg, dif_pos (add_mem hf hg)]
      have h : (⟨f + g, hfam ▸ add_mem hf hg⟩ : Submodule.span ℤ hc.family)
          = ⟨f, hfam ▸ hf⟩ + ⟨g, hfam ▸ hg⟩ := rfl
      rw [h, map_add]
      rfl
    · intro f hf
      simp only [dif_pos hf]
      exact (ν _).2
    · intro f hf g hg
      simp only [dif_pos hf, dif_pos hg]
      exact hν.inner_eq _ _
    · intro f hf hf1
      simp only [dif_pos hf]
      have hf0 : f ∈ charSpanZero hc.family := mem_charSpanZero.2 ⟨hfam ▸ hf, hf1⟩
      have hz : (⟨f, hfam ▸ hf⟩ : Submodule.span ℤ hc.family)
          = Submodule.inclusion (charSpanZero_le hc.family) ⟨f, hf0⟩ := rfl
      rw [hz, hν.eq_on_zero, hc.coe_tau]
      exact dadeMapFun_eq_dadeSupportExtension hc.isDadeData
        (hc.mem_dadeDomain_of_mem_charSpanZero hc.family_subset_indFam_Irr hf0)
  have hdeg : ∃ φ ∈ Prep03.hallIndFamily L,
      φ 1 = ((Prep03.hallCoreIn L).relIndex L : ℂ) := by
    have hn : (hallCore ↥L).Normal := hallCore_normal
    have hsolv : Group.IsSolvable ↥(hallCore ↥L) := inferInstance
    have hne : (hallCore ↥L : Subgroup ↥L) ≠ ⊥ := hsub ▸ hc.core_ne_bot
    have hmul' : ((hallCore ↥L : Subgroup ↥L) : Set ↥L)
        * ((E.subgroupOf L : Subgroup ↥L) : Set ↥L) = Set.univ := by
      rw [← hsub]; exact hc.mul_core_compl
    have hinf' : (hallCore ↥L : Subgroup ↥L) ⊓ E.subgroupOf L = ⊥ := by
      rw [← hsub]; exact hc.inf_core_compl
    have hC' : ∀ u ∈ E.subgroupOf L, u ≠ 1 →
        (hallCore ↥L : Subgroup ↥L) ⊓ Subgroup.centralizer {u} = ⊥ := by
      rw [← hsub]; exact hc.free_core
    obtain ⟨θ, hθ, hθne, -, -, hdeg⟩ :=
      exists_mem_Irr_indClassFun_mem_Irr_index (E := E.subgroupOf L) hne hmul' hinf' hC'
    exact ⟨indClassFun (hallCore ↥L) θ, ⟨θ, hθ, hθne, rfl⟩, by
      rw [hdeg, Subgroup.relIndex, hsub]⟩
  refine ⟨hA, hsig, h3, h4, h5, hdade', fun _ ha _ hb hab => hdade'.fusion ha hb hab,
    fun _ ha => ⟨hdade'.normal_subgroupOf ha, hdade'.sup_eq ha, hdade'.inf_eq_bot ha⟩,
    fun _ ha _ hb => hdade'.coprime_card ha hb, hfam ▸ hc.family_subset_Irr, ?_, ?_, hcoh, hdeg⟩
  ·
    intro f hf
    have h := hc.star_mem_family (hfam ▸ hf)
    rw [hfam] at h
    exact h
  ·
    rw [← hfam]
    have hfin : hc.family.Finite := hc.family_finite
    have := hfin.to_subtype
    exact Set.one_lt_ncard_iff_nontrivial.2 hc.family_nontrivial

end

end CFSG.FeitThompson.Proofs
