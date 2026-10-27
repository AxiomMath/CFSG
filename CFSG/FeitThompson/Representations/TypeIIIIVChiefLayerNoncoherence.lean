module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.TypeIIIIVChiefData
import CFSG.FeitThompson.Foundations.OddPrimePowerQuadraticBound
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
public import CFSG.FeitThompson.Representations.NilpotentNormalSectionCoherenceDescent
public import CFSG.FeitThompson.Representations.EqualDegreeDifferenceSaturatesAntirealBlocks
public import CFSG.FeitThompson.Representations.CoreDetectingFamilyAntirealBlocksSupport
public import CFSG.FeitThompson.Representations.TypeIIIAndIVWeightedNormalFamily
public import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
public import CFSG.FeitThompson.Representations.WeightedFeitInequalityConjugatePairExtension
import all CFSG.FeitThompson.Representations.WeightedFeitInequalityConjugatePairExtension
public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
import all CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep05 NormalInducedFamily

universe u

variable {G : Type*} [Group G] [Finite G] {M U W₁ W₂ : Subgroup G}

theorem subgroupOf_fittingOf (M : Subgroup G) : (fittingOf M).subgroupOf M = fittingRaw ↥M := by
  rw [fittingOf_eq]
  exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

theorem hallCoreOf_le_fittingOf (M : Subgroup G) : hallCoreOf M ≤ fittingOf M := by
  rw [hallCoreOf_eq, fittingOf_eq]
  exact Subgroup.map_mono hallCore_le_fittingRaw

omit [Finite G] in
theorem subgroupOf_commutator_self (M : Subgroup G) :
    (⁅M, M⁆ : Subgroup G).subgroupOf M = CFSG.FeitThompson.Prep06.derivedOf M := by
  rw [CFSG.FeitThompson.Prep06.derivedOf_eq, ← Subgroup.map_subtype_commutator M]
  exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

theorem index_derivedOf (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    (CFSG.FeitThompson.Prep06.derivedOf M).index = Nat.card ↥W₁ := by
  rw [← subgroupOf_commutator_self M, hc.isComplement'_subgroupOf_commutator_W₁.symm.index_eq_card]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.le_M_W₁).toEquiv

theorem fittingRaw_le_derivedOf (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    fittingRaw ↥M ≤ CFSG.FeitThompson.Prep06.derivedOf M := by
  rw [← subgroupOf_fittingOf M, ← subgroupOf_commutator_self M]
  exact Subgroup.subgroupOf_mono M (by rw [fittingOf_eq]; exact hc.fittingRaw_le_commutator)

theorem sup_le_fittingOf (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hsolv : Group.IsSolvable ↥M) (hq : (Nat.card ↥W₁).Prime) (hU : U ≠ ⊥)
    {H₀ : Subgroup G} (hlayer : IsChiefLayer M H₀ (hallCoreOf M)) :
    H₀ ⊔ centralizerIn U (hallCoreOf M) ≤ fittingOf M :=
  sup_le (hlayer.2.1.le.trans (hallCoreOf_le_fittingOf M))
    (chiefData_fitting_product hsolv hq hU hc).2.1.right_le

theorem four_mul_index_sq_add_one_lt_relIndex {G : Type u} [Group G] [Finite G]
    (hprime : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    (hG : IsMinimalSimpleOdd G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup G} (hH₀ : centralizerIn (hallCoreOf M) U ≤ H₀)
    (hlayer : IsChiefLayer M H₀ (hallCoreOf M)) :
    4 * (CFSG.FeitThompson.Prep06.derivedOf M).index ^ 2 + 1
      < ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M).relIndex (fittingRaw ↥M) := by
  obtain ⟨hp, hq, hpodd, hqodd, hpq, -, -, -, -, -, -, -, -, -, -, hlayers⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data hprime G hG M U W₁ W₂ hM htype hc _ _ rfl rfl
  obtain ⟨-, -, -, hidx⟩ := (hlayers H₀ hH₀ hlayer).1
  obtain ⟨-, -, -, -, hn1, hn2, hequiv⟩ := hlayers H₀ hH₀ hlayer
  obtain ⟨e⟩ := hequiv hn1 hn2
  rw [← subgroupOf_fittingOf M, Subgroup.relIndex_subgroupOf (fittingOf_le M), index_derivedOf hc]
  have h1 : (H₀ ⊔ centralizerIn U (hallCoreOf M)).relIndex (fittingOf M)
      = H₀.relIndex (hallCoreOf M) := by
    rw [Subgroup.relIndex, Subgroup.index, Subgroup.relIndex, Subgroup.index]
    exact Nat.card_congr e.toEquiv
  rw [h1, hidx]
  exact four_mul_sq_add_one_lt_pow_of_odd_primes hp hq hpodd hqodd hpq

theorem cfInner_inst {α : Type*} (i j : Fintype α) (f g : α → ℂ) :
    @cfInner α i f g = @cfInner α j f g := by
  have h : i = j := Subsingleton.elim i j
  subst h; rfl

theorem cfIP_eq_cfInner_of_finite {α : Type*} [Finite α] [Fintype α] (f g : α → ℂ) :
    CFSG.FeitThompson.Prep05.cfIP f g = cfInner f g :=
  cfInner_inst _ _ f g

theorem kerLayerIndFam_inst {L : Type*} [Group L] (A B : Subgroup L) (i j : Fintype L) :
    @kerLayerIndFam L _ A B i = @kerLayerIndFam L _ A B j := by
  have h : i = j := Subsingleton.elim i j
  subst h; rfl

theorem charSpanZero_le_span' {L : Type*} [Group L] (S : Set (L → ℂ)) :
    charSpanZero S ≤ Submodule.span ℤ S := fun _ hf => (mem_charSpanZero.1 hf).1

theorem mem_virtualCharSpan_of_mem_virtualChars {X : Type*} [Group X] {f : X → ℂ}
    (h : f ∈ virtualChars X) : f ∈ virtualCharSpan X :=
  mem_virtualCharSpan_of_mem_span_Irr (by rwa [← virtualChars_eq_span_Irr])

theorem subTauHom_coe {L : Type*} {X : Type*} [Group L] [Fintype L] [Group X] [Fintype X]
    {S : Finset (L → ℂ)} {tau : (L → ℂ) → X → ℂ} {R : (L → ℂ) → Finset (X → ℂ)}
    (hc : IsSubcoherent S tau R) {V : Set (L → ℂ)} (hV : V ⊆ ↑S) (f : charSpanZero V) :
    ((WeightedFeitExtension.subTauHom hc hV f : virtualChars X) : X → ℂ) = tau (f : L → ℂ) := by
  with_unfolding_all rfl

theorem kerLayerIndFam_subset_bot {L : Type*} [Group L] [Fintype L] (A K : Subgroup L) :
    kerLayerIndFam A K ⊆ kerLayerIndFam ⊥ K := by
  intro f hf
  rw [mem_kerLayerIndFam] at hf
  obtain ⟨ψ, hψ, rfl⟩ := hf
  obtain ⟨hirr, -, hne⟩ := mem_kerLayerIrr.1 hψ
  rw [mem_kerLayerIndFam]
  refine ⟨ψ, mem_kerLayerIrr.2 ⟨hirr, fun n hn => ?_, hne⟩, rfl⟩
  rw [Subgroup.mem_bot] at hn
  rw [(Subtype.ext hn : n = 1)]

theorem indBetween_eq_indClassFun (M K : Subgroup G) (hKM : K ≤ M) (θ : ↥K → ℂ) :
    letI : Fintype ↥M := Fintype.ofFinite _
    indBetween K M θ
      = indClassFun (K.subgroupOf M) (θ ∘ (Subgroup.subgroupOfEquivOfLe hKM)) := by
  let _ : Fintype ↥M := Fintype.ofFinite _
  rw [indBetween]
  congr 1
  funext z
  rw [Function.comp_apply, extendZero]
  have h : ((z : ↥M) : G) = (K.subtype ((Subgroup.subgroupOfEquivOfLe hKM) z)) := rfl
  rw [h, K.subtype_injective.extend_apply]

theorem derivedIndFamKer_eq_kerLayerIndFam (M A : Subgroup G) :
    letI : Fintype ↥M := Fintype.ofFinite _
    derivedIndFamKer M A
      = kerLayerIndFam (A.subgroupOf M) ((⁅M, M⁆ : Subgroup G).subgroupOf M) := by
  let _ : Fintype ↥M := Fintype.ofFinite _
  have hKM : (⁅M, M⁆ : Subgroup G) ≤ M := Subgroup.commutator_le_self M
  set e := Subgroup.subgroupOfEquivOfLe hKM with he
  have hcomp₁ : ∀ θ : ↥(⁅M, M⁆ : Subgroup G) → ℂ, (θ ∘ ⇑e) ∘ ⇑e.symm = θ := fun θ => by
    funext x; simp
  have hcomp₂ : ∀ ψ : ↥((⁅M, M⁆ : Subgroup G).subgroupOf M) → ℂ, (ψ ∘ ⇑e.symm) ∘ ⇑e = ψ :=
    fun ψ => by funext x; simp
  ext f
  rw [derivedIndFamKer, mem_kerLayerIndFam]
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, ⟨hirr, hne, hker⟩, rfl⟩
    refine ⟨θ ∘ ⇑e, ?_, (indBetween_eq_indClassFun M _ hKM θ).symm⟩
    refine mem_kerLayerIrr.2 ⟨mem_Irr_of_comp_mulEquiv e.symm (by rw [hcomp₁]; exact hirr), ?_, ?_⟩
    · intro n hn
      have h1 : ((e n : ↥(⁅M, M⁆ : Subgroup G)) : G) ∈ A := Subgroup.mem_subgroupOf.1 hn
      simpa [he] using hker (e n) h1
    · intro hcon
      refine hne (funext fun x => ?_)
      have h := congrFun hcon (e.symm x)
      simpa using h
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨hirr, hker, hne⟩ := mem_kerLayerIrr.1 hψ
    refine ⟨ψ ∘ ⇑e.symm, ⟨mem_Irr_of_comp_mulEquiv e (by rw [hcomp₂]; exact hirr), ?_, ?_⟩, ?_⟩
    · intro hcon
      refine hne (funext fun n => ?_)
      have h := congrFun hcon (e n)
      simpa using h
    · intro x hx
      have h1 : ((e.symm x : ↥((⁅M, M⁆ : Subgroup G).subgroupOf M)) : ↥M) ∈ A.subgroupOf M := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      simpa using hker (e.symm x) h1
    · rw [indBetween_eq_indClassFun M _ hKM, hcomp₂]

open scoped Classical in
theorem kerLayerIndFam_bot_eq_indFamNonprincipal {G : Type*} [Group G] [Fintype G]
    (M : Subgroup G) :
    kerLayerIndFam (⊥ : Subgroup ↥M) ((⁅M, M⁆ : Subgroup G).subgroupOf M)
      = CFSG.FeitThompson.Prep06.indFamNonprincipal M (CFSG.FeitThompson.Prep06.derivedOf M) := by
  rw [subgroupOf_commutator_self, CFSG.FeitThompson.Prep06.indFamNonprincipal_eq]
  ext θ
  rw [mem_kerLayerIndFam, mem_indFam]
  refine ⟨fun ⟨ψ, hψ, h⟩ => ⟨ψ, ?_, h⟩, fun ⟨ψ, hψ, h⟩ => ⟨ψ, ?_, h⟩⟩
  · obtain ⟨hirr, -, hne⟩ := mem_kerLayerIrr.1 hψ
    exact mem_nonprincipalIrr.2 ⟨hirr, hne⟩
  · obtain ⟨hirr, hne⟩ := mem_nonprincipalIrr.1 hψ
    refine mem_kerLayerIrr.2 ⟨hirr, fun n hn => ?_, hne⟩
    rw [Subgroup.mem_bot] at hn
    rw [(Subtype.ext hn : n = 1)]

omit [Finite G] in
theorem extendZero_eq_extendByZero (M : Subgroup G) (f : ↥M → ℂ) :
    extendZero f = extendByZero M f := by
  funext x
  rw [extendZero]
  by_cases hx : x ∈ M
  · have h : x = M.subtype ⟨x, hx⟩ := rfl
    rw [h, M.subtype_injective.extend_apply]
    exact (extendByZero_apply_coe M f ⟨x, hx⟩).symm
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨a, rfl⟩; exact hx a.2),
      extendByZero_of_notMem _ _ hx]
    rfl

theorem derSignalizer_eq_dadeT (M : Subgroup G) :
    derSignalizer M = CFSG.FeitThompson.Prep06.dadeT M := by
  funext a
  rw [derSignalizer, signalizerOn, CFSG.FeitThompson.Prep06.dadeT]
  congr 1

theorem tauDerived_eq_dadeTau (M W₁ W₂ : Subgroup G) (f : ↥M → ℂ) :
    tauDerived M W₁ W₂ f = CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂ f := by
  have key : ∀ (L : Subgroup G) (A : Set G) (J : G → Subgroup G) (g : ↥L → ℂ),
      dadeMapFun L A J g = dadeSupportExtension A J (extendByZero L g) := by
    intro L A J g; with_unfolding_all rfl
  rw [tauDerived, CFSG.FeitThompson.Prep06.dadeTau_eq, key, derSignalizer_eq_dadeT,
    extendZero_eq_extendByZero]
  congr 1

open scoped Classical in
theorem isSubcoherent_of_weighted {G : Type u} [Group G] [Fintype G]
    {M W₁ W₂ : Subgroup G} [Fintype ↥M]
    {Sset : Set (↥M → ℂ)} (hfin : Sset.Finite)
    (hchar : ∀ f ∈ Sset, f ≠ 0 ∧ IsCharacter (↥M) f)
    (hstar : ∀ f ∈ Sset, star f ∈ Sset)
    (hstarne : ∀ f ∈ Sset, star f ≠ f)
    (horth : ∀ f ∈ Sset, ∀ g ∈ Sset, f ≠ g → cfInner f g = 0)
    (htau : ∀ f ∈ Submodule.span ℤ Sset, ∀ g ∈ Submodule.span ℤ Sset, f 1 = 0 → g 1 = 0 →
      CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂ (f + g)
          = CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂ f + CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂ g ∧
        cfInner (CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂ f) (CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂ g)
          = cfInner f g ∧
        CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂ f 1 = 0 ∧
        CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂ f ∈ virtualChars G)
    {R : (↥M → ℂ) → Set (G → ℂ)}
    (hR : ∀ f ∈ Sset, (R f).Finite ∧ R f ⊆ (virtualChars G : Set (G → ℂ)) ∧
      (∀ r ∈ R f, ∀ s ∈ R f, cfInner r s = if r = s then 1 else 0) ∧
      CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂ (f - star f) = ∑ᶠ r ∈ R f, r)
    (hRR : ∀ f ∈ Sset, ∀ g ∈ Sset, g ≠ f → g ≠ star f →
      ∀ r ∈ R f, ∀ s ∈ R g, cfInner r s = 0) :
    IsSubcoherent hfin.toFinset (CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂)
      (fun f => if h : (R f).Finite then h.toFinset else ∅) := by
  have hmem : ∀ f, f ∈ hfin.toFinset ↔ f ∈ Sset := by intro f; simp
  have hspan : ∀ f ∈ intSpanZeroAtOne (hfin.toFinset : Set (↥M → ℂ)),
      f ∈ Submodule.span ℤ Sset ∧ f 1 = 0 := by
    intro f hf
    obtain ⟨h1, h2⟩ := mem_intSpanZeroAtOne.mp hf
    rw [Set.Finite.coe_toFinset] at h1
    exact ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro χ hχ; exact (hchar χ ((hmem χ).1 hχ)).2
  · intro χ hχ; exact (hchar χ ((hmem χ).1 hχ)).1
  · intro χ hχ; exact (hmem _).2 (hstar χ ((hmem χ).1 hχ))
  · intro χ hχ; exact hstarne χ ((hmem χ).1 hχ)
  · intro χ hχ ψ hψ hne
    rw [charInner_eq_cfInner]
    exact horth χ ((hmem χ).1 hχ) ψ ((hmem ψ).1 hψ) hne
  · intro f hf h hh
    obtain ⟨hf1, hf2⟩ := hspan f hf
    obtain ⟨hh1, hh2⟩ := hspan h hh
    exact (htau f hf1 h hh1 hf2 hh2).1
  · intro f hf
    obtain ⟨hf1, hf2⟩ := hspan f hf
    exact mem_virtualCharSpan_of_mem_virtualChars (htau f hf1 f hf1 hf2 hf2).2.2.2
  · intro f hf h hh
    obtain ⟨hf1, hf2⟩ := hspan f hf
    obtain ⟨hh1, hh2⟩ := hspan h hh
    rw [charInner_eq_cfInner, charInner_eq_cfInner]
    exact (htau f hf1 h hh1 hf2 hh2).2.1
  · intro f hf
    obtain ⟨hf1, hf2⟩ := hspan f hf
    exact (htau f hf1 f hf1 hf2 hf2).2.2.1
  · intro χ hχ r hr
    have hχ' := (hmem χ).1 hχ
    rw [dif_pos (hR χ hχ').1, Set.Finite.mem_toFinset] at hr
    exact mem_virtualCharSpan_of_mem_virtualChars ((hR χ hχ').2.1 hr)
  · intro χ hχ r hr
    have hχ' := (hmem χ).1 hχ
    rw [dif_pos (hR χ hχ').1, Set.Finite.mem_toFinset] at hr
    rw [charInner_eq_cfInner, (hR χ hχ').2.2.1 r hr r hr, if_pos rfl]
  · intro χ hχ r hr s hs hne
    have hχ' := (hmem χ).1 hχ
    rw [dif_pos (hR χ hχ').1, Set.Finite.mem_toFinset] at hr hs
    rw [charInner_eq_cfInner, (hR χ hχ').2.2.1 r hr s hs, if_neg hne]
  · intro χ hχ
    have hχ' := (hmem χ).1 hχ
    have hfinR := (hR χ hχ').1
    rw [(hR χ hχ').2.2.2, dif_pos hfinR, ← finsum_mem_coe_finset, hfinR.coe_toFinset]
  · intro χ hχ ψ hψ hne1 hne2 r hr s hs
    have hχ' := (hmem χ).1 hχ
    have hψ' := (hmem ψ).1 hψ
    rw [dif_pos (hR χ hχ').1, Set.Finite.mem_toFinset] at hr
    rw [dif_pos (hR ψ hψ').1, Set.Finite.mem_toFinset] at hs
    rw [charInner_eq_cfInner]
    exact hRR χ hχ' ψ hψ' hne1 hne2 r hr s hs

theorem isCoherent_of_isCoherentAt {X : Type u} [Group X] [Finite X] [Fintype X]
    {N V₁ V₂ : Subgroup X} [Fintype ↥N] {Sfin : Finset (↥N → ℂ)}
    {tau : (↥N → ℂ) → X → ℂ} {R : (↥N → ℂ) → Finset (X → ℂ)}
    (hc : IsSubcoherent Sfin tau R)
    (htau : ∀ f, tau f = CFSG.FeitThompson.Prep06.dadeTau N V₁ V₂ f)
    {S S₀ : Set (↥N → ℂ)} (hUS : S ⊆ ↑Sfin) (hS : S = S₀)
    (ν : Submodule.span ℤ S₀ →+ (X → ℂ))
    (hν : IsCoherentAt N S₀ (tauDerived N V₁ V₂) ν) :
    IsCoherent S (WeightedFeitExtension.subTauHom hc hUS) := by
  subst hS
  rw [isCoherent_iff]
  refine ⟨AddMonoidHom.mk' (fun f => (⟨ν f, hν.mem_virtualChars f⟩ : virtualChars X))
      (fun f g => Subtype.ext (by simp)), ?_, ?_⟩
  · intro f g
    have h := hν.isometry f g
    rw [cfIP_eq_cfInner_of_finite, cfIP_eq_cfInner_of_finite] at h
    exact h.trans (cfInner_inst _ _ _ _)
  · intro f
    refine Subtype.ext ?_
    have hz : ((Submodule.inclusion (charSpanZero_le_span' S) f : Submodule.span ℤ S) : ↥N → ℂ) 1
        = 0 := (mem_charSpanZero.1 f.2).2
    have h := hν.eq_tau (Submodule.inclusion (charSpanZero_le_span' S) f) hz
    change (ν _ : X → ℂ) = _
    rw [subTauHom_coe, htau, h, tauDerived_eq_dadeTau]
    rfl

theorem hasCoherentMap_of_isCoherent_subTauHom_of_tau_eq {X : Type u} [Group X] [Fintype X]
    {N V₁ V₂ : Subgroup X} [Fintype ↥N] {Sfin : Finset (↥N → ℂ)}
    {tau : (↥N → ℂ) → X → ℂ} {R : (↥N → ℂ) → Finset (X → ℂ)}
    (hc : IsSubcoherent Sfin tau R)
    (htau : ∀ f, tau f = CFSG.FeitThompson.Prep06.dadeTau N V₁ V₂ f)
    {S : Set (↥N → ℂ)} (hUS : S ⊆ ↑Sfin)
    (h : IsCoherent S (WeightedFeitExtension.subTauHom hc hUS)) :
    CFSG.FeitThompson.Prep06.HasCoherentMap N V₁ V₂ S := by
  rw [isCoherent_iff] at h
  obtain ⟨ν, hinner, heq⟩ := h
  refine ⟨ν, fun f g => (hinner f g).trans (cfInner_inst _ _ _ _), ?_⟩
  intro f hf1
  have hfz : (f : ↥N → ℂ) ∈ charSpanZero S := mem_charSpanZero.2 ⟨f.2, hf1⟩
  have h2 := heq ⟨(f : ↥N → ℂ), hfz⟩
  have h3 : Submodule.inclusion (charSpanZero_le_span' S) ⟨(f : ↥N → ℂ), hfz⟩ = f :=
    Subtype.ext rfl
  rw [h3] at h2
  rw [h2, subTauHom_coe, htau]

theorem hasCoherentMap_of_isCoherentAt_chiefLayer
    (_h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (_h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (_h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Finite G] (_hG : IsMinimalSimpleOdd G)
    {M U W₁ W₂ : Subgroup G} (_hM : IsCoatom M) (_htype : IsTypeIII M ∨ IsTypeIV M)
    (_hc : IsWitnessedPConfiguration M U W₁ W₂)
    {H₀ : Subgroup G} (_hH₀ : centralizerIn (hallCoreOf M) U ≤ H₀)
    (_hlayer : IsChiefLayer M H₀ (hallCoreOf M))
    (_ν : Submodule.span ℤ
        (derivedIndFamKer M (H₀ ⊔ centralizerIn U (hallCoreOf M))) →+ (G → ℂ))
    (_hν : IsCoherentAt M (derivedIndFamKer M (H₀ ⊔ centralizerIn U (hallCoreOf M)))
      (tauDerived M W₁ W₂) _ν) :
    letI := Fintype.ofFinite G
    CFSG.FeitThompson.Prep06.HasCoherentMap M W₁ W₂
      (CFSG.FeitThompson.Prep06.indFamNonprincipal M (CFSG.FeitThompson.Prep06.derivedOf M)) := by
  classical
  let iG : Fintype G := Fintype.ofFinite G
  change CFSG.FeitThompson.Prep06.HasCoherentMap M W₁ W₂
    (CFSG.FeitThompson.Prep06.indFamNonprincipal M (CFSG.FeitThompson.Prep06.derivedOf M))
  have hG6 : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨_hG.odd_natCard, _hG.isSimpleGroup, _hG.not_isMulCommutative, _hG.isSolvable_of_ne_top⟩
  have hsolvM : Group.IsSolvable ↥M := _hG.isSolvable_of_ne_top M _hM.1
  have hKsolv : Group.IsSolvable ↥(CFSG.FeitThompson.Prep06.derivedOf M) := inferInstance
  have hKnormal : (CFSG.FeitThompson.Prep06.derivedOf M).Normal := by
    rw [CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  obtain ⟨hp, hq, hpodd, hqodd, hpq, hUne, -, -, -, -, -, -, -, -, -, hlayers⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data _h₃ G _hG M U W₁ W₂ _hM _htype _hc _ _ rfl rfl
  obtain ⟨-, -, hnormH1, -, -, -, -⟩ := hlayers H₀ _hH₀ _hlayer
  have hH1normal : ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormH1
  obtain ⟨hchar, hstar, hstarne, horth, htauC, ⟨R, hR, hRR⟩, hnoncoh⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_weighted_normal_family _h₁ _h₂ G hG6 M U W₁ W₂ _hM _htype
      _hc _ rfl
  have hfin :
      (CFSG.FeitThompson.Prep06.indFamNonprincipal M (CFSG.FeitThompson.Prep06.derivedOf M)).Finite := by
    rw [← kerLayerIndFam_bot_eq_indFamNonprincipal M]
    exact finite_kerLayerIndFam
  have hsub := isSubcoherent_of_weighted (M := M) (W₁ := W₁) (W₂ := W₂) hfin
    (fun f hf => ⟨(hchar f hf).1, (hchar f hf).2⟩) hstar hstarne horth htauC hR hRR
  have hStar : (hfin.toFinset : Set (↥M → ℂ))
      = kerLayerIndFam (⊥ : Subgroup ↥M) (CFSG.FeitThompson.Prep06.derivedOf M) := by
    rw [hfin.coe_toFinset, ← subgroupOf_commutator_self M,
      kerLayerIndFam_bot_eq_indFamNonprincipal M, subgroupOf_commutator_self]
  have hUS : kerLayerIndFam ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M)
      (CFSG.FeitThompson.Prep06.derivedOf M) ⊆ (hfin.toFinset : Set (↥M → ℂ)) := by
    rw [hStar]; exact kerLayerIndFam_subset_bot _ _
  have hSeq : kerLayerIndFam ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M)
      (CFSG.FeitThompson.Prep06.derivedOf M)
      = derivedIndFamKer M (H₀ ⊔ centralizerIn U (hallCoreOf M)) := by
    rw [derivedIndFamKer_eq_kerLayerIndFam M (H₀ ⊔ centralizerIn U (hallCoreOf M)),
      subgroupOf_commutator_self]
    exact kerLayerIndFam_inst _ _ _ _
  have hcoh1 := isCoherent_of_isCoherentAt hsub (fun _ => rfl) hUS hSeq _ν _hν
  have hnilF : Group.IsNilpotent ↥(fittingRaw ↥M) := fittingRaw_isNilpotent ↥M
  have hnil := Group.nilpotent_quotient_of_nilpotent
    ((⊥ : Subgroup ↥M).subgroupOf (fittingRaw ↥M))
  have hH1H : (H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M ≤ fittingRaw ↥M := by
    rw [← subgroupOf_fittingOf M]
    exact Subgroup.subgroupOf_mono M (sup_le_fittingOf _hc hsolvM hq hUne _hlayer)
  have hthr := four_mul_index_sq_add_one_lt_relIndex _h₃ _hG _hM _htype _hc _hH₀ _hlayer
  have hfinal :=
    NilpotentSectionCoherence.isCoherent_kerLayerIndFam_of_isNilpotent_quotient_of_eq_bot
      (K := CFSG.FeitThompson.Prep06.derivedOf M) (M := (⊥ : Subgroup ↥M)) (H := fittingRaw ↥M)
      (H1 := (H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M) hsub hStar
      (fittingRaw_normal ↥M) hnil bot_le hH1H (fittingRaw_le_derivedOf _hc) hthr hcoh1
  have hres :=
    hasCoherentMap_of_isCoherent_subTauHom_of_tau_eq hsub (fun _ => rfl) hStar.ge hfinal
  rw [← hStar, hfin.coe_toFinset] at hres
  exact hres

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FPF_type_iii_iv_chief_layer_noncoherence
    (h₁ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₂ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₃ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_chief_layer_noncoherence.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc H₀ hH₀ hlayer
  rintro ⟨ν, hν⟩
  let _ : Fintype G := Fintype.ofFinite G
  have hG6 : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  exact h₂ G hG6 M U W₁ W₂ hM (htype.imp_right Or.inl) hc
    (hasCoherentMap_of_isCoherentAt_chiefLayer h₁ h₂ h₃ hG hM htype hc hH₀ hlayer ν hν)

end CFSG.FeitThompson.Proofs
