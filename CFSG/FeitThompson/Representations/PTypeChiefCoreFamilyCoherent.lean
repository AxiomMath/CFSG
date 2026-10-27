module

public import CFSG.FeitThompson.Representations.CoreDetectingFamilyAntirealBlocks
public import CFSG.FeitThompson.Representations.FieldActionDetectingFamilyCoherence
public import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
public import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
public import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
public import CFSG.FeitThompson.Representations.PTypeChiefCoreFamilyCoherentSupport
public import CFSG.FeitThompson.Local.TypeIIHallCoreElementaryAbelian
public import CFSG.FeitThompson.Representations.TypeIAlternativesFrobeniusDadeCoherence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PtypeCoreCoherence

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G]

private theorem subgroupOf_map_subtype (M : Subgroup G) (X : Subgroup ↥M) :
    (X.map M.subtype).subgroupOf M = X :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective X

structure IsPtypeCoreConfig [Finite G] (M U W₁ W₂ : Subgroup G) (H0 : Subgroup ↥M) [H0.Normal]
    (A : Set ↥M) (A0 : Set G) (T : G → Subgroup G) : Prop where
  simple : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  odd_card : Odd (Nat.card G)
  solvable_proper : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K
  isCoatom : IsCoatom M
  isType : IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M
  isWitnessedPConfiguration : IsWitnessedPConfiguration M U W₁ W₂
  isChiefFactor : IsChiefFactor (hallCore ↥M) H0
  centralizer_le_H0 :
    hallCore ↥M ⊓ Subgroup.centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ H0
  A_subset : A ⊆ ((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1}
  A_conj : ∀ t : ↥M, (fun a => t⁻¹ * a * t) '' A = A
  centralizer_subset_A : ∀ y ∈ hallCore ↥M, y ≠ 1 →
    ((commutator ↥M ⊓ Subgroup.centralizer {y} : Subgroup ↥M) : Set ↥M) \ {1} ⊆ A
  A0_eq : A0 = (fun x : ↥M => (x : G)) '' bridgeSupport A (W₁.subgroupOf M) (W₂.subgroupOf M)
  isDadeData : IsDadeData M A0 T

noncomputable def coreDetectFam (M : Subgroup G) [Fintype ↥M] (U : Subgroup G)
    (H0 : Subgroup ↥M) [H0.Normal] : Set (↥M → ℂ) :=
  indFam (commutator ↥M)
    (irrKer ℂ ((hallCore ↥M).subgroupOf (commutator ↥M))
      ((H0 ⊔ ⁅chiefActionKer (hallCore ↥M) H0 (U.subgroupOf M),
          chiefActionKer (hallCore ↥M) H0 (U.subgroupOf M)⁆).subgroupOf (commutator ↥M)))

theorem coreDetectFam_eq_indFam (M : Subgroup G) [Fintype ↥M] (U : Subgroup G)
    (H0 : Subgroup ↥M) [H0.Normal] :
    coreDetectFam M U H0 = indFam (commutator ↥M)
      (irrKer ℂ ((hallCore ↥M).subgroupOf (commutator ↥M))
        ((H0 ⊔ ⁅chiefActionKer (hallCore ↥M) H0 (U.subgroupOf M),
            chiefActionKer (hallCore ↥M) H0 (U.subgroupOf M)⁆).subgroupOf
          (commutator ↥M))) := (rfl)

theorem mem_coreDetectFam {M : Subgroup G} [Fintype ↥M] {U : Subgroup G} {H0 : Subgroup ↥M}
    [H0.Normal] {f : ↥M → ℂ} :
    f ∈ coreDetectFam M U H0 ↔
      ∃ θ ∈ irrKer ℂ ((hallCore ↥M).subgroupOf (commutator ↥M))
        ((H0 ⊔ ⁅chiefActionKer (hallCore ↥M) H0 (U.subgroupOf M),
            chiefActionKer (hallCore ↥M) H0 (U.subgroupOf M)⁆).subgroupOf (commutator ↥M)),
        indClassFun (commutator ↥M) θ = f :=
  mem_indFam _

theorem coreDetectFam_subset_indFamDetect (M : Subgroup G) [Fintype ↥M] (U : Subgroup G)
    (H0 : Subgroup ↥M) [H0.Normal] :
    coreDetectFam M U H0 ⊆
      indFamDetect (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) :=
  indFam_irrKer_subset_indFamDetect _ _ _

section GroupTheory

variable [Finite G] {M U W₁ W₂ : Subgroup G} {H0 : Subgroup ↥M} [H0.Normal] {A : Set ↥M}
  {A0 : Set G} {T : G → Subgroup G}

namespace IsPtypeCoreConfig

variable (hc : IsPtypeCoreConfig M U W₁ W₂ H0 A A0 T)

include hc

theorem isSolvable_M : Group.IsSolvable ↥M := hc.solvable_proper M hc.isCoatom.1

theorem H0_le_hallCore : H0 ≤ hallCore ↥M := hc.isChiefFactor.le

theorem H0_lt_hallCore : H0 < hallCore ↥M := hc.isChiefFactor.lt

theorem commutator_hallCore_le_H0 : ⁅hallCore ↥M, hallCore ↥M⁆ ≤ H0 :=
  have := hc.isSolvable_M
  hc.isChiefFactor.commutator_num_le_den

theorem sup_hallCore_U : hallCore ↥M ⊔ U.subgroupOf M = commutator ↥M := by
  have h1 : (hallCore ↥M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have h := congrArg (fun X : Subgroup G => X.subgroupOf M)
    hc.isWitnessedPConfiguration.sup_hallCore_E
  simp only [Subgroup.subgroupOf_sup h1 hc.isWitnessedPConfiguration.le_M_E,
    subgroupOf_map_subtype] at h
  rw [h, commutator_eq_subgroupOf_commutator]

theorem disjoint_hallCore_U : Disjoint (hallCore ↥M) (U.subgroupOf M) := by
  rw [Subgroup.disjoint_def]
  intro x hx1 hx2
  have h : (x : G) ∈ (hallCore ↥M).map M.subtype ⊓ U :=
    ⟨Subgroup.mem_map_of_mem _ hx1, Subgroup.mem_subgroupOf.1 hx2⟩
  rw [hc.isWitnessedPConfiguration.disjoint_hallCore_E.eq_bot] at h
  exact Subtype.ext (by simpa using h)

theorem coprime_natCard_hallCore_U :
    (Nat.card (hallCore ↥M)).Coprime (Nat.card (U.subgroupOf M)) := by
  have h1 := hc.isWitnessedPConfiguration.coprime_natCard_hallCore_natCard_E
  rw [Subgroup.card_map_of_injective M.subtype_injective] at h1
  rwa [Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe hc.isWitnessedPConfiguration.le_M_E).toEquiv]

theorem one_notMem_A : (1 : ↥M) ∉ A := fun h => (hc.A_subset h).2 rfl

theorem image_subset_A0 : (fun x : ↥M => (x : G)) '' A ⊆ A0 := by
  rw [hc.A0_eq]
  exact Set.image_mono subset_bridgeSupport_left

end IsPtypeCoreConfig

end GroupTheory

section Characters

variable [Finite G] {M U W₁ W₂ : Subgroup G} [Fintype ↥M] {H0 : Subgroup ↥M} [H0.Normal]
  {A : Set ↥M} {A0 : Set G} {T : G → Subgroup G}

namespace IsPtypeCoreConfig

variable (hc : IsPtypeCoreConfig M U W₁ W₂ H0 A A0 T)

include hc

theorem eq_zero_of_mem_coreDetectFam {f : ↥M → ℂ} (hf : f ∈ coreDetectFam M U H0)
    {g : ↥M} (hg : g ∉ A) (hg1 : g ≠ 1) : f g = 0 :=
  PrimeDadeSubcoherence.apply_eq_zero_of_mem_indFamDetect_of_notMem hc.A_conj
    hc.centralizer_subset_A (coreDetectFam_subset_indFamDetect M U H0 hf)
    (by simp only [Set.mem_union, Set.mem_singleton_iff]; tauto)

omit hc [Finite G] in
theorem mem_span_Irr_of_mem_span {f : ↥M → ℂ}
    (hf : f ∈ Submodule.span ℤ (coreDetectFam M U H0)) : f ∈ Submodule.span ℤ (Irr ↥M) :=
  Submodule.span_le.2 (fun _ hg =>
    PrimeDadeSubcoherence.mem_span_Irr_of_mem_indFamDetect
      (coreDetectFam_subset_indFamDetect M U H0 hg)) hf

theorem eq_zero_of_mem_charSpanZero {f : ↥M → ℂ}
    (hf : f ∈ charSpanZero (coreDetectFam M U H0)) {g : ↥M} (hg : g ∉ A) : f g = 0 := by
  rcases eq_or_ne g 1 with rfl | hg1
  · exact (mem_charSpanZero.1 hf).2
  · exact PrimeDadeSubcoherence.apply_eq_zero_of_mem_intSpanZeroAtOne hc.A_conj
      hc.centralizer_subset_A
      (mem_intSpanZeroAtOne.2 ⟨Submodule.span_le.2
        (fun _ hg' => Submodule.subset_span (coreDetectFam_subset_indFamDetect M U H0 hg'))
        (mem_charSpanZero.1 hf).1, (mem_charSpanZero.1 hf).2⟩) hg

theorem mem_dadeDomain_of_mem_charSpanZero {f : ↥M → ℂ}
    (hf : f ∈ charSpanZero (coreDetectFam M U H0)) : f ∈ dadeDomain M A0 :=
  PrimeDadeSubcoherence.mem_dadeDomain_of_mem_intSpanZeroAtOne hc.A_conj
    hc.centralizer_subset_A hc.image_subset_A0
    (mem_intSpanZeroAtOne.2 ⟨Submodule.span_le.2
      (fun _ hg => Submodule.subset_span (coreDetectFam_subset_indFamDetect M U H0 hg))
      (mem_charSpanZero.1 hf).1, (mem_charSpanZero.1 hf).2⟩)

theorem dadeMapFun_mem_virtualChars {f : ↥M → ℂ}
    (hf : f ∈ charSpanZero (coreDetectFam M U H0)) : dadeMapFun M A0 T f ∈ virtualChars G :=
  mem_virtualChars_of_mem_span_Irr (PrimeDadeSubcoherence.dadeMapFun_mem_span_Irr hc.isDadeData
    (hc.mem_dadeDomain_of_mem_charSpanZero hf)
    (mem_span_Irr_of_mem_span (mem_charSpanZero.1 hf).1))

noncomputable def baselineMap : charSpanZero (coreDetectFam M U H0) →+ virtualChars G :=
  AddMonoidHom.mk' (fun f => ⟨dadeMapFun M A0 T (f : ↥M → ℂ), hc.dadeMapFun_mem_virtualChars f.2⟩)
    fun f g => Subtype.ext (by
      simpa using dadeMapFun_add M A0 T (f : ↥M → ℂ) (g : ↥M → ℂ))

theorem coe_baselineMap (f : charSpanZero (coreDetectFam M U H0)) :
    (hc.baselineMap f : G → ℂ) = dadeMapFun M A0 T (f : ↥M → ℂ) := (rfl)

theorem cfInner_baselineMap [Fintype G] (f g : charSpanZero (coreDetectFam M U H0)) :
    cfInner (hc.baselineMap f : G → ℂ) (hc.baselineMap g : G → ℂ)
      = cfInner (f : ↥M → ℂ) (g : ↥M → ℂ) := by
  rw [hc.coe_baselineMap, hc.coe_baselineMap]
  exact PrimeDadeSubcoherence.cfInner_dadeMapFun hc.isDadeData
    (hc.mem_dadeDomain_of_mem_charSpanZero f.2) (hc.mem_dadeDomain_of_mem_charSpanZero g.2)

theorem baselineMap_apply_one (f : charSpanZero (coreDetectFam M U H0)) :
    (hc.baselineMap f : G → ℂ) 1 = 0 := by
  rw [hc.coe_baselineMap]
  exact PrimeDadeSubcoherence.dadeMapFun_apply_one_eq_zero hc.isDadeData
    (hc.mem_dadeDomain_of_mem_charSpanZero f.2)

theorem prime_natCard_W₁ : (Nat.card W₁).Prime := by
  have hsolv := hc.isSolvable_M
  rcases hc.isType with h | h | h <;>
    exact (h.clauses_of_isWitnessedPConfiguration hsolv
      hc.isWitnessedPConfiguration).1.prime_natCard_W₁

theorem ne_bot_U : U ≠ ⊥ := by
  have hsolv := hc.isSolvable_M
  rcases hc.isType with h | h | h
  · exact (h.clauses_of_isWitnessedPConfiguration hsolv hc.isWitnessedPConfiguration).2.1
  · exact (h.clauses_of_isWitnessedPConfiguration hsolv hc.isWitnessedPConfiguration).2.1
  · intro hU
    exact (h.clauses_of_isWitnessedPConfiguration hsolv hc.isWitnessedPConfiguration).2.1
      (hU ▸ inferInstance)

theorem isPTypeConfig :
    IsPTypeConfig (hallCore ↥M) (⁅M, M⁆.subgroupOf M) (U.subgroupOf M) (W₁.subgroupOf M)
      (fittingRaw ↥M) (W₂.subgroupOf M) :=
  hc.isWitnessedPConfiguration.isPTypeConfig hc.isSolvable_M hc.prime_natCard_W₁ hc.ne_bot_U

theorem odd_natCard_M : Odd (Nat.card ↥M) := by
  have hd : Nat.card ↥M ∣ Nat.card G := Subgroup.card_subgroup_dvd_card M
  rcases Nat.even_or_odd (Nat.card ↥M) with he | ho
  · exact absurd (he.two_dvd.trans hd)
      (by simpa [Nat.two_dvd_ne_zero] using Nat.odd_iff.1 hc.odd_card)
  · exact ho

theorem A_subset_subgroupOf :
    A ⊆ ((⁅M, M⁆.subgroupOf M : Subgroup ↥M) : Set ↥M) \ {1} := fun x hx => by
  have h := hc.A_subset hx
  rwa [commutator_eq_subgroupOf_commutator] at h

theorem A_invariant : ∀ g : ↥M, ∀ x ∈ A, g⁻¹ * x * g ∈ A := fun g x hx => by
  rw [← hc.A_conj g]; exact ⟨x, hx, rfl⟩

theorem centralizer_subset_A_subgroupOf : ∀ h ∈ hallCore ↥M, h ≠ 1 →
    ((⁅M, M⁆.subgroupOf M ⊓ Subgroup.centralizer ({h} : Set ↥M) : Subgroup ↥M) : Set ↥M) \ {1}
      ⊆ A := fun h hh hh1 => by
  have hsub := hc.centralizer_subset_A h hh hh1
  rwa [commutator_eq_subgroupOf_commutator] at hsub

noncomputable def baselineMapOn {S : Finset (↥M → ℂ)}
    (hS : (S : Set (↥M → ℂ)) = coreDetectFam M U H0) :
    charSpanZero (S : Set (↥M → ℂ)) →+ virtualChars G :=
  AddMonoidHom.mk' (fun f => ⟨dadeMapFun M A0 T (f : ↥M → ℂ),
      hc.dadeMapFun_mem_virtualChars (hS ▸ f.2)⟩)
    fun f g => Subtype.ext (by simpa using dadeMapFun_add M A0 T (f : ↥M → ℂ) (g : ↥M → ℂ))

theorem coe_baselineMapOn {S : Finset (↥M → ℂ)}
    (hS : (S : Set (↥M → ℂ)) = coreDetectFam M U H0)
    (f : charSpanZero (S : Set (↥M → ℂ))) :
    (hc.baselineMapOn hS f : G → ℂ) = dadeMapFun M A0 T (f : ↥M → ℂ) := (rfl)

theorem mem_dadeDomain_of_mem_virtualCharsOn {f : ↥M → ℂ}
    (hf : f ∈ ScalarCoreCoherence.virtualCharsOn A) : f ∈ dadeDomain M A0 := by
  rw [ScalarCoreCoherence.mem_virtualCharsOn] at hf
  refine mem_dadeDomain_of_mem_span_Irr (virtualChars_le_span_Irr hf.1) fun x hx => ?_
  exact hf.2 x fun hxA => hx (hc.image_subset_A0 ⟨x, hxA, rfl⟩)

noncomputable def dadeSupportedMap :
    ScalarCoreCoherence.virtualCharsOn A →+ virtualChars G :=
  AddMonoidHom.mk' (fun f => ⟨dadeMapFun M A0 T (f : ↥M → ℂ),
      mem_virtualChars_of_mem_span_Irr (PrimeDadeSubcoherence.dadeMapFun_mem_span_Irr
        hc.isDadeData (hc.mem_dadeDomain_of_mem_virtualCharsOn f.2)
        (virtualChars_le_span_Irr (ScalarCoreCoherence.mem_virtualCharsOn.1 f.2).1))⟩)
    fun f g => Subtype.ext (by simpa using dadeMapFun_add M A0 T (f : ↥M → ℂ) (g : ↥M → ℂ))

theorem coe_dadeSupportedMap (f : ScalarCoreCoherence.virtualCharsOn A) :
    (hc.dadeSupportedMap f : G → ℂ) = dadeMapFun M A0 T (f : ↥M → ℂ) := (rfl)

theorem cfInner_dadeSupportedMap [Fintype G]
    (f g : ScalarCoreCoherence.virtualCharsOn A) :
    cfInner (hc.dadeSupportedMap f : G → ℂ) (hc.dadeSupportedMap g : G → ℂ)
      = cfInner (f : ↥M → ℂ) (g : ↥M → ℂ) :=
  PrimeDadeSubcoherence.cfInner_dadeMapFun hc.isDadeData
    (hc.mem_dadeDomain_of_mem_virtualCharsOn f.2) (hc.mem_dadeDomain_of_mem_virtualCharsOn g.2)

theorem isCoherent_coreDetectFam_of_fixedFree [Fintype G]
    {S : Finset (↥M → ℂ)} {R : (↥M → ℂ) → Finset (G → ℂ)}
    (hsub : IsSubcoherent S (dadeMapFun M A0 T) R)
    (hS : (S : Set (↥M → ℂ)) = coreDetectFam M U H0)
    (hfree : ∀ u ∈ U.subgroupOf M, u ∉ chiefActionKer (hallCore ↥M) H0 (U.subgroupOf M) →
      ∀ h ∈ hallCore ↥M, ((u⁻¹ * h * u : ↥M) : ↥M ⧸ H0) = (h : ↥M ⧸ H0) → h ∈ H0)
    (τS : charSpanZero (S : Set (↥M → ℂ)) →+ virtualChars G)
    (hτS : ∀ f : charSpanZero (S : Set (↥M → ℂ)),
      (τS f : G → ℂ) = dadeMapFun M A0 T (f : ↥M → ℂ)) :
    IsCoherent (S : Set (↥M → ℂ)) τS :=
  FieldActionCoreCoherence.isCoherent_fieldActionDetectFam hsub τS hτS hc.H0_le_hallCore
    hc.disjoint_hallCore_U hc.sup_hallCore_U hc.coprime_natCard_hallCore_U
    hc.commutator_hallCore_le_H0 hfree (by rw [hS, coreDetectFam_eq_indFam])

theorem isCoherent_coreDetectFam [Fintype G]
    {S : Finset (↥M → ℂ)} {R : (↥M → ℂ) → Finset (G → ℂ)}
    (hsub : IsSubcoherent S (dadeMapFun M A0 T) R)
    (hS : (S : Set (↥M → ℂ)) = coreDetectFam M U H0) :
    IsCoherent (coreDetectFam M U H0) hc.baselineMap := by
  classical
  refine FrobeniusDade.isCoherent_of_set_eq hS.symm hc.baselineMap (hc.baselineMapOn hS)
    (fun f f' hff' => by rw [hc.coe_baselineMap, hc.coe_baselineMapOn, hff']) ?_
  have hsolv := hc.isSolvable_M
  have hcfg := hc.isPTypeConfig
  obtain ⟨q, hq⟩ : ∃ q, Nat.card (W₁.subgroupOf M) = q := ⟨_, rfl⟩
  have hfq := Fact.mk (hq ▸ hcfg.prime_natCard_B : q.Prime)
  obtain ⟨b, hbB, hb1, hbgen⟩ := exists_zpowers_eq_of_prime_natCard hcfg.prime_natCard_B
  have hchief := hc.isChiefFactor
  have hHn : (hallCore ↥M).Normal := hchief.normal_num
  have hCU : hallCore ↥M ⊓ Subgroup.centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ H0 :=
    hc.centralizer_le_H0
  have hs := hcfg.isFaithfulImageSetup hq hchief hCU hbB hb1
  obtain ⟨p, d, hp, -, ⟨e⟩⟩ :=
    ChiefFactorLinearAction.exists_prime_nonempty_mulEquiv_of_isChiefFactor hchief
  have hfp := Fact.mk hp
  have hdq : d = q := by
    have h := hs.finrank_eq p e hp
    rwa [Module.finrank_fin_fun] at h
  subst hdq
  obtain ⟨hD, hDA, hDb⟩ : ∃ D : PrimeDimLinearSetup p d (Fin d → ZMod p),
      D.A = ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) H0 (U.subgroupOf M) e ∧
        D.b = ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) H0 e b :=
    ⟨hcfg.linearModel hq hchief hCU hbB hb1 e,
      hcfg.linearModel_A hq hchief hCU hbB hb1 e, hcfg.linearModel_b hq hchief hCU hbB hb1 e⟩
  rcases hD.xor_actsReducibly_isIrreducible with ⟨hred, -⟩ | ⟨hirr, -⟩
  ·
    obtain ⟨Sys, hSysA, hSysb⟩ := hD.exists_scalarLineSystem hred
    have hscal := isScalarCoreConfig_of_scalarLineSystem hcfg hc.odd_natCard_M hq hchief hCU
      hbB hb1 hbgen e Sys (by rw [hSysA, hDA]) (by rw [hSysb, hDb]) hc.A_subset_subgroupOf
      hc.A_invariant hc.centralizer_subset_A_subgroupOf
    have hKn : (⁅M, M⁆.subgroupOf M : Subgroup ↥M).Normal := normal_subgroupOf_commutator_self M
    have hfamily : scalarEqualityFamily (⁅M, M⁆.subgroupOf M) (hallCore ↥M) H0 (U.subgroupOf M)
        (fun i => ChiefFactorLinearAction.subgroupOfSubmodule e (Sys.L i))
          = coreDetectFam M U H0 := by
      have hne : Nonempty (ZMod d) := ⟨0⟩
      rw [coreDetectFam_eq_indFam,
        show scalarEqualityFamily (⁅M, M⁆.subgroupOf M) (hallCore ↥M) H0 (U.subgroupOf M)
            (fun i => ChiefFactorLinearAction.subgroupOfSubmodule e (Sys.L i))
          = indFam (⁅M, M⁆.subgroupOf M)
            (irrKer ℂ ((hallCore ↥M).subgroupOf (⁅M, M⁆.subgroupOf M))
              ((H0 ⊔ ⁅lineFixerInf (hallCore ↥M) H0 (U.subgroupOf M)
                  (fun i => ChiefFactorLinearAction.subgroupOfSubmodule e (Sys.L i)),
                lineFixerInf (hallCore ↥M) H0 (U.subgroupOf M)
                  (fun i => ChiefFactorLinearAction.subgroupOfSubmodule e
                    (Sys.L i))⁆).subgroupOf (⁅M, M⁆.subgroupOf M)))
          from by ext f; rw [mem_scalarEqualityFamily, mem_indFam],
        lineFixerInf_eq_chiefActionKer hscal.iSup_Eline, ← commutator_eq_subgroupOf_commutator]
    exact ScalarCoreCoherence.isCoherent_scalarCoreDetectFam hscal hsub (by rw [hS, hfamily])
      hc.dadeSupportedMap hc.cfInner_dadeSupportedMap (fun _ => hc.coe_dadeSupportedMap _)
      (hc.baselineMapOn hS) (hc.coe_baselineMapOn hS)
  ·
    exact hc.isCoherent_coreDetectFam_of_fixedFree hsub hS
      (fixedFree_of_isIrreducible e (by rw [← hDA]; exact hD.isMulCommutative_A)
        (by rw [← hDA]; exact hirr))
      (hc.baselineMapOn hS) (hc.coe_baselineMapOn hS)

end IsPtypeCoreConfig

end Characters

end PtypeCoreCoherence

end CFSG.FeitThompson
