module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Representations.TypeIINonfrobeniusCrossedColumnData
public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
public import CFSG.FeitThompson.Local.DisjointDSetsNonconjugateMaximals
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.CrossMaximalFirstWitnessValue
import CFSG.FeitThompson.Representations.CoherentNormalIrreducibleConjugation
import CFSG.FeitThompson.Representations.OddNormalInducedBlocksConjPairs
import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers
import CFSG.FeitThompson.OddOrder.LocalTypesConjugationInvariant
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
public import CFSG.FeitThompson.Representations.DadeBlockOrthogonalityCosetConstant
import CFSG.FeitThompson.Representations.TypeThreeFullSupportTiInduction
public import CFSG.FeitThompson.Foundations.CentralSeriesDerivedLength
public import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import CFSG.FeitThompson.Representations.TypeVTwoFamilyCoherenceJoining

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open _root_.CFSG.FeitThompson
open _root_.CFSG.FeitThompson.Prep05

variable {G : Type*} [Group G]

theorem sigSignalizer_eq_sigmaSignalizerOn [Finite G] (M : Subgroup G) :
    sigSignalizer M = Prep09.sigmaSignalizerOn M := by
  classical
  funext a
  by_cases ha : a ∈ sigmaCore M ∧ a ≠ 1
  · have ha' : a ∈ (sigmaCore M : Set G) \ {1} := ⟨ha.1, ha.2⟩
    rw [sigSignalizer, signalizerOn_of_mem ha', Prep09.sigmaSignalizerOn, if_pos ha]
    rfl
  · have ha' : a ∉ (sigmaCore M : Set G) \ {1} := fun h => ha ⟨h.1, h.2⟩
    rw [sigSignalizer, signalizerOn_of_notMem ha', Prep09.sigmaSignalizerOn, if_neg ha]

theorem fixedSet_eq_coreFixedSet (M : Subgroup G) :
    fixedSet M (hallCoreOf M) = Prep09.coreFixedSet (Prep09.hallCoreIn M) M := by
  ext a
  simp only [mem_fixedSet, Prep09.coreFixedSet, Set.mem_ofPred_eq, centralizerIn_eq,
    Prep09.centIn, centralizer_coe_zpowers]
  rfl

theorem hallCoreOf_subgroupOf (M : Subgroup G) :
    (hallCoreOf M).subgroupOf M = hallCore ↥M :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

theorem mem_hallCore_iff_coe_mem_hallCoreOf {M : Subgroup G} {x : ↥M} :
    x ∈ hallCore ↥M ↔ (x : G) ∈ hallCoreOf M := by
  rw [← hallCoreOf_subgroupOf M, Subgroup.mem_subgroupOf]

theorem inf_centralizer_subgroupOf_eq_bot_iff {M Y : Subgroup G} (hYM : Y ≤ M) (x : ↥M) :
    Y.subgroupOf M ⊓ centralizer ({x} : Set ↥M) = ⊥ ↔
      Y ⊓ centralizer ({(x : G)} : Set G) = ⊥ := by
  have hmap : ((Y.subgroupOf M ⊓ centralizer ({x} : Set ↥M)).map M.subtype : Subgroup G)
      = Y ⊓ centralizer ({(x : G)} : Set G) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      mem_centralizer_singleton_iff, Subgroup.coe_subtype]
    exact ⟨fun ⟨w, ⟨hw1, hw2⟩, hwz⟩ => hwz ▸ ⟨hw1, congrArg Subtype.val hw2⟩,
      fun ⟨hz1, hz2⟩ => ⟨⟨z, hYM hz1⟩, ⟨hz1, Subtype.ext hz2⟩, rfl⟩⟩
  rw [← hmap, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]

theorem ambientCoreCentralizerSupport_subgroupOf {M Y : Subgroup G} (hYM : Y ≤ M) :
    ambientCoreCentralizerSupport (Y.subgroupOf M) = fixedSet M Y := by
  rw [ambientCoreCentralizerSupport_eq_image]
  ext a
  simp only [mem_fixedSet, centralizerIn_eq, centralizer_coe_zpowers, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_coreCentralizerSupport] at hx
    exact ⟨x.2, fun h => hx.1 (Subtype.ext h),
      fun hc => hx.2 ((inf_centralizer_subgroupOf_eq_bot_iff hYM x).2 hc)⟩
  · rintro ⟨haM, ha1, hcent⟩
    exact ⟨⟨a, haM⟩, mem_coreCentralizerSupport.2
      ⟨fun h => ha1 (congrArg Subtype.val h),
        fun hc => hcent ((inf_centralizer_subgroupOf_eq_bot_iff hYM ⟨a, haM⟩).1 hc)⟩, rfl⟩

theorem ambientCoreCentralizerSupport_hallCore (M : Subgroup G) :
    ambientCoreCentralizerSupport (G := G) (hallCore ↥M) = fixedSet M (hallCoreOf M) := by
  rw [← hallCoreOf_subgroupOf M, ambientCoreCentralizerSupport_subgroupOf (hallCoreOf_le M)]

theorem ambientPuncturedCore_subgroupOf {M Y : Subgroup G} (hYM : Y ≤ M) :
    ambientPuncturedCore (Y.subgroupOf M) = (Y : Set G) \ {1} := by
  rw [ambientPuncturedCore_eq_image_sdiff]
  ext a
  simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_subgroupOf]
  exact ⟨fun ⟨x, ⟨hx, hx1⟩, hxa⟩ => hxa ▸ ⟨hx, fun h => hx1 (Subtype.ext h)⟩,
    fun ⟨ha, ha1⟩ => ⟨⟨a, hYM ha⟩, ⟨ha, fun h => ha1 (congrArg Subtype.val h)⟩, rfl⟩⟩

theorem ambientPuncturedCore_hallCore (M : Subgroup G) :
    ambientPuncturedCore (G := G) (hallCore ↥M) = (hallCoreOf M : Set G) \ {1} := by
  rw [← hallCoreOf_subgroupOf M, ambientPuncturedCore_subgroupOf (hallCoreOf_le M)]

theorem extendZero_apply_coe' {X : Subgroup G} (f : ↥X → ℂ) (x : ↥X) :
    Prep05.extendZero f (x : G) = f x := X.subtype_injective.extend_apply f 0 x

theorem fixedSet_eq_ambientCoreCentralizerSupport (M : Subgroup G) :
    fixedSet M (hallCoreOf M) = ambientCoreCentralizerSupport (hallCore ↥M) :=
  (ambientCoreCentralizerSupport_hallCore M).symm

theorem tauHall_eq_dadeMapFun [Finite G] (M : Subgroup G) (f : ↥M → ℂ) :
    tauHall M f = dadeMapFun M (fixedSet M (hallCoreOf M)) (sigSignalizer M) f := by
  rw [tauHall, dadeMapFun_def, CFSG.FeitThompson.Proofs.extendZero_eq_extendByZero]

theorem indBetween_eq_indClassFun_of_subgroupOf [Finite G] {M Y : Subgroup G} {K : Subgroup ↥M}
    (hK : Y.subgroupOf M = K) (θ : ↥Y → ℂ) :
    indBetween Y M θ
      = letI := Fintype.ofFinite ↥M
        indClassFun K (fun z : ↥K => Prep05.extendZero θ ((z : ↥M) : G)) := by
  subst hK
  rfl

noncomputable def hallCoreOfEquiv (M : Subgroup G) : ↥(hallCore ↥M) ≃* ↥(hallCoreOf M) :=
  (hallCore ↥M).equivMapOfInjective M.subtype M.subtype_injective

theorem coe_hallCoreOfEquiv (M : Subgroup G) (y : ↥(hallCore ↥M)) :
    ((hallCoreOfEquiv M y : ↥(hallCoreOf M)) : G) = ((y : ↥M) : G) := (rfl)

theorem indBetween_hallCoreOf [Finite G] (M : Subgroup G) (θ : ↥(hallCoreOf M) → ℂ) :
    indBetween (hallCoreOf M) M θ
      = letI := Fintype.ofFinite ↥M
        indClassFun (hallCore ↥M) (fun y => θ (hallCoreOfEquiv M y)) := by
  rw [indBetween_eq_indClassFun_of_subgroupOf (hallCoreOf_subgroupOf M)]
  congr 1
  funext z
  rw [← coe_hallCoreOfEquiv M z, extendZero_apply_coe']

theorem comp_equiv_eq_one_iff {A B : Type*} (e : A ≃ B) (θ : B → ℂ) :
    (fun y => θ (e y)) = (1 : A → ℂ) ↔ θ = (1 : B → ℂ) := by
  refine ⟨fun h => funext fun x => ?_, fun h => by rw [h]; rfl⟩
  obtain ⟨y, rfl⟩ := e.surjective x
  exact congrFun h y

theorem hallIndFam_eq_indFam [Finite G] (M : Subgroup G) :
    hallIndFam M
      = letI := Fintype.ofFinite ↥M
        indFam (hallCore ↥M) (nonprincipalIrr ↥(hallCore ↥M)) := by
  let _ := Fintype.ofFinite ↥M
  ext f
  simp only [hallIndFam, Set.mem_image, Set.mem_ofPred_eq, mem_indFam, mem_nonprincipalIrr]
  constructor
  · rintro ⟨θ, ⟨hθ, hθ1⟩, rfl⟩
    refine ⟨fun y => θ (hallCoreOfEquiv M y),
      ⟨FrobeniusInduction.mem_Irr_comp_mulEquiv hθ (hallCoreOfEquiv M), ?_⟩,
      (indBetween_hallCoreOf M θ).symm⟩
    exact fun h => hθ1 ((comp_equiv_eq_one_iff (hallCoreOfEquiv M).toEquiv θ).1 h)
  · rintro ⟨θ, ⟨hθ, hθ1⟩, rfl⟩
    refine ⟨fun x => θ ((hallCoreOfEquiv M).symm x),
      ⟨FrobeniusInduction.mem_Irr_comp_mulEquiv hθ (hallCoreOfEquiv M).symm, ?_⟩, ?_⟩
    · exact fun h => hθ1 ((comp_equiv_eq_one_iff (hallCoreOfEquiv M).toEquiv.symm θ).1 h)
    · refine (indBetween_hallCoreOf M (fun x => θ ((hallCoreOfEquiv M).symm x))).trans ?_
      simp

theorem mem_irrDetect_iff_not_kerContains {M : Subgroup G} {χ : ↥M → ℂ} :
    χ ∈ irrDetect ℂ (hallCore ↥M) ↔ χ ∈ Irr ↥M ∧ ¬ kerContains (hallCoreOf M) M χ := by
  rw [mem_irrDetect, irrChar_eq_Irr]
  refine and_congr Iff.rfl (not_congr ?_)
  rw [kerContains]
  exact ⟨fun h x hx => mem_charValueKernel.1 (h (mem_hallCore_iff_coe_mem_hallCoreOf.2 hx)),
    fun h x hx => mem_charValueKernel.2 (h x (mem_hallCore_iff_coe_mem_hallCoreOf.1 hx))⟩

theorem isFrobeniusTypeLocalData_of_isTypeI [Finite G] {M : Subgroup G} (hI : IsTypeI M) :
    ∃ U V : Subgroup ↥M, IsFrobeniusTypeLocalData (hallCore ↥M) U V := by
  obtain ⟨E, hE⟩ := hI.exists_frobenius
  obtain ⟨E₁, hE₁E, -, hcomm, hcent⟩ := hE.exists_abelian_normal
  exact ⟨E, E₁, { core_ne_bot := hE.hallCore_ne_bot
                  sup_eq_top := hE.sup_eq_top
                  inf_eq_bot := hE.inf_eq_bot
                  coprime := hE.coprime_card
                  le_complement := hE₁E
                  isMulCommutative := hcomm
                  centralizer_le := hcent }⟩

theorem isFixedPointFreeOn_iff {A B : Subgroup G} :
    IsFixedPointFreeOn A B ↔ ∀ b ∈ B, b ≠ 1 → A ⊓ centralizer ({b} : Set G) = ⊥ := by
  simp only [IsFixedPointFreeOn, centralizerIn_eq, centralizer_coe_zpowers]

theorem isFixedPointFreeOn_conj_smul {A B : Subgroup G} (h : IsFixedPointFreeOn A B) (g : G) :
    IsFixedPointFreeOn (MulAut.conj g • A) (MulAut.conj g • B) := by
  rw [isFixedPointFreeOn_iff] at h ⊢
  intro b hb hb1
  obtain ⟨b₀, hb₀, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hb
  have hb₀1 : b₀ ≠ 1 := fun hc => hb1 (by simp [hc])
  have hkey := h b₀ hb₀ hb₀1
  rw [show ((MulAut.conj g) • b₀ : G) = g * b₀ * g⁻¹ from rfl,
    ← smul_centralizer_singleton g b₀, ← Subgroup.smul_inf, hkey]
  simp

theorem hallCoreOf_conj_smul (M : Subgroup G) (g : G) :
    hallCoreOf (MulAut.conj g • M) = MulAut.conj g • hallCoreOf M := by
  rw [hallCoreOf, hallCoreOf]
  exact (map_map_subtype_hallCore_comm (MulAut.conj g) M).symm

theorem ne_conj_smul_of_not_exists_free_complement {M N E : Subgroup G} (hEN : E ≤ N)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E)
    (hnotFrob : ¬ ∃ D : Subgroup G, D ≤ M ∧
      FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) D ∧
      IsFixedPointFreeOn (hallCoreOf M) D) :
    ∀ g : G, M ≠ MulAut.conj g • N := by
  intro g hMN
  refine hnotFrob ⟨MulAut.conj g • E, ?_, ?_, ?_⟩
  · rw [hMN, Subgroup.pointwise_smul_le_pointwise_smul_iff]
    exact hEN
  · rw [hMN, hallCoreOf_conj_smul]
    exact isInternalSemidirectProduct_conj_smul hsemi g
  · rw [hMN, hallCoreOf_conj_smul]
    exact isFixedPointFreeOn_conj_smul hfree g

theorem dadeSupport_congr {J J' : G → Subgroup G} {a : G} (h : J' a = J a) :
    dadeSupport J' a = dadeSupport J a := by
  ext x
  simp only [mem_dadeSupport_iff, mem_dadeCoset_iff, h]

theorem totalDadeSupport_congr {A : Set G} {J J' : G → Subgroup G} (h : ∀ a ∈ A, J' a = J a) :
    totalDadeSupport A J' = totalDadeSupport A J := by
  ext x
  simp only [mem_totalDadeSupport_iff]
  exact ⟨fun ⟨a, ha, hx⟩ => ⟨a, ha, (dadeSupport_congr (h a ha)) ▸ hx⟩,
    fun ⟨a, ha, hx⟩ => ⟨a, ha, (dadeSupport_congr (h a ha)).symm ▸ hx⟩⟩

theorem sigmaPacketSupport_eq_totalDadeSupport_hallCoreOf [Finite G] {M : Subgroup G}
    (hSM : sigmaCore M = hallCoreOf M) :
    Prep08.sigmaPacketSupport G M
      = totalDadeSupport ((hallCoreOf M : Set G) \ {1}) (sigSignalizer M) := by
  rw [Prep08.sigmaPacketSupport_eq_totalDadeSupport, hSM]
  refine (totalDadeSupport_congr fun a ha => ?_).symm
  rw [sigSignalizer, Prep05.signalizerOn_of_mem (hSM ▸ ha), Prep05.signalizer_eq]
  rfl

theorem fixedSet_eq_sdiff_of_free [Finite G] {N E : Subgroup G}
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E) :
    fixedSet N (hallCoreOf N) = (hallCoreOf N : Set G) \ {1} := by
  have _ : ((hallCoreOf N).subgroupOf N).Normal := hallCoreOf_subgroupOf N ▸ hallCore_normal
  rw [isFixedPointFreeOn_iff] at hfree
  ext a
  simp only [mem_fixedSet, centralizerIn_eq, centralizer_coe_zpowers, Set.mem_sdiff,
    Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨haN, ha1, hcent⟩
    refine ⟨?_, ha1⟩
    by_contra hnot
    exact hcent (inf_centralizer_singleton_eq_bot_of_mem_of_notMem
      hsemi.coe_eq_mul.symm hsemi.inf_eq_bot hfree haN hnot)
  · rintro ⟨haH, ha1⟩
    refine ⟨hallCoreOf_le N haH, ha1, fun hbot => ha1 ?_⟩
    have hmem : a ∈ hallCoreOf N ⊓ centralizer ({a} : Set G) :=
      ⟨haH, mem_centralizer_singleton_iff.2 rfl⟩
    rw [hbot] at hmem
    simpa using hmem

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep05
open scoped ComplexOrder

universe u

variable {G : Type*} [Group G] [Finite G]

theorem isSignedIrr_of_isCoherentAt {N : Subgroup G} {S : Set (↥N → ℂ)}
    {τ : (↥N → ℂ) → (G → ℂ)} {ν : Submodule.span ℤ S →+ (G → ℂ)}
    (hν : IsCoherentAt N S τ ν) {ζ : ↥N → ℂ} (hζIrr : ζ ∈ Irr ↥N)
    (hζ : ζ ∈ Submodule.span ℤ S) : IsSignedIrr (ν ⟨ζ, hζ⟩ : G → ℂ) := by
  have _ : Fintype G := Fintype.ofFinite G
  have _ : Fintype ↥N := Fintype.ofFinite _
  have hnorm : cfInner (ν ⟨ζ, hζ⟩ : G → ℂ) (ν ⟨ζ, hζ⟩ : G → ℂ) = 1 := by
    rw [← cfIP_eq_cfInner, hν.isometry, cfIP_eq_cfInner]
    exact cfInner_self_of_mem_Irr hζIrr
  exact mem_Irr_or_neg_mem_Irr_of_mem_span_Irr_of_cfInner_self_eq_one
    (by rw [← virtualChars_eq_span_Irr]; exact hν.mem_virtualChars _) hnorm

theorem exists_isFTTypeOneLocalSetup
    (h₄ : CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    {G : Type u} [Group G] [Finite G] (hG : Prep05.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M) :
    ∃ U V : Subgroup ↥M, IsFTTypeOneLocalSetup M (hallCore ↥M) U V (sigSignalizer M) := by
  have hG9 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, -, -, hdade, -⟩ := h₄ G hG9 M hM hIM
  obtain ⟨U, V, hloc⟩ := isFrobeniusTypeLocalData_of_isTypeI hIM
  refine ⟨U, V, { odd_natCard := (odd_natCard_lt_natCard_of_ne_top hG.odd_natCard hM.1).2
                  frobeniusType := hloc
                  dadeData := ?_ }⟩
  rw [ambientCoreCentralizerSupport_hallCore, fixedSet_eq_coreFixedSet,
    sigSignalizer_eq_sigmaSignalizerOn]
  exact hdade

theorem existsUnique_tauHall_root_of_isTypeI
    (h₄ : CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    {G : Type u} [Group G] [Finite G] (hG : Prep05.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M) :
    ∀ χ ∈ Irr ↥M, ¬ kerContains (hallCoreOf M) M χ →
      ∃! η : G → ℂ, η ∈ Irr G ∧ η ≠ cconj η ∧
        tauHall M (χ - cconj χ) = η - cconj η := by
  obtain ⟨U, V, hsetup⟩ := exists_isFTTypeOneLocalSetup h₄ hG hM hIM
  intro χ hχIrr hχker
  have hχX : χ ∈ irrDetect ℂ (hallCore ↥M) :=
    mem_irrDetect_iff_not_kerContains.2 ⟨hχIrr, hχker⟩
  have hτ : tauHall M (χ - cconj χ)
      = dadeMapFun M (ambientCoreCentralizerSupport (hallCore ↥M)) (sigSignalizer M)
          (χ - star χ) := by
    rw [cconj_eq_star, tauHall_eq_dadeMapFun, ambientCoreCentralizerSupport_hallCore]
  obtain ⟨η, ⟨hηIrr, hηne, hηeq⟩, huniq⟩ := hsetup.existsUnique_dadeRoot hχX
  refine ⟨η, ⟨hηIrr, fun hc => hηne (by rw [cconj_eq_star] at hc; exact hc.symm),
    by rw [hτ, hηeq, cconj_eq_star]⟩, fun ρ ⟨hρIrr, hρne, hρeq⟩ => ?_⟩
  refine huniq ρ ⟨hρIrr, fun hc => hρne (by rw [cconj_eq_star]; exact hc.symm), ?_⟩
  rw [← hτ, hρeq, cconj_eq_star]

theorem coherentImage_mem_signedRootBlock {N : Subgroup G} [Fintype G] [Fintype ↥N]
    {U V : Subgroup ↥N} {J : G → Subgroup G}
    (hN : IsFTTypeOneLocalSetup N (hallCore ↥N) U V J)
    {S : Set (↥N → ℂ)} (hS : S = indFam (hallCore ↥N) (nonprincipalIrr ↥(hallCore ↥N)))
    {ν : Submodule.span ℤ S →+ (G → ℂ)}
    (hνmem : ∀ f, (ν f : G → ℂ) ∈ virtualChars G)
    (hνiso : ∀ f g, cfInner (ν f : G → ℂ) (ν g : G → ℂ)
      = cfInner (f : ↥N → ℂ) (g : ↥N → ℂ))
    (hνtau : ∀ f : Submodule.span ℤ S, (f : ↥N → ℂ) 1 = 0 →
      (ν f : G → ℂ)
        = dadeMapFun N (ambientCoreCentralizerSupport (hallCore ↥N)) J (f : ↥N → ℂ))
    {ζ : ↥N → ℂ} (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥N) (hζ : ζ ∈ Submodule.span ℤ S) :
    (ν ⟨ζ, hζ⟩ : G → ℂ)
      ∈ signedRootBlock (dadeRoot N (ambientCoreCentralizerSupport (hallCore ↥N)) J) ζ := by
  have hζS' : ζ ∈ indFam (hallCore ↥N) (nonprincipalIrr ↥(hallCore ↥N)) := hS ▸ hζS
  have hζX : ζ ∈ irrDetect ℂ (hallCore ↥N) :=
    irrConstituents_subset_irrDetect _ hζS' (self_mem_irrConstituents_of_mem_Irr hζIrr)
  obtain ⟨hηIrr, hηne, hηeq⟩ := hN.dadeRoot_spec hζX
  set η := dadeRoot N (ambientCoreCentralizerSupport (hallCore ↥N)) J ζ with hη
  have hstarIrr : star η ∈ Irr G := star_mem_Irr hηIrr
  have hstarζS : star ζ ∈ S := by
    rw [hS] at hζS ⊢
    rw [nonprincipalIrr_eq_sdiff_singleton] at hζS ⊢
    exact NormalInducedFamily.star_mem_of_mem rfl hζS
  have hζne : star ζ ≠ ζ := fun hc =>
    ne_conj_of_mem_indFam_nonprincipalIrr hN.odd_natCard _ hζS'
      (funext fun y => (congrFun hc y).symm)
  have hΨsi : (ν ⟨ζ, hζ⟩ : G → ℂ) ∈ signedIrr G := by
    refine mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one ?_ ?_
    · rw [← virtualChars_eq_span_Irr]; exact hνmem _
    · rw [hνiso]; exact cfInner_self_of_mem_Irr hζIrr
  have hg : ζ - star ζ ∈ Submodule.span ℤ S :=
    sub_mem hζ (Submodule.subset_span hstarζS)
  have hg1 : ((⟨ζ - star ζ, hg⟩ : Submodule.span ℤ S) : ↥N → ℂ) 1 = 0 := by
    change (ζ - star ζ) 1 = 0
    simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def, sub_eq_zero]
    exact (conj_apply_one_of_mem_Irr hζIrr).symm
  have hsub : cfInner (η - star η) (ν ⟨ζ, hζ⟩ : G → ℂ) = 1 := by
    rw [← hηeq, ← hνtau ⟨ζ - star ζ, hg⟩ hg1, hνiso ⟨ζ - star ζ, hg⟩ ⟨ζ, hζ⟩]
    change cfInner (ζ - star ζ) ζ = 1
    rw [cfInner_sub_left, cfInner_self_of_mem_Irr hζIrr,
      cfInner_eq_ite_of_mem_Irr (star_mem_Irr hζIrr) hζIrr, if_neg hζne, sub_zero]
  have horth : cfInner η (star η) = 0 := by
    rw [cfInner_eq_ite_of_mem_Irr hηIrr hstarIrr, if_neg fun hc => hηne hc.symm]
  exact signedPair_subset_signedRootBlock _ (self_mem_irrConstituents_of_mem_Irr hζIrr)
    (mem_signedPair.2 (eq_or_eq_neg_of_cfInner_sub_eq_one (Irr_subset_signedIrr hηIrr)
      (Irr_subset_signedIrr hstarIrr) hΨsi horth hsub))

theorem disjoint_totalDadeSupport_of_not_exists_free_complement
    (h₁ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₃ : CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    {G : Type u} [Group G] [Finite G] (hG : Prep05.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : IsCoatom M) (hN : IsCoatom N)
    (hIM : IsTypeI M) (hIN : IsTypeI N)
    {E : Subgroup G} (hEN : E ≤ N)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E)
    (hnotFrob : ¬ ∃ D : Subgroup G, D ≤ M ∧
      FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) D ∧
      IsFixedPointFreeOn (hallCoreOf M) D) :
    Disjoint
      (totalDadeSupport (ambientPuncturedCore (hallCore ↥M)) (sigSignalizer M))
      (totalDadeSupport (ambientCoreCentralizerSupport (hallCore ↥N)) (sigSignalizer N)) := by
  have hG9 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG8 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hSM : sigmaCore M = hallCoreOf M := ((h₃ G hG9 M hM hIM).2.1).symm
  have hSN : sigmaCore N = hallCoreOf N := ((h₃ G hG9 N hN hIN).2.1).symm
  have hTN : ambientCoreCentralizerSupport (G := G) (hallCore ↥N)
      = (hallCoreOf N : Set G) \ {1} := by
    rw [ambientCoreCentralizerSupport_hallCore, fixedSet_eq_sdiff_of_free hsemi hfree]
  have hDM : totalDadeSupport (ambientPuncturedCore (G := G) (hallCore ↥M)) (sigSignalizer M)
      = Prep08.sigmaPacketSupport G M := by
    rw [ambientPuncturedCore_hallCore, sigmaPacketSupport_eq_totalDadeSupport_hallCoreOf hSM]
  have hDN : totalDadeSupport (ambientCoreCentralizerSupport (G := G) (hallCore ↥N))
      (sigSignalizer N) = Prep08.sigmaPacketSupport G N := by
    rw [hTN, sigmaPacketSupport_eq_totalDadeSupport_hallCoreOf hSN]
  rw [hDM, hDN, Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
  exact FTS_nonconjugate_packets_disjoint h₁ h₂ G hG8 N M hN hM fun g =>
    ne_conj_smul_of_not_exists_free_complement hEN hsemi hfree hnotFrob g⁻¹

theorem cfIP_coherentImage_eq_zero_of_mem_block
    (h₁ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₃ : CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₄ : CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    {G : Type u} [Group G] [Finite G] (hG : Prep05.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : IsCoatom M) (hN : IsCoatom N)
    (hIM : IsTypeI M) (hIN : IsTypeI N)
    {E : Subgroup G} (hEN : E ≤ N) (hEbot : E ≠ ⊥)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E)
    (hnotFrob : ¬ ∃ D : Subgroup G, D ≤ M ∧
      FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) D ∧
      IsFixedPointFreeOn (hallCoreOf M) D)
    {ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ)}
    (hν : IsCoherentAt N (hallIndFam N) (tauHall N) ν)
    {ζ : ↥N → ℂ} (hζS : ζ ∈ hallIndFam N) (hζIrr : ζ ∈ Irr ↥N)
    (hζ : ζ ∈ Submodule.span ℤ (hallIndFam N))
    {Ψ : G → ℂ} (hΨ : Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ)) :
    ∀ η : (↥M → ℂ) → (G → ℂ),
      (∀ χ ∈ Irr ↥M, ¬ kerContains (hallCoreOf M) M χ →
        η χ ∈ Irr G ∧ η χ ≠ cconj (η χ) ∧
        tauHall M (χ - cconj χ) = η χ - cconj (η χ)) →
      ∀ θ ∈ hallIndFam M, ∀ χ ∈ Irr ↥M, ¬ kerContains (hallCoreOf M) M χ →
        0 < cfIP θ χ → cfIP Ψ (η χ) = 0 ∧ cfIP Ψ (-(cconj (η χ))) = 0 := by
  have _ : Fintype G := Fintype.ofFinite G
  letI instM : Fintype ↥M := Fintype.ofFinite ↥M
  letI instN : Fintype ↥N := Fintype.ofFinite ↥N
  obtain ⟨UM, VM, hMsetup⟩ := exists_isFTTypeOneLocalSetup h₄ hG hM hIM
  obtain ⟨UN, VN, hNsetup⟩ := exists_isFTTypeOneLocalSetup h₄ hG hN hIN
  have hdisj := disjoint_totalDadeSupport_of_not_exists_free_complement h₁ h₂ h₃ hG hM hN hIM hIN
    hEN hsemi hfree hnotFrob
  have hSNeq : hallIndFam N = indFam (hallCore ↥N) (nonprincipalIrr ↥(hallCore ↥N)) :=
    hallIndFam_eq_indFam N
  have hνtau : ∀ f : Submodule.span ℤ (hallIndFam N), (f : ↥N → ℂ) 1 = 0 →
      (ν f : G → ℂ)
        = dadeMapFun N (ambientCoreCentralizerSupport (hallCore ↥N)) (sigSignalizer N)
            (f : ↥N → ℂ) := by
    intro f hf1
    rw [hν.eq_tau f hf1, tauHall_eq_dadeMapFun, ambientCoreCentralizerSupport_hallCore]
  have hΨblock : Ψ ∈ signedRootBlock
      (dadeRoot N (ambientCoreCentralizerSupport (hallCore ↥N)) (sigSignalizer N)) ζ := by
    rw [hΨ]
    refine coherentImage_mem_signedRootBlock hNsetup hSNeq hν.mem_virtualChars
      (fun f g => ?_) hνtau hζS hζIrr hζ
    rw [← cfIP_eq_cfInner, hν.isometry, cfIP_eq_cfInner]
  have hζS' : ζ ∈ indFam (hallCore ↥N) (nonprincipalIrr ↥(hallCore ↥N)) := hSNeq ▸ hζS
  intro η hη θ hθ χ hχIrr hχker hχpos
  have hθ' : θ ∈ indFam (hallCore ↥M) (nonprincipalIrr ↥(hallCore ↥M)) :=
    hallIndFam_eq_indFam M ▸ hθ
  have hχX : χ ∈ irrDetect ℂ (hallCore ↥M) :=
    mem_irrDetect_iff_not_kerContains.2 ⟨hχIrr, hχker⟩
  obtain ⟨hηIrr, hηne, hηeq⟩ := hη χ hχIrr hχker
  obtain ⟨hrIrr, hrne, hreq⟩ := hMsetup.dadeRoot_spec hχX
  have hηr : dadeRoot M (ambientCoreCentralizerSupport (hallCore ↥M)) (sigSignalizer M) χ
      = η χ := by
    refine eq_of_sub_star_eq_sub_star hηIrr hrIrr
      (fun hc => hηne (by rw [cconj_eq_star]; exact hc.symm)) ?_
    rw [← hreq, ambientCoreCentralizerSupport_hallCore, ← tauHall_eq_dadeMapFun]
    rw [← cconj_eq_star (f := χ), hηeq, cconj_eq_star]
  have hχcon : χ ∈ irrConstituents θ := by
    refine mem_irrConstituents.2 ⟨hχIrr, ?_⟩
    rwa [← cfIP_eq_cfInner]
  have hpair : ∀ a ∈ signedPair (η χ), a ∈ signedRootBlock
      (dadeRoot M (ambientCoreCentralizerSupport (hallCore ↥M)) (sigSignalizer M)) θ := by
    intro a ha
    exact signedPair_subset_signedRootBlock _ hχcon (by rwa [hηr])
  have key : ∀ a ∈ signedPair (η χ), cfIP Ψ a = 0 := by
    intro a ha
    have h0 := cfInner_eq_zero_of_disjoint_oriented hMsetup hNsetup hθ' hζS'
      (Or.inl hdisj) (hpair a ha) hΨblock
    have hc := conj_cfInner a Ψ
    rw [h0, map_zero] at hc
    rw [cfIP_eq_cfInner]
    exact hc.symm
  exact ⟨key _ (self_mem_signedPair _), by
    rw [cconj_eq_star]; exact key _ (neg_star_mem_signedPair _)⟩

theorem FPF_frobenius_coherent_image_other_type_i_blocks
    (h₁ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₃ : CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₄ : CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u}) :
    CFSG.FeitThompson.Statements.FPF_frobenius_coherent_image_other_type_i_blocks.{u} := by
  intro G _ _ hG M N hM hN hIM hIN E hEN hEbot hsemi hfree hnotFrob ν hν ζ hζS hζIrr hζ Ψ hΨ
  refine ⟨existsUnique_tauHall_root_of_isTypeI h₄ hG hM hIM, ?_, ?_⟩
  ·
    rw [hΨ]
    exact isSignedIrr_of_isCoherentAt hν hζIrr hζ
  · exact cfIP_coherentImage_eq_zero_of_mem_block h₁ h₂ h₃ h₄ hG hM hN hIM hIN hEN hEbot
      hsemi hfree hnotFrob hν hζS hζIrr hζ hΨ

end CFSG.FeitThompson.Proofs

end
