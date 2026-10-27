module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Representations.CharacterConstantOutsideSubgroupIntegral
public import CFSG.FeitThompson.Representations.FrobeniusCoherentImageOtherTypeIBlocks
import CFSG.FeitThompson.Local.TypeISupportedByTypeIIFrobenius
import CFSG.FeitThompson.Representations.TypeISupportingGroupConfiguration
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
public import CFSG.FeitThompson.Representations.TypeIInverseDadeDerivedConstancy
import CFSG.FeitThompson.Representations.TypeIIIIVChiefLayerNoncoherence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep05
open scoped ComplexOrder

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_lt_self_of_ne_bot_of_isSolvable {K : Subgroup G} (hK : K ≠ ⊥)
    (hsolv : Group.IsSolvable ↥K) : (⁅K, K⁆ : Subgroup G) < K := by
  have hnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hK
  have hlt : _root_.commutator ↥K < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)
  have hmap : (_root_.commutator ↥K).map K.subtype < (⊤ : Subgroup ↥K).map K.subtype :=
    (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).2 hlt
  rwa [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.subtype_range] at hmap

theorem commutator_hallCoreOf_lt (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M) :
    (⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) < hallCoreOf M :=
  commutator_lt_self_of_ne_bot_of_isSolvable (hallCoreOf_ne_bot hIM)
    (hG.isSolvable_of_ne_top _ fun h => hM.1 (top_le_iff.1 (h ▸ hallCoreOf_le M)))

theorem sdiff_commutator_hallCoreOf_nonempty (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M) :
    ((hallCoreOf M : Set G) \
      ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G)).Nonempty := by
  obtain ⟨x, hxK, hxC⟩ := SetLike.exists_of_lt (commutator_hallCoreOf_lt hG hM hIM)
  exact ⟨x, hxK, hxC⟩

omit [Finite G] in
theorem ne_one_of_mem_sdiff_commutator {K : Subgroup G} {k : G}
    (hk : k ∈ (K : Set G) \ ((⁅K, K⁆ : Subgroup G) : Set G)) : k ≠ 1 :=
  fun h => hk.2 (h ▸ (⁅K, K⁆ : Subgroup G).one_mem)

omit [Finite G] in
theorem centralizerIn_zpowers_eq_centIn (X : Subgroup G) (b : G) :
    centralizerIn X (zpowers b) = Prep09.centIn X {b} := by
  rw [centralizerIn_eq, Prep09.centIn, centralizer_coe_zpowers]

omit [Finite G] in
theorem mem_fixedSet_of_mem_hallCoreOf {M : Subgroup G} {k : G} (hk : k ∈ hallCoreOf M)
    (hk1 : k ≠ 1) : k ∈ fixedSet M (hallCoreOf M) := by
  refine ⟨hallCoreOf_le M hk, hk1, ?_⟩
  intro hbot
  have hmem : k ∈ centralizerIn (hallCoreOf M) (zpowers k) := by
    rw [centralizerIn_eq, Subgroup.mem_inf]
    refine ⟨hk, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (Commute.refl k) n).eq
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hk1 hmem

theorem rhoHall_apply_of_forall_eq {M : Subgroup G} (Ψ : G → ℂ) {k : G}
    (hkA : k ∈ fixedSet M (hallCoreOf M))
    (h : ∀ r ∈ sigSignalizer M k, Ψ (r * k) = Ψ k) : rhoHall M Ψ k = Ψ k := by
  let _ : Fintype G := Fintype.ofFinite G
  rw [rhoHall]
  exact dadeAverage_apply_of_eq_on (A := fixedSet M (hallCoreOf M))
    (H := sigSignalizer M) (χ := Ψ) hkA h

theorem sigSignalizer_eq_bot_of_centralizer_le
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M)
    {k : G} (hk : k ∈ hallCoreOf M) (hk1 : k ≠ 1)
    (hcent : centralizer ({k} : Set G) ≤ M) : sigSignalizer M k = ⊥ := by
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, hsplit, -⟩ := h₇ G hG09 M hM hIM
  have hkA' : k ∈ Prep09.coreFixedSet (Prep09.hallCoreIn M) M := by
    rw [← fixedSet_eq_coreFixedSet]
    exact mem_fixedSet_of_mem_hallCoreOf hk hk1
  obtain ⟨hle, -, -, hinf⟩ := hsplit k hkA'
  rw [sigSignalizer_eq_sigmaSignalizerOn]
  refine le_antisymm ?_ bot_le
  intro x hx
  have hmem : x ∈ Prep09.sigmaSignalizerOn M k ⊓ Prep09.centIn M {k} :=
    Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_inf.2 ⟨hcent (hle hx), hle hx⟩⟩
  rw [hinf] at hmem
  exact hmem

theorem rhoHall_apply_eq_of_centralizer_le
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M)
    (Ψ : G → ℂ) {k : G} (hk : k ∈ hallCoreOf M) (hk1 : k ≠ 1)
    (hcent : centralizer ({k} : Set G) ≤ M) : rhoHall M Ψ k = Ψ k := by
  have hbot := sigSignalizer_eq_bot_of_centralizer_le h₇ hG hM hIM hk hk1 hcent
  refine rhoHall_apply_of_forall_eq Ψ (mem_fixedSet_of_mem_hallCoreOf hk hk1) ?_
  intro r hr
  rw [hbot, Subgroup.mem_bot] at hr
  rw [hr, one_mul]

theorem not_isTypeII_of_not_frobenius
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_complement_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M)
    (hnotFrob : ¬ ∃ D : Subgroup G, D ≤ M ∧
      FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) D ∧
      IsFixedPointFreeOn (hallCoreOf M) D)
    {k : G} (hkA : k ∈ fixedSet M (hallCoreOf M)) (hcent : ¬ centralizer ({k} : Set G) ≤ M)
    {T : Subgroup G} (hT : IsUniqueMaximalOvergroup (centralizer ({k} : Set G)) T) :
    ¬ IsTypeII T := by
  intro hTII
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hkA' : k ∈ Prep09.coreFixedSet (Prep09.hallCoreIn M) M := by
    rw [← fixedSet_eq_coreFixedSet]; exact hkA
  obtain ⟨D, hDM, -, -, hsemi, hfix⟩ :=
    FTS_supporting_type_two_forces_frobenius h₁ h₃ h₅ h₆ G hG09 M hM hIM k hkA' hcent T hT hTII
  exact hnotFrob ⟨D, hDM, hsemi, fun b hb hb1 => by
    rw [centralizerIn_zpowers_eq_centIn]; exact hfix b hb hb1⟩

theorem not_frobenius_of_notMem_hallCoreOf
    {T : Subgroup G} {k : G} (hkT : k ∈ T) (hkH : k ∉ hallCoreOf T)
    (hkc : centralizerIn (hallCoreOf T) (zpowers k) ≠ ⊥) :
    ¬ ∃ D : Subgroup G, D ≤ T ∧
      FreeCore.IsInternalSemidirectProduct T (hallCoreOf T) D ∧
      IsFixedPointFreeOn (hallCoreOf T) D := by
  rintro ⟨D, hDT, hsemi, hfree⟩
  have _ : ((hallCoreOf T).subgroupOf T).Normal := normal_subgroupOf_hallCoreOf T
  refine hkc ?_
  rw [centralizerIn_eq, centralizer_coe_zpowers]
  exact inf_centralizer_singleton_eq_bot_of_mem_of_notMem hsemi.coe_eq_mul.symm hsemi.inf_eq_bot
    (fun e he he1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hfree he he1) hkT hkH

omit [Finite G] in
theorem mem_hallCore_iff_coe_mem_hallCoreOf {T : Subgroup G} (x : ↥T) :
    x ∈ hallCore ↥T ↔ ((x : G) ∈ hallCoreOf T) := by
  rw [← subgroupOf_hallCoreOf T, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem image_coreCentralizerSupportOutsideCore_eq (T : Subgroup G) :
    (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G)
      = Prep09.exteriorFixedSet (Prep09.hallCoreIn T) T := by
  have hA := fixedSet_eq_ambientCoreCentralizerSupport T
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxA, hxH⟩ := mem_coreCentralizerSupportOutsideCore_iff.1 hx
    have hmemA : ((x : ↥T) : G) ∈ fixedSet T (hallCoreOf T) := by
      rw [hA]; exact mem_ambientCoreCentralizerSupport.2 hxA
    refine Prep09.mem_exteriorFixedSet.2
      ⟨x.2, fun hc => hxH ((mem_hallCore_iff_coe_mem_hallCoreOf x).2 hc), ?_⟩
    rw [← centralizerIn_zpowers_eq_centIn]
    exact (mem_fixedSet.1 hmemA).2.2
  · intro ha
    obtain ⟨haT, haH, hac⟩ := Prep09.mem_exteriorFixedSet.1 ha
    have ha1 : a ≠ 1 := fun h1 => haH (h1 ▸ Subgroup.one_mem (Prep09.hallCoreIn T))
    have hmemA : a ∈ fixedSet T (hallCoreOf T) := by
      refine mem_fixedSet.2 ⟨haT, ha1, ?_⟩
      rw [centralizerIn_zpowers_eq_centIn]; exact hac
    rw [hA, ambientCoreCentralizerSupport_eq_image] at hmemA
    obtain ⟨x, hx, rfl⟩ := hmemA
    exact ⟨x, mem_coreCentralizerSupportOutsideCore_iff.2
      ⟨hx, fun hc => haH ((mem_hallCore_iff_coe_mem_hallCoreOf x).1 hc)⟩, rfl⟩

theorem hallIndFam_eq_indFam_hallCore (T : Subgroup G) :
    letI : Fintype ↥T := Fintype.ofFinite _
    hallIndFam T = indFam (hallCore ↥T) (nonprincipalIrr ↥(hallCore ↥T)) := by
  let _ : Fintype ↥T := Fintype.ofFinite _
  have hle : hallCoreOf T ≤ T := hallCoreOf_le T
  have key : hallIndFam T
      = indFam ((hallCoreOf T).subgroupOf T)
          (nonprincipalIrr ↥((hallCoreOf T).subgroupOf T)) := by
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
      · exact (indBetween_eq_indClassFun T _ hle θ).symm
    · rintro ⟨ψ, ⟨hψ, hψ1⟩, rfl⟩
      refine ⟨ψ ∘ (Subgroup.subgroupOfEquivOfLe hle).symm, ⟨?_, ?_⟩, ?_⟩
      · exact FrobeniusInduction.mem_Irr_comp_mulEquiv hψ (Subgroup.subgroupOfEquivOfLe hle).symm
      · intro hcon
        refine hψ1 ?_
        funext y
        have h := congrFun hcon ((Subgroup.subgroupOfEquivOfLe hle) y)
        simpa using h
      · rw [indBetween_eq_indClassFun T _ hle]
        congr 1
  rwa [subgroupOf_hallCoreOf T] at key

theorem isDadeData_fixedSet_hallCoreOf
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {T : Subgroup G} (hT : IsCoatom T) (hIT : IsTypeI T) :
    IsDadeData T (fixedSet T (hallCoreOf T)) (sigSignalizer T) := by
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, -, -, hdade, -, -, -⟩ := h₇ G hG09 T hT hIT
  rw [sigSignalizer_eq_sigmaSignalizerOn, fixedSet_eq_coreFixedSet]; exact hdade

theorem exists_isFrobeniusTypeLocalData_hallCore {T : Subgroup G} (hIT : IsTypeI T) :
    ∃ U U₁ : Subgroup ↥T, IsFrobeniusTypeLocalData (hallCore ↥T) U U₁ := by
  obtain ⟨E, hFrob, -⟩ := hIT.exists_isFrobeniusType
  obtain ⟨E₁, hE₁E, -, hab, hcent⟩ := hFrob.exists_abelian_normal
  exact ⟨E, E₁, { core_ne_bot := hFrob.hallCore_ne_bot
                  sup_eq_top := hFrob.sup_eq_top
                  inf_eq_bot := hFrob.inf_eq_bot
                  coprime := hFrob.coprime_card
                  le_complement := hE₁E
                  isMulCommutative := hab
                  centralizer_le := hcent }⟩

theorem isTIWithNormalizer_image_coreCentralizerSupportOutsideCore
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {T : Subgroup G} (hT : IsCoatom T) (hIT : IsTypeI T)
    (hD : (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G).Nonempty) :
    IsTIWithNormalizer
      (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G) T := by
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, -, -, -, -, hti, -⟩ := h₇ G hG09 T hT hIT
  rw [image_coreCentralizerSupportOutsideCore_eq] at hD ⊢
  exact hti hD

theorem conj_image_eq_iff_mem_of_isTypeI_dade
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {T : Subgroup G} (hT : IsCoatom T) (hIT : IsTypeI T)
    (hD : (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G).Nonempty) :
    ∀ g : G,
      (fun x => g⁻¹ * x * g) ''
        (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G)
        = (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G) ↔ g ∈ T := by
  have hti := isTIWithNormalizer_image_coreCentralizerSupportOutsideCore h₇ hG hT hIT hD
  have hset := setOf_conj_eq_self_eq_normalizer
    (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G)
  intro g
  constructor
  · intro hg
    have hgn : g ∈ Subgroup.normalizer
        (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G) := by
      rw [← SetLike.mem_coe, ← hset]; exact hg
    rwa [hti.normalizer_eq] at hgn
  · intro hg
    have hgn : g ∈ Subgroup.normalizer
        (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G) := by
      rw [hti.normalizer_eq]; exact hg
    have hmem : g ∈ {g : G | (fun x => g⁻¹ * x * g) ''
        (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G)
        = (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G)} := by
      rw [hset]; exact hgn
    exact hmem

theorem inter_conj_image_eq_empty_of_isTypeI_dade
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {T : Subgroup G} (hT : IsCoatom T) (hIT : IsTypeI T)
    (hD : (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G).Nonempty) :
    ∀ g ∉ T,
      (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G) ∩
        (fun x => g⁻¹ * x * g) ''
          (Subtype.val '' coreCentralizerSupportOutsideCore (hallCore ↥T) : Set G) = ∅ := by
  have hti := isTIWithNormalizer_image_coreCentralizerSupportOutsideCore h₇ hG hT hIT hD
  intro g hg
  exact Set.disjoint_iff_inter_eq_empty.1 (hti.disjoint_image_conj_inv hg)

theorem dadeRoot_spec_hallCoreOf
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {T : Subgroup G} (hT : IsCoatom T) (hIT : IsTypeI T) :
    ∀ χ ∈ Irr ↥T, ¬ kerContains (hallCoreOf T) T χ →
      dadeRoot T (fixedSet T (hallCoreOf T)) (sigSignalizer T) χ ∈ Irr G ∧
      dadeRoot T (fixedSet T (hallCoreOf T)) (sigSignalizer T) χ
        ≠ cconj (dadeRoot T (fixedSet T (hallCoreOf T)) (sigSignalizer T) χ) ∧
      tauHall T (χ - cconj χ)
        = dadeRoot T (fixedSet T (hallCoreOf T)) (sigSignalizer T) χ
          - cconj (dadeRoot T (fixedSet T (hallCoreOf T)) (sigSignalizer T) χ) := by
  have hA : fixedSet T (hallCoreOf T) = ambientCoreCentralizerSupport (hallCore ↥T) :=
    fixedSet_eq_ambientCoreCentralizerSupport T
  have hodd : Odd (Nat.card ↥T) := (odd_natCard_lt_natCard_of_ne_top hG.odd_natCard hT.1).2
  intro χ hχ hker
  have hχ' : χ ∈ irrDetect ℂ (hallCore ↥T) :=
    mem_irrDetect_iff_not_kerContains.2 ⟨hχ, hker⟩
  obtain ⟨h1, h2, h3⟩ := dadeRoot_spec (H := hallCore ↥T)
    (isDadeData_fixedSet_hallCoreOf h₇ hG hT hIT) hodd hA hχ'
  refine ⟨h1, fun hcon => h2 hcon.symm, ?_⟩
  rw [show cconj χ = star χ from rfl, tauHall_eq_dadeMapFun]
  exact h3

open scoped ComplexOrder in
theorem isOrthogonal_signedRootBlock_dadeRoot_of_isCoherentAt
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G)
    {N : Subgroup G} (hN : IsCoatom N) (hIN : IsTypeI N)
    {E : Subgroup G} (hEN : E ≤ N) (hEbot : E ≠ ⊥)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E)
    {ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ)}
    (hν : IsCoherentAt N (hallIndFam N) (tauHall N) ν)
    {ζ : ↥N → ℂ} (hζS : ζ ∈ hallIndFam N) (hζIrr : ζ ∈ Irr ↥N)
    (hζ : ζ ∈ Submodule.span ℤ (hallIndFam N))
    {Ψ : G → ℂ} (hΨ : Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ))
    {T : Subgroup G} (hT : IsCoatom T) (hIT : IsTypeI T)
    (hnotFrobT : ¬ ∃ D : Subgroup G, D ≤ T ∧
      FreeCore.IsInternalSemidirectProduct T (hallCoreOf T) D ∧
      IsFixedPointFreeOn (hallCoreOf T) D) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype ↥T := Fintype.ofFinite _
    ∀ θ ∈ indFam (hallCore ↥T) (nonprincipalIrr ↥(hallCore ↥T)),
      ∀ ρ ∈ signedRootBlock
        (dadeRoot T (fixedSet T (hallCoreOf T)) (sigSignalizer T)) θ, IsOrthogonal Ψ ρ := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ↥T := Fintype.ofFinite _
  set η := dadeRoot T (fixedSet T (hallCoreOf T)) (sigSignalizer T) with hη
  have hblock := _root_.CFSG.FeitThompson.Proofs.cfIP_coherentImage_eq_zero_of_mem_block h₂ h₄ h₆ h₇ hG
    hT hN hIT hIN hEN hEbot hsemi hfree hnotFrobT hν hζS hζIrr hζ hΨ η
    (dadeRoot_spec_hallCoreOf h₇ hG hT hIT)
  intro θ hθ ρ hρ
  obtain ⟨χ, hχ, hρχ⟩ := (mem_signedRootBlock η θ).1 hρ
  have hχIrr : χ ∈ Irr ↥T := (mem_irrConstituents.1 hχ).1
  have hχdet : χ ∈ irrDetect ℂ (hallCore ↥T) :=
    irrConstituents_subset_irrDetect (hallCore ↥T) hθ hχ
  have hker : ¬ kerContains (hallCoreOf T) T χ :=
    (mem_irrDetect_iff_not_kerContains.1 hχdet).2
  have hθS : θ ∈ hallIndFam T := by rw [hallIndFam_eq_indFam_hallCore T]; exact hθ
  have hpos : 0 < cfIP θ χ := by rw [cfIP_eq_cfInner]; exact (mem_irrConstituents.1 hχ).2
  obtain ⟨hzero1, hzero2⟩ := hblock θ hθS χ hχIrr hker hpos
  rcases mem_signedPair.1 hρχ with rfl | rfl
  · rw [isOrthogonal_iff, ← cfIP_eq_cfInner]; exact hzero1
  · rw [isOrthogonal_iff, ← cfIP_eq_cfInner]; exact hzero2

theorem coherentImage_apply_mul_hallCoreOf_eq
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_complement_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
    {N : Subgroup G} (hN : IsCoatom N) (hIN : IsTypeI N)
    {E : Subgroup G} (hEN : E ≤ N) (hEbot : E ≠ ⊥)
    (hsemi : FreeCore.IsInternalSemidirectProduct N (hallCoreOf N) E)
    (hfree : IsFixedPointFreeOn (hallCoreOf N) E)
    {ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ)}
    (hν : IsCoherentAt N (hallIndFam N) (tauHall N) ν)
    {ζ : ↥N → ℂ} (hζS : ζ ∈ hallIndFam N) (hζIrr : ζ ∈ Irr ↥N)
    (hζ : ζ ∈ Submodule.span ℤ (hallIndFam N))
    {Ψ : G → ℂ} (hΨ : Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ))
    {T : Subgroup G} (hT : IsCoatom T) (hIT : IsTypeI T)
    (hnotFrobT : ¬ ∃ D : Subgroup G, D ≤ T ∧
      FreeCore.IsInternalSemidirectProduct T (hallCoreOf T) D ∧
      IsFixedPointFreeOn (hallCoreOf T) D)
    {y : G} (hyT : y ∈ fixedSet T (hallCoreOf T)) (hyH : y ∉ hallCoreOf T) :
    ∀ h ∈ hallCoreOf T, Ψ (y * h) = Ψ y := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ↥T := Fintype.ofFinite _
  obtain ⟨U, U₁, hloc⟩ := exists_isFrobeniusTypeLocalData_hallCore hIT
  have hodd : Odd (Nat.card ↥T) := (odd_natCard_lt_natCard_of_ne_top hG.odd_natCard hT.1).2
  have hA : fixedSet T (hallCoreOf T) = ambientCoreCentralizerSupport (hallCore ↥T) :=
    fixedSet_eq_ambientCoreCentralizerSupport T
  have hΨcf : Ψ ∈ classFun G := by
    rw [hΨ]; exact virtualChars_le_classFun (hν.mem_virtualChars _)
  have horth := isOrthogonal_signedRootBlock_dadeRoot_of_isCoherentAt h₂ h₄ h₆ h₇ hG hN hIN
    hEN hEbot hsemi hfree hν hζS hζIrr hζ hΨ hT hIT hnotFrobT
  intro h hh
  have hxT : y ∈ T := (mem_fixedSet.1 hyT).1
  have hxH : (⟨y, hxT⟩ : ↥T) ∉ hallCore ↥T :=
    fun hc => hyH ((mem_hallCore_iff_coe_mem_hallCoreOf (⟨y, hxT⟩ : ↥T)).1 hc)
  have hhH : (⟨h, hallCoreOf_le T hh⟩ : ↥T) ∈ hallCore ↥T :=
    (mem_hallCore_iff_coe_mem_hallCoreOf (⟨h, hallCoreOf_le T hh⟩ : ↥T)).2 hh
  exact apply_mul_eq_of_isOrthogonal_signedRootBlock_dadeRoot
    (isDadeData_fixedSet_hallCoreOf h₇ hG hT hIT) hloc hodd hA rfl
    (conj_image_eq_iff_mem_of_isTypeI_dade h₇ hG hT hIT)
    (inter_conj_image_eq_empty_of_isTypeI_dade h₇ hG hT hIT) hΨcf horth hxH hhH

theorem rhoHall_apply_eq_of_not_centralizer_le
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_complement_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M)
    (hnotFrob : ¬ ∃ D : Subgroup G, D ≤ M ∧
      FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) D ∧
      IsFixedPointFreeOn (hallCoreOf M) D)
    (Ψ : G → ℂ)
    (hconst : ∀ T : Subgroup G, IsCoatom T → IsTypeI T →
      (¬ ∃ D : Subgroup G, D ≤ T ∧
        FreeCore.IsInternalSemidirectProduct T (hallCoreOf T) D ∧
        IsFixedPointFreeOn (hallCoreOf T) D) →
      ∀ y ∈ fixedSet T (hallCoreOf T), y ∉ hallCoreOf T →
        ∀ h ∈ hallCoreOf T, Ψ (y * h) = Ψ y)
    {k : G} (hk : k ∈ hallCoreOf M) (hk1 : k ≠ 1)
    (hcent : ¬ centralizer ({k} : Set G) ≤ M) : rhoHall M Ψ k = Ψ k := by
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hkA : k ∈ fixedSet M (hallCoreOf M) := mem_fixedSet_of_mem_hallCoreOf hk hk1
  have hkA' : k ∈ Prep09.coreFixedSet (Prep09.hallCoreIn M) M := by
    rw [← fixedSet_eq_coreFixedSet]; exact hkA
  obtain ⟨-, -, -, -, -, -, -, -, hesc⟩ := h₇ G hG09 M hM hIM
  obtain ⟨-, T, hT, hTtype, -, -, hTImem, -, hRM, -⟩ := hesc k hkA' hcent
  have hTI : IsTypeI T := by
    rcases hTtype with hTI | hTII
    · exact hTI
    · exact absurd hTII (not_isTypeII_of_not_frobenius h₁ h₃ h₅ h₆ hG hM hIM hnotFrob hkA hcent hT)
  obtain ⟨hkAT, hkout⟩ := hTImem hTI
  have hkT : k ∈ fixedSet T (hallCoreOf T) := by
    rw [fixedSet_eq_coreFixedSet]; exact hkAT
  have hkH : k ∉ hallCoreOf T := fun h => hkout ⟨h, hk1⟩
  have hcosetT :=
    hconst T hT.isCoatom hTI (not_frobenius_of_notMem_hallCoreOf hkT.1 hkH hkT.2.2) k hkT hkH
  refine rhoHall_apply_of_forall_eq Ψ hkA ?_
  intro r hr
  rw [sigSignalizer_eq_sigmaSignalizerOn, hRM] at hr
  obtain ⟨hrH, hrc⟩ := Subgroup.mem_inf.1 hr
  have hcomm : r * k = k * r := ((Subgroup.mem_centralizer_iff.1 hrc) k rfl).symm
  rw [hcomm, hcosetT r hrH]

theorem tauHall_eq_dadeExtend (M : Subgroup G) (f : ↥M → ℂ) :
    tauHall M f = dadeExtend M (fixedSet M (hallCoreOf M)) (sigSignalizer M) f := by
  rw [dadeExtend_eq_dadeSupportExtension, tauHall, extendZero_eq_extendByZero]

omit [Finite G] in
theorem mem_fixedSet_iff_mem_coreCentralizerSupport (M : Subgroup G) (x : ↥M) :
    (x : G) ∈ fixedSet M (hallCoreOf M) ↔ x ∈ coreCentralizerSupport (hallCore ↥M) := by
  rw [fixedSet_eq_ambientCoreCentralizerSupport, mem_ambientCoreCentralizerSupport]

theorem invDadeRoot_spec_of_isTypeI
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M) :
    ∀ χ ∈ Irr ↥M, ¬ kerContains (hallCoreOf M) M χ →
      invDadeRoot M (fixedSet M (hallCoreOf M)) (sigSignalizer M) χ ∈ Irr G ∧
        invDadeRoot M (fixedSet M (hallCoreOf M)) (sigSignalizer M) χ
          ≠ cconj (invDadeRoot M (fixedSet M (hallCoreOf M)) (sigSignalizer M) χ) ∧
        tauHall M (χ - cconj χ)
          = invDadeRoot M (fixedSet M (hallCoreOf M)) (sigSignalizer M) χ
            - cconj (invDadeRoot M (fixedSet M (hallCoreOf M)) (sigSignalizer M) χ) := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ↥M := Fintype.ofFinite _
  have hD := isDadeData_fixedSet_hallCoreOf h₇ hG hM hIM
  have hodd : Odd (Nat.card ↥M) := (odd_natCard_lt_natCard_of_ne_top hG.odd_natCard hM.1).2
  have hA := mem_fixedSet_iff_mem_coreCentralizerSupport M
  intro χ hχ hker
  have hχ' : χ ∈ irrDetect ℂ (hallCore ↥M) :=
    mem_irrDetect_iff_not_kerContains.2 ⟨hχ, hker⟩
  have hτ := isAntirealIsometry_dadeExtend (H := hallCore ↥M) hD hodd hA
  refine ⟨invDadeRoot_mem_Irr hD hodd hA hχ', ?_, ?_⟩
  · have h := hτ.star_root_ne hχ'
    rw [invDadeRoot_eq]
    exact fun hcon => h hcon.symm
  · rw [show cconj χ = star χ from rfl,
      show ∀ f : G → ℂ, cconj f = star f from fun _ => rfl,
      tauHall_eq_dadeExtend]
    exact dadeExtend_sub_star_eq hD hodd hA hχ'

theorem indFam_hallCore_subset_hallIndFam (M : Subgroup G) :
    letI : Fintype ↥M := Fintype.ofFinite _
    indFam (hallCore ↥M) (nonprincipalIrr ↥(hallCore ↥M)) ⊆ hallIndFam M := by
  let _ : Fintype ↥M := Fintype.ofFinite _
  have hsub : (hallCoreOf M).subgroupOf M = hallCore ↥M := subgroupOf_hallCoreOf M
  rw [← hsub]
  intro f hf
  obtain ⟨ψ, hψ, rfl⟩ := (mem_indFam _).1 hf
  have hle : hallCoreOf M ≤ M := hallCoreOf_le M
  set e := Subgroup.subgroupOfEquivOfLe hle with he
  refine ⟨ψ ∘ e.symm, ⟨?_, ?_⟩, ?_⟩
  · exact FrobeniusInduction.mem_Irr_comp_mulEquiv (mem_nonprincipalIrr.1 hψ).1 e.symm
  · intro hcon
    refine (mem_nonprincipalIrr.1 hψ).2 ?_
    funext y
    have h := congrFun hcon (e y)
    simpa using h
  · rw [indBetween_eq_indClassFun M (hallCoreOf M) hle]
    congr 1

omit [Finite G] in
theorem mem_commutator_hallCoreOf_of_mem_commutator (M : Subgroup G)
    {x : ↥(hallCore ↥M)} (hx : x ∈ _root_.commutator ↥(hallCore ↥M)) :
    ((x : ↥M) : G) ∈ (⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) := by
  have h1 : ((x : ↥M)) ∈ (⁅hallCore ↥M, hallCore ↥M⁆ : Subgroup ↥M) := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨x, hx, rfl⟩
  have h2 : ((x : ↥M) : G) ∈ (⁅hallCore ↥M, hallCore ↥M⁆ : Subgroup ↥M).map M.subtype :=
    ⟨(x : ↥M), h1, rfl⟩
  rwa [Subgroup.map_commutator, ← hallCoreOf_eq] at h2

omit [Finite G] in
theorem exists_mem_hallCore_coe_eq (M : Subgroup G) {k : G} (hk : k ∈ hallCoreOf M) :
    ∃ x : ↥(hallCore ↥M), ((x : ↥M) : G) = k := by
  rw [hallCoreOf_eq, Subgroup.mem_map] at hk
  obtain ⟨y, hy, rfl⟩ := hk
  exact ⟨⟨y, hy⟩, rfl⟩

theorem rhoHall_apply_eq_apply_of_notMem_commutator
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M)
    {Ψ : G → ℂ} (hΨcf : Ψ ∈ classFun G)
    (hortho : letI : Fintype G := Fintype.ofFinite G
      letI : Fintype ↥M := Fintype.ofFinite _
      ∀ θ ∈ indFam (hallCore ↥M) (nonprincipalIrr ↥(hallCore ↥M)),
        ∀ ρ ∈ rootPairSet
          (invDadeRoot M (fixedSet M (hallCoreOf M)) (sigSignalizer M)) θ,
          IsOrthogonal Ψ ρ)
    {x y : G}
    (hx : x ∈ (hallCoreOf M : Set G) \ ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G))
    (hy : y ∈ (hallCoreOf M : Set G) \ ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G)) :
    rhoHall M Ψ x = rhoHall M Ψ y := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ↥M := Fintype.ofFinite _
  obtain ⟨U, U₁, hLD⟩ := exists_isFrobeniusTypeLocalData_hallCore hIM
  have hD := isDadeData_fixedSet_hallCoreOf h₇ hG hM hIM
  have hodd : Odd (Nat.card ↥M) := (odd_natCard_lt_natCard_of_ne_top hG.odd_natCard hM.1).2
  have hA := mem_fixedSet_iff_mem_coreCentralizerSupport M
  obtain ⟨a, ha⟩ := exists_mem_hallCore_coe_eq M hx.1
  obtain ⟨b, hb⟩ := exists_mem_hallCore_coe_eq M hy.1
  have ha' : a ∉ _root_.commutator ↥(hallCore ↥M) := fun hcon =>
    hx.2 (ha ▸ mem_commutator_hallCoreOf_of_mem_commutator M hcon)
  have hb' : b ∉ _root_.commutator ↥(hallCore ↥M) := fun hcon =>
    hy.2 (hb ▸ mem_commutator_hallCoreOf_of_mem_commutator M hcon)
  have key := dadeAverage_apply_eq_apply_of_notMem_commutator_invDadeRoot
    (U := U) (U₁ := U₁) hD hodd hLD hA hΨcf hortho ha' hb'
  rw [ha, hb] at key
  exact key

theorem isOrthogonal_of_mem_rootPairSet_invDadeRoot
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M N : Subgroup G} (hM : IsCoatom M) (hN : IsCoatom N)
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
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype ↥M := Fintype.ofFinite _
    ∀ θ ∈ indFam (hallCore ↥M) (nonprincipalIrr ↥(hallCore ↥M)),
      ∀ ρ ∈ rootPairSet
        (invDadeRoot M (fixedSet M (hallCoreOf M)) (sigSignalizer M)) θ,
        IsOrthogonal Ψ ρ := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ↥M := Fintype.ofFinite _
  have key := cfIP_coherentImage_eq_zero_of_mem_block h₂ h₄ h₆ h₇ hG hM hN
    hIM hIN hEN hEbot hsemi hfree hnotFrob hν hζS hζIrr hζ hΨ
    (invDadeRoot M (fixedSet M (hallCoreOf M)) (sigSignalizer M))
    (invDadeRoot_spec_of_isTypeI h₇ hG hM hIM)
  intro θ hθ ρ hρ
  obtain ⟨χ, hχ, hρ'⟩ := mem_rootPairSet.1 hρ
  have hχdet : χ ∈ irrDetect ℂ (hallCore ↥M) := by
    rw [← iUnion_irrConstituents (hallCore ↥M)]
    exact Set.mem_biUnion hθ hχ
  obtain ⟨hχIrr, hker⟩ := mem_irrDetect_iff_not_kerContains.1 hχdet
  have hpos : (0 : ℂ) < cfIP θ χ := by
    rw [cfIP_eq_cfInner]
    exact (mem_irrConstituents.1 hχ).2
  obtain ⟨h1, h2⟩ := key θ (indFam_hallCore_subset_hallIndFam M hθ) χ hχIrr hker hpos
  rw [cfIP_eq_cfInner] at h1 h2
  rcases hρ' with rfl | rfl
  · exact isOrthogonal_iff.2 h1
  · exact isOrthogonal_iff.2 h2

theorem exists_rhoHall_eq_const_on_sdiff_commutator
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_complement_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : IsCoatom M) (hN : IsCoatom N) (hIM : IsTypeI M) (hIN : IsTypeI N)
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
    ∃ c : ℂ, ∀ k ∈ (hallCoreOf M : Set G) \
      ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G), rhoHall M Ψ k = c := by
  obtain ⟨x, hx⟩ := sdiff_commutator_hallCoreOf_nonempty hG hM hIM
  have hΨcf : Ψ ∈ classFun G := by
    rw [hΨ]; exact virtualChars_le_classFun (hν.mem_virtualChars _)
  have hortho := isOrthogonal_of_mem_rootPairSet_invDadeRoot h₂ h₄ h₆ h₇ hG hM hN hIM hIN hEN
    hEbot hsemi hfree hnotFrob hν hζS hζIrr hζ hΨ
  exact ⟨rhoHall M Ψ x, fun k hk =>
    rhoHall_apply_eq_apply_of_notMem_commutator h₇ hG hM hIM hΨcf hortho hk hx⟩

theorem exists_int_eq_of_isCoherentAt_of_eq_const
    (hG : IsMinimalSimpleOdd G) {M N : Subgroup G} (hM : IsCoatom M) (hIM : IsTypeI M)
    {ν : Submodule.span ℤ (hallIndFam N) →+ (G → ℂ)}
    (hν : IsCoherentAt N (hallIndFam N) (tauHall N) ν)
    {ζ : ↥N → ℂ} (hζ : ζ ∈ Submodule.span ℤ (hallIndFam N))
    {Ψ : G → ℂ} (hΨ : Ψ = (ν ⟨ζ, hζ⟩ : G → ℂ))
    {c : ℂ} (hc : ∀ k ∈ (hallCoreOf M : Set G) \
      ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G), Ψ k = c) :
    ∃ n : ℤ, ∀ k ∈ (hallCoreOf M : Set G) \
      ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G), Ψ k = (n : ℂ) := by
  have hmem : Ψ ∈ Submodule.span ℤ (Irr G) := by
    rw [hΨ, ← virtualChars_eq_span_Irr]
    exact hν.mem_virtualChars _
  obtain ⟨n, hn⟩ := exists_int_eq_of_mem_span_Irr_of_eq_of_notMem
    (commutator_hallCoreOf_lt hG hM hIM) hmem fun k hk hk' => hc k ⟨hk, hk'⟩
  exact ⟨n, fun k hk => by rw [hc k hk, hn]⟩

theorem FPF_type_i_second_witness_comparison
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₃ : Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₄ : Statements.FTS_sigma_prime_separation.{u})
    (h₅ : Statements.FTS_type_I_complement_structure.{u})
    (h₆ : Statements.FTS_type_I_core_kappa_identity.{u})
    (h₇ : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FPF_type_i_second_witness_comparison.{u} := by
  intro G _ _ hG M N hM hN hIM hIN E hEN hEbot hsemi hfree hnotFrob ν hν ζ hζS hζIrr hζ Ψ hΨ
  have hconst : ∀ T : Subgroup G, IsCoatom T → IsTypeI T →
      (¬ ∃ D : Subgroup G, D ≤ T ∧
        FreeCore.IsInternalSemidirectProduct T (hallCoreOf T) D ∧
        IsFixedPointFreeOn (hallCoreOf T) D) →
      ∀ y ∈ fixedSet T (hallCoreOf T), y ∉ hallCoreOf T →
        ∀ h ∈ hallCoreOf T, Ψ (y * h) = Ψ y :=
    fun T hT hIT hnotFrobT y hyT hyH =>
      coherentImage_apply_mul_hallCoreOf_eq h₁ h₂ h₃ h₄ h₅ h₆ h₇ hG hN hIN hEN hEbot hsemi
        hfree hν hζS hζIrr hζ hΨ hT hIT hnotFrobT hyT hyH
  have hpt : ∀ k ∈ hallCoreOf M, k ≠ 1 → rhoHall M Ψ k = Ψ k := by
    intro k hk hk1
    by_cases hcent : centralizer ({k} : Set G) ≤ M
    · exact rhoHall_apply_eq_of_centralizer_le h₇ hG hM hIM Ψ hk hk1 hcent
    · exact rhoHall_apply_eq_of_not_centralizer_le h₁ h₃ h₅ h₆ h₇ hG hM hIM hnotFrob Ψ hconst
        hk hk1 hcent
  refine ⟨hpt, sdiff_commutator_hallCoreOf_nonempty hG hM hIM, ?_⟩
  obtain ⟨c, hc⟩ := exists_rhoHall_eq_const_on_sdiff_commutator h₁ h₂ h₃ h₄ h₅ h₆ h₇ hG hM hN
    hIM hIN hEN hEbot hsemi hfree hnotFrob hν hζS hζIrr hζ hΨ
  refine exists_int_eq_of_isCoherentAt_of_eq_const hG hM hIM hν hζ hΨ (c := c) fun k hk => ?_
  rw [← hpt k hk.1 (ne_one_of_mem_sdiff_commutator hk)]
  exact hc k hk

end CFSG.FeitThompson.Proofs

end
