module

public import CFSG.FeitThompson.Representations.PrimeTIFittingInducedFamilyCases
public import CFSG.FeitThompson.Representations.TypePComplementaryFittingNorm
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
public import CFSG.FeitThompson.Representations.TypeIIIVExtendedDadeSupport
public import CFSG.FeitThompson.Local.TauOneFixedLineCentralizerUnique
public import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.Local.SplitPrimeKernelFreeComplement
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
public import CFSG.FeitThompson.Representations.PTypeChiefCoreFamilyCoherent
import CFSG.FeitThompson.Representations.PrincipalColumnProjectionNormalizedPivot
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
import CFSG.FeitThompson.Representations.ActualPairedSupportSaturation
public import CFSG.FeitThompson.Representations.CoherentMapOrientsEqualDegreeRows
public import CFSG.FeitThompson.Representations.CoherentReferenceImageOddNonzeroOffCore
public import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open CFSG.FeitThompson.Prep03

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

theorem IsWitnessedPConfiguration.coprime_natCard_commutator_W₁ {G : Type*} [Group G] [Finite G]
    {M U W₁ W₂ : Subgroup G} (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    (Nat.card ↥(⁅M, M⁆ : Subgroup G)).Coprime (Nat.card ↥W₁) :=
  hc.coprime_natCard_W₁_natCard_commutator.symm

theorem IsWitnessedPConfiguration.natCard_commutator_eq_relIndex {G : Type*} [Group G] [Finite G]
    {M U W₁ W₂ : Subgroup G} (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    Nat.card ↥(⁅M, M⁆ : Subgroup G) = W₁.relIndex M :=
  hc.relIndex_W₁_eq_natCard_commutator.symm

theorem IsWitnessedPConfiguration.isCyclicTIPair_sup_of_isAmbient {G : Type u} [Group G] [Fintype G]
    {M U W₁ W₂ : Subgroup G}
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : IsAmbient G) (hM : IsCoatom M) (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := by
  obtain ⟨-, hpp, hqp, -, -, hpq, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
      M U W₁ W₂ hM hc _ _ rfl rfl
  exact hc.isCyclicTIPair_sup hG.odd_natCard ((Nat.coprime_primes hqp hpp).2 fun h => hpq h.symm)

theorem eq_zero_of_mem_detectInd_commutator {G : Type*} [Group G] [Fintype G]
    {M H : Subgroup G} {f : ↥M → ℂ}
    (hf : f ∈ detectInd M (⁅M, M⁆ : Subgroup G) H) {y : ↥M}
    (hy : (y : G) ∉ (⁅M, M⁆ : Subgroup G)) : f y = 0 := by
  obtain ⟨θ, -, -, rfl⟩ := hf
  have : ((⁅M, M⁆ : Subgroup G).subgroupOf M).Normal := normal_subgroupOf_commutator_self M
  exact indClassFun_eq_zero_of_notMem _ θ (by simpa [Subgroup.mem_subgroupOf] using hy)

theorem isTypeIIWitness_of_isTypeII {G : Type*} [Group G] [Fintype G] {M U W₁ W₂ : Subgroup G}
    (hG : IsAmbient G) (hM : IsCoatom M) (htype : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    CFSG.FeitThompson.Prep09.IsTypeIIWitness M U W₁ W₂ :=
  htype.clauses_of_isWitnessedPConfiguration (hG.forall_isSolvable M hM.1) hc

theorem sigmaCore_eq_hallCoreIn_of_isTypeII {G : Type u} [Group G] [Fintype G] {M : Subgroup G}
    (h₃ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (hG : IsAmbient G) (hM : IsCoatom M) (htype : IsTypeII M) :
    sigmaCore M = Prep03.hallCoreIn M :=
  (h₃ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
    M hM).1 htype

theorem sigmaCore_eq_commutator_of_isTypeIII {G : Type u} [Group G] [Fintype G] {M : Subgroup G}
    (h₃ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (hG : IsAmbient G) (hM : IsCoatom M) (htype : IsTypeIII M) :
    sigmaCore M = (⁅M, M⁆ : Subgroup G) :=
  (h₃ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
    M hM).2 (Or.inl htype)

theorem extendedSupport_isTI_of_isTypeII {G : Type u} [Group G] [Fintype G]
    {M U W₁ W₂ : Subgroup G}
    (h₆ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : IsAmbient G) (hM : IsCoatom M) (htype : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    Prep03.hallCoreIn M = sigmaCore M ∧
      (CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
        CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂)).Nonempty ∧
      (CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
        CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂)) ⊆ (M : Set G) \ {1} ∧
      Subgroup.normalizer (CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M)
          (⁅M, M⁆ : Subgroup G) ∪ CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂)) = M ∧
      ∀ g : G, g ∉ M →
        (CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
            CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂)) ∩
          CFSG.FeitThompson.Prep09.conjSet g (CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M)
            (⁅M, M⁆ : Subgroup G) ∪ CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂)) = ∅ := by
  obtain ⟨hHS, hne, hsub, hnorm, hdisj, -, -⟩ :=
    h₆ G (CFSG.FeitThompson.Proofs.isMinimalSimpleOddOrder_of_isAmbient hG) M U W₁ W₂ hM htype
      (isTypeIIWitness_of_isTypeII hG hM htype hc) _ rfl
  exact ⟨hHS, hne, hsub, hnorm, hdisj⟩

theorem isDadeData_extendedSupport_of_isTypeII {G : Type u} [Group G] [Fintype G]
    {M U W₁ W₂ : Subgroup G}
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : IsAmbient G) (hM : IsCoatom M) (htype : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsDadeData M
      (CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
        CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂))
      (CFSG.FeitThompson.Prep09.hallSignalizerOn M) := by
  obtain ⟨-, -, -, -, -, -, -, hD, -, -, -⟩ :=
    CFSG.FeitThompson.Proofs.FTS_type_II_extended_dade_induction h₅ h₆ G
      (CFSG.FeitThompson.Proofs.isMinimalSimpleOddOrder_of_isAmbient hG) M U W₁ W₂ hM htype
      (isTypeIIWitness_of_isTypeII hG hM htype hc) _ rfl
  exact hD

namespace OrientedCoreFamily

section Transport

variable {G : Type*} [Group G]

theorem subgroupOf_map_subtype_self {M : Subgroup G} (K : Subgroup ↥M) :
    (K.map M.subtype).subgroupOf M = K := by
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

theorem eq_of_map_subtype_eq {M : Subgroup G} {K K' : Subgroup ↥M}
    (h : K.map M.subtype = K'.map M.subtype) : K = K' := by
  have h2 : (K.map M.subtype).subgroupOf M = (K'.map M.subtype).subgroupOf M := by rw [h]
  rwa [subgroupOf_map_subtype_self, subgroupOf_map_subtype_self] at h2

theorem subgroupOf_hallCoreIn (M : Subgroup G) : (Prep03.hallCoreIn M).subgroupOf M = hallCore ↥M :=
  subgroupOf_map_subtype_self _

theorem isMulCommutative_of_map_subtype {M : Subgroup G} {K : Subgroup ↥M}
    (h : IsMulCommutative ↥(K.map M.subtype)) : IsMulCommutative ↥K :=
  isMulCommutative_of_mulEquiv (Subgroup.equivMapOfInjective K M.subtype M.subtype_injective)

theorem le_normalizer_subgroupOf {M A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf M ≤ Subgroup.normalizer ((B.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have h2 := h (mem_subgroupOf.1 ha)
  rw [Subgroup.mem_normalizer_iff] at h2
  simpa [Subgroup.mem_subgroupOf] using h2 (n : G)

theorem le_normalizer_map_subtype {M A : Subgroup G} (hA : A ≤ M) {N : Subgroup ↥M}
    (h : A.subgroupOf M ≤ Subgroup.normalizer ((N : Subgroup ↥M) : Set ↥M)) :
    A ≤ Subgroup.normalizer ((N.map M.subtype : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have hA' : (⟨a, hA ha⟩ : ↥M) ∈ A.subgroupOf M := mem_subgroupOf.2 (by simpa using ha)
  have h2 := h hA'
  rw [Subgroup.mem_normalizer_iff] at h2
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨a, hA ha⟩ * y * ⟨a, hA ha⟩⁻¹, (h2 y).1 hy, by simp⟩
  · rintro ⟨y, hy, hxy⟩
    have hy' : ((y : G)) = a * n * a⁻¹ := hxy
    have hnM : n ∈ M := by
      have hn : n = a⁻¹ * (y : G) * a := by rw [hy']; group
      rw [hn]
      exact M.mul_mem (M.mul_mem (M.inv_mem (hA ha)) y.2) (hA ha)
    refine ⟨⟨n, hnM⟩, (h2 ⟨n, hnM⟩).2 ?_, rfl⟩
    have hyy : (⟨a, hA ha⟩ : ↥M) * ⟨n, hnM⟩ * ⟨a, hA ha⟩⁻¹ = y :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rw [hy'])
    rw [hyy]; exact hy

theorem le_normalizer_of_le_of_isMulCommutative {A N : Subgroup G} [IsMulCommutative ↥A]
    (hNA : N ≤ A) : A ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have hcomm : x * n * x⁻¹ = n := by rw [setLike_mul_comm hx (hNA hn)]; group
    rwa [hcomm]
  · have hnA : n ∈ A := by
      have hrw : n = x⁻¹ * (x * n * x⁻¹) * x := by group
      rw [hrw]
      exact A.mul_mem (A.mul_mem (A.inv_mem hx) (hNA hn)) hx
    have hcomm : x * n * x⁻¹ = n := by rw [setLike_mul_comm hx hnA]; group
    rwa [← hcomm]

theorem map_subtype_coreCentralizer (M U : Subgroup G) (hU : U ≤ M) :
    (coreCentralizer (hallCore ↥M) (U.subgroupOf M)).map M.subtype
      = cent U (Prep03.hallCoreIn M : Set G) := by
  ext x
  simp only [Subgroup.mem_map, mem_coreCentralizer, cent, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff, Prep03.hallCoreIn, Subgroup.coe_subtype]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨hyU, hyc⟩, rfl⟩
    refine ⟨mem_subgroupOf.1 hyU, ?_⟩
    rintro g ⟨h, hh, rfl⟩
    exact congrArg (Subtype.val) (hyc h hh)
  · rintro ⟨hxU, hxc⟩
    refine ⟨⟨x, hU hxU⟩, ⟨mem_subgroupOf.2 (by simpa using hxU), ?_⟩, rfl⟩
    intro h hh
    exact Subtype.ext (by simpa using hxc (h : G) ⟨h, hh, rfl⟩)

end Transport

section Families

variable {G : Type*} [Group G] [Fintype G]

theorem detectInd_eq_indFamDetect (M Y H : Subgroup G) :
    detectInd M Y H
      = indFamDetect (Y.subgroupOf M) ((H.subgroupOf M).subgroupOf (Y.subgroupOf M)) := by
  ext f
  rw [mem_indFamDetect_subgroupOf]
  simp only [detectInd, Set.mem_ofPred_eq, Irr_eq_irrChar, Subgroup.mem_subgroupOf]

theorem subgroupOf_fittingIn (M : Subgroup G) : (Prep03.fittingIn M).subgroupOf M = fittingRaw ↥M :=
  subgroupOf_map_subtype_self _

theorem detectInd_commutator_eq_indFamDetect (M : Subgroup G) :
    detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)
      = indFamDetect (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) := by
  rw [detectInd_eq_indFamDetect, subgroupOf_hallCoreIn, ← commutator_eq_subgroupOf_commutator]

theorem detectInd_fittingIn_eq_indFamDetect (M : Subgroup G) :
    detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M)
      = indFamDetect (fittingRaw ↥M) ((hallCore ↥M).subgroupOf (fittingRaw ↥M)) := by
  rw [detectInd_eq_indFamDetect, subgroupOf_hallCoreIn, subgroupOf_fittingIn]

end Families

section Coherent

variable {G : Type*} [Group G] [Fintype G]

noncomputable def ofSpanHom {L : Subgroup G} {S : Set (↥L → ℂ)}
    (ν : Submodule.span ℤ S →+ virtualChars G) : (↥L → ℂ) → (G → ℂ) := by
  classical
  exact fun f => if h : f ∈ Submodule.span ℤ S then (ν ⟨f, h⟩ : G → ℂ) else 0

theorem ofSpanHom_apply_of_mem {L : Subgroup G} {S : Set (↥L → ℂ)}
    (ν : Submodule.span ℤ S →+ virtualChars G) {f : ↥L → ℂ}
    (hf : f ∈ Submodule.span ℤ S) : ofSpanHom ν f = (ν ⟨f, hf⟩ : G → ℂ) := by
  classical
  simp only [ofSpanHom, dif_pos hf]

theorem ofSpanHom_apply_of_notMem {L : Subgroup G} {S : Set (↥L → ℂ)}
    (ν : Submodule.span ℤ S →+ virtualChars G) {f : ↥L → ℂ}
    (hf : f ∉ Submodule.span ℤ S) : ofSpanHom ν f = 0 := by
  classical
  simp only [ofSpanHom, dif_neg hf]

theorem isAdditiveIsometryOn_ofSpanHom {L : Subgroup G} {S : Set (↥L → ℂ)}
    (ν : Submodule.span ℤ S →+ virtualChars G)
    (hiso : ∀ f g : Submodule.span ℤ S,
      cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ)) :
    IsAdditiveIsometryOn S (ofSpanHom ν) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf g hg
    rw [ofSpanHom_apply_of_mem ν (add_mem hf hg), ofSpanHom_apply_of_mem ν hf,
      ofSpanHom_apply_of_mem ν hg]
    have h : (⟨f + g, add_mem hf hg⟩ : Submodule.span ℤ S) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
    rw [h, map_add]
    rfl
  · intro f hf
    rw [ofSpanHom_apply_of_mem ν hf]
    exact (ν ⟨f, hf⟩).2
  · intro f hf g hg
    rw [ofSpanHom_apply_of_mem ν hf, ofSpanHom_apply_of_mem ν hg]
    exact hiso ⟨f, hf⟩ ⟨g, hg⟩

theorem isAdditiveIsometryOn_ofSpanHom_of_isCoherentWith {L : Subgroup G} {S : Set (↥L → ℂ)}
    {τ : charSpanZero S →+ virtualChars G} {ν : Submodule.span ℤ S →+ virtualChars G}
    (hν : IsCoherentWith S τ ν) : IsAdditiveIsometryOn S (ofSpanHom ν) :=
  isAdditiveIsometryOn_ofSpanHom ν hν.inner_eq

def toSpanHom {L : Subgroup G} {S : Set (↥L → ℂ)}
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : IsAdditiveIsometryOn S ν) :
    Submodule.span ℤ S →+ virtualChars G where
  toFun f := ⟨ν (f : ↥L → ℂ), hν.2.1 _ f.2⟩
  map_zero' := by
    refine Subtype.ext ?_
    have h := hν.1 0 (zero_mem _) 0 (zero_mem _)
    simp only [add_zero] at h
    change ν ((0 : Submodule.span ℤ S) : ↥L → ℂ) = 0
    have h0 : ((0 : Submodule.span ℤ S) : ↥L → ℂ) = 0 := rfl
    rw [h0]
    exact add_eq_left.1 h.symm
  map_add' f g := Subtype.ext (hν.1 _ f.2 _ g.2)

theorem coe_toSpanHom {L : Subgroup G} {S : Set (↥L → ℂ)}
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : IsAdditiveIsometryOn S ν)
    (f : Submodule.span ℤ S) : (toSpanHom hν f : G → ℂ) = ν (f : ↥L → ℂ) := (rfl)

theorem cfInner_toSpanHom {L : Subgroup G} {S : Set (↥L → ℂ)}
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : IsAdditiveIsometryOn S ν)
    (f g : Submodule.span ℤ S) :
    cfInner (toSpanHom hν f : G → ℂ) (toSpanHom hν g : G → ℂ)
      = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) := hν.2.2 _ f.2 _ g.2

theorem ofSpanHom_toSpanHom {L : Subgroup G} {S : Set (↥L → ℂ)}
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : IsAdditiveIsometryOn S ν)
    {f : ↥L → ℂ} (hf : f ∈ Submodule.span ℤ S) : ofSpanHom (toSpanHom hν) f = ν f := by
  rw [ofSpanHom_apply_of_mem _ hf, coe_toSpanHom]

end Coherent

section MinimalCore

variable {G : Type u} [Group G] [Fintype G]

theorem sup_hallCore_subgroupOf_eq_commutator {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    hallCore ↥M ⊔ U.subgroupOf M = commutator ↥M := by
  have hle : (hallCore ↥M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have h : ((hallCore ↥M).map M.subtype ⊔ U).subgroupOf M = (⁅M, M⁆ : Subgroup G).subgroupOf M := by
    rw [hc.sup_hallCore_E]
  rwa [Subgroup.subgroupOf_sup hle hc.le_M_E, subgroupOf_map_subtype_self,
    ← commutator_eq_subgroupOf_commutator] at h

theorem inf_hallCore_subgroupOf_eq_bot {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) : hallCore ↥M ⊓ U.subgroupOf M = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x ⟨hxH, hxU⟩
  have hd := disjoint_iff.1 hc.disjoint_hallCore_E
  have hmem : (x : G) ∈ (hallCore ↥M).map M.subtype ⊓ U := ⟨⟨x, hxH, rfl⟩, mem_subgroupOf.1 hxU⟩
  rw [hd] at hmem
  exact Subtype.ext (by simpa using hmem)

theorem le_hallCore_subgroupOf_W₂ {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) : W₂.subgroupOf M ≤ hallCore ↥M := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hc.le_hallCore_W₂ (mem_subgroupOf.1 hx)
  exact (Subtype.ext hxy : y = x) ▸ hy

theorem coreProduct_eq_fittingRaw {M U : Subgroup G} (hU : U ≤ M)
    (hdir : IsInternalDirectProduct (Prep03.fittingIn M) (Prep03.hallCoreIn M)
      (cent U (Prep03.hallCoreIn M : Set G))) :
    coreProduct (hallCore ↥M) (U.subgroupOf M) = fittingRaw ↥M := by
  have hnormal : (hallCore ↥M).Normal := hallCore_normal
  refine eq_of_map_subtype_eq (SetLike.coe_injective ?_)
  have hR : ((fittingRaw ↥M).map M.subtype : Set G) = (Prep03.fittingIn M : Set G) := rfl
  rw [Subgroup.coe_map, coe_coreProduct, hR, hdir.coe_eq_mul, Set.image_mul, ← Subgroup.coe_map,
    ← Subgroup.coe_map, map_subtype_coreCentralizer M U hU]
  rfl

theorem isPrimeCyclicTIHyp_commutator {M U W₁ W₂ : Subgroup G} (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M) := by
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  rwa [CFSG.FeitThompson.Prep06.derivedOf_eq] at h

theorem isMinimalAbelianCore_of_isWitnessedPConfiguration
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M) := by
  obtain ⟨-, -, hqp, -, -, -, -, hUab, hsemi1, -, -, -, -, -, -, -, -, hmin, -, -, hdir,
    hFab, -, -⟩ :=
    h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
      M U W₁ W₂ hM hc _ _ rfl rfl
  have hHabG : IsMulCommutative ↥(CFSG.FeitThompson.Prep05.hallCoreOf M) :=
    have : IsMulCommutative ↥(CFSG.FeitThompson.Prep05.fittingOf M) := hFab
    isMulCommutative_of_le hdir.left_le
  have hHab : IsMulCommutative ↥(hallCore ↥M) := isMulCommutative_of_map_subtype hHabG
  refine
    { normal := hallCore_normal
      isMulCommutative_core := hHab
      isMulCommutative_compl := CFSG.FeitThompson.Proofs.isMulCommutative_subgroupOf hUab
      right_le := le_hallCore_subgroupOf_W₂ hc
      sup_eq := sup_hallCore_subgroupOf_eq_commutator hc
      inf_eq_bot := inf_hallCore_subgroupOf_eq_bot hc
      le_normalizer := le_normalizer_subgroupOf hc.le_normalizer_E
      prime_natCard := by rwa [natCard_subgroupOf_eq hc.le_M_W₁]
      minimal := ?_ }
  intro N hN hU hW
  have hNG : N.map M.subtype ≤ CFSG.FeitThompson.Prep05.hallCoreOf M := Subgroup.map_mono hN
  have hMnorm : M ≤ Subgroup.normalizer ((N.map M.subtype : Subgroup G) : Set G) := by
    have hHn : CFSG.FeitThompson.Prep05.hallCoreOf M ≤
        Subgroup.normalizer ((N.map M.subtype : Subgroup G) : Set G) := by
      refine le_normalizer_map_subtype (CFSG.FeitThompson.Prep05.hallCoreOf_le M) ?_
      have hrw : (CFSG.FeitThompson.Prep05.hallCoreOf M).subgroupOf M = hallCore ↥M :=
        subgroupOf_map_subtype_self _
      rw [hrw]
      have := hHab
      exact le_normalizer_of_le_of_isMulCommutative hN
    have hUn : U ≤ Subgroup.normalizer ((N.map M.subtype : Subgroup G) : Set G) :=
      le_normalizer_map_subtype hc.le_M_E hU
    have hW₁n : W₁ ≤ Subgroup.normalizer ((N.map M.subtype : Subgroup G) : Set G) :=
      le_normalizer_map_subtype hc.le_M_W₁ hW
    exact le_trans (le_of_eq hsemi1.sup_eq.symm) (sup_le hHn (sup_le hUn hW₁n))
  rcases hmin _ hNG hMnorm with h | h
  · left
    have h2 : (N.map M.subtype).subgroupOf M = (⊥ : Subgroup G).subgroupOf M := by rw [h]
    rwa [subgroupOf_map_subtype_self, Subgroup.bot_subgroupOf] at h2
  · right
    have h2 : (N.map M.subtype).subgroupOf M
        = (CFSG.FeitThompson.Prep05.hallCoreOf M).subgroupOf M := by rw [h]
    rw [CFSG.FeitThompson.Prep05.hallCoreOf_eq] at h2
    rwa [subgroupOf_map_subtype_self, subgroupOf_map_subtype_self] at h2

theorem detectInd_fittingIn_subset_span_detectInd_commutator {M U W₁ W₂ : Subgroup G}
    {σ : classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) →ₗ[ℂ] classFun ↥M}
    [Fintype ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)]
    (h : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hc : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hσ : IsCyclicTIIsometry (W₁.subgroupOf M ⊔ W₂.subgroupOf M) (W₁.subgroupOf M)
      (W₂.subgroupOf M) σ)
    (hF : coreProduct (hallCore ↥M) (U.subgroupOf M) = fittingRaw ↥M) :
    detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M) ⊆
      (Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) : Set (↥M → ℂ)) := by
  have hnorm : (coreProduct (hallCore ↥M) (U.subgroupOf M)).Normal := by
    rw [hF]; exact fittingRaw_normal ↥M
  intro ζ hζ
  rw [detectInd_fittingIn_eq_indFamDetect, ← hF] at hζ
  rw [detectInd_commutator_eq_indFamDetect]
  exact hc.mem_span_indFamDetect_of_mem_indFamDetect_coreProduct (σ := σ) h hσ hζ

theorem apply_one_of_mem_detectInd_fittingIn {M U W₁ W₂ : Subgroup G}
    (h : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hc : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hF : coreProduct (hallCore ↥M) (U.subgroupOf M) = fittingRaw ↥M)
    {ζ : ↥M → ℂ} (hζ : ζ ∈ detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M)) :
    ζ 1 = (Nat.card ↥(W₁.subgroupOf M) : ℂ) *
      ((coreCentralizer (hallCore ↥M) (U.subgroupOf M)).relIndex (U.subgroupOf M) : ℂ) := by
  rw [detectInd_fittingIn_eq_indFamDetect, ← hF] at hζ
  exact hc.apply_one_of_mem_indFamDetect_coreProduct h hζ

theorem comap_subgroupOf_subgroupOfEquivOfLe {M A B : Subgroup G} (hB : B ≤ M) :
    Subgroup.comap (Subgroup.subgroupOfEquivOfLe hB).toMonoidHom (A.subgroupOf B)
      = (A.subgroupOf M).subgroupOf (B.subgroupOf M) := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, Subgroup.subgroupOfEquivOfLe_apply_coe]

theorem relIndex_subgroupOf_eq {M A B : Subgroup G} (hB : B ≤ M) :
    (A.subgroupOf M).relIndex (B.subgroupOf M) = A.relIndex B := by
  rw [Subgroup.relIndex, Subgroup.relIndex, ← comap_subgroupOf_subgroupOfEquivOfLe hB,
    Subgroup.index_comap_of_surjective _ (Subgroup.subgroupOfEquivOfLe hB).surjective]

theorem relIndex_coreCentralizer_eq (M U : Subgroup G) (hU : U ≤ M) :
    (coreCentralizer (hallCore ↥M) (U.subgroupOf M)).relIndex (U.subgroupOf M)
      = (cent U (Prep03.hallCoreIn M : Set G)).relIndex U := by
  have h1 : coreCentralizer (hallCore ↥M) (U.subgroupOf M)
      = (cent U (Prep03.hallCoreIn M : Set G)).subgroupOf M := by
    rw [← map_subtype_coreCentralizer M U hU, subgroupOf_map_subtype_self]
  rw [h1, relIndex_subgroupOf_eq hU]

theorem apply_one_of_mem_detectInd_fittingIn' {M U W₁ W₂ : Subgroup G} (hU : U ≤ M) (h1 : W₁ ≤ M)
    (h : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hc : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hF : coreProduct (hallCore ↥M) (U.subgroupOf M) = fittingRaw ↥M)
    {u : ℕ} (hu : u = (cent U (Prep03.hallCoreIn M : Set G)).relIndex U)
    {ζ : ↥M → ℂ} (hζ : ζ ∈ detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M)) :
    ζ 1 = ((Nat.card ↥W₁ * u : ℕ) : ℂ) := by
  rw [apply_one_of_mem_detectInd_fittingIn h hc hF hζ, natCard_subgroupOf_eq h1,
    relIndex_coreCentralizer_eq M U hU, hu]
  push_cast
  ring

end MinimalCore

section CoherentBaseline

variable {G : Type u} [Group G] [Fintype G]

def coreFixedSupport (M : Subgroup G) : Set ↥M :=
  {x : ↥M | x ∈ commutator ↥M ∧ x ≠ 1 ∧
    hallCore ↥M ⊓ Subgroup.centralizer ({x} : Set ↥M) ≠ ⊥}

theorem mem_coreFixedSupport {M : Subgroup G} {x : ↥M} :
    x ∈ coreFixedSupport M ↔ x ∈ commutator ↥M ∧ x ≠ 1 ∧
      ∃ y ∈ hallCore ↥M, y ≠ 1 ∧ x * y = y * x := by
  simp only [coreFixedSupport, Set.mem_ofPred_eq, ne_eq, Subgroup.ne_bot_iff_exists_ne_one]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨⟨y, hyH, hyc⟩, hy1⟩
    exact ⟨y, hyH, fun h => hy1 (Subtype.ext (by simpa using congrArg Subtype.val h)),
      Subgroup.mem_centralizer_iff.1 hyc x rfl⟩
  · rintro ⟨y, hyH, hy1, hyc⟩
    exact ⟨⟨y, hyH, Subgroup.mem_centralizer_iff.2 fun z hz => hz ▸ hyc⟩,
      fun h => hy1 (by simpa using congrArg Subtype.val h)⟩

theorem coreFixedSupport_subset (M : Subgroup G) :
    coreFixedSupport M ⊆ ((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1} :=
  fun _ hx => ⟨hx.1, hx.2.1⟩

private theorem eq_one_of_conj_eq_one {L : Type*} [Group L] {x t : L}
    (h : t⁻¹ * x * t = 1) : x = 1 :=
  calc x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    _ = t * (1 : L) * t⁻¹ := by rw [h]
    _ = 1 := by group

theorem conj_mem_coreFixedSupport {M : Subgroup G} {x : ↥M} (hx : x ∈ coreFixedSupport M)
    (t : ↥M) : t⁻¹ * x * t ∈ coreFixedSupport M := by
  have hK : (commutator ↥M).Normal := inferInstance
  have hH : (hallCore ↥M).Normal := hallCore_normal
  rw [mem_coreFixedSupport] at hx ⊢
  obtain ⟨hxK, hx1, y, hyH, hy1, hyc⟩ := hx
  refine ⟨by simpa [mul_assoc] using hK.conj_mem x hxK t⁻¹,
    fun h => hx1 (eq_one_of_conj_eq_one h), t⁻¹ * y * t,
    by simpa [mul_assoc] using hH.conj_mem y hyH t⁻¹,
    fun h => hy1 (eq_one_of_conj_eq_one h), ?_⟩
  calc t⁻¹ * x * t * (t⁻¹ * y * t) = t⁻¹ * (x * y) * t := by group
    _ = t⁻¹ * (y * x) * t := by rw [hyc]
    _ = t⁻¹ * y * t * (t⁻¹ * x * t) := by group

theorem coreFixedSupport_conj (M : Subgroup G) (t : ↥M) :
    (fun a => t⁻¹ * a * t) '' coreFixedSupport M = coreFixedSupport M := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_coreFixedSupport hx t
  · intro x hx
    refine ⟨t * x * t⁻¹, ?_, by group⟩
    have h := conj_mem_coreFixedSupport hx t⁻¹
    have he : t⁻¹⁻¹ * x * t⁻¹ = t * x * t⁻¹ := by group
    rwa [he] at h

theorem centralizer_subset_coreFixedSupport (M : Subgroup G) :
    ∀ y ∈ hallCore ↥M, y ≠ 1 →
      ((commutator ↥M ⊓ Subgroup.centralizer ({y} : Set ↥M) : Subgroup ↥M) : Set ↥M) \ {1}
        ⊆ coreFixedSupport M := by
  intro y hy hy1 x ⟨⟨hxK, hxc⟩, hx1⟩
  rw [mem_coreFixedSupport]
  exact ⟨hxK, hx1, y, hy, hy1, (Subgroup.mem_centralizer_iff.1 hxc y rfl).symm⟩

theorem mem_coreFixedSet_iff {H X : Subgroup G} {a : G} :
    a ∈ CFSG.FeitThompson.Prep09.coreFixedSet H X ↔ a ∈ X ∧ a ≠ 1 ∧
      ∃ y ∈ H, y ≠ 1 ∧ a * y = y * a := by
  simp only [CFSG.FeitThompson.Prep09.coreFixedSet, Set.mem_ofPred_eq, CFSG.FeitThompson.Prep09.centIn,
    ne_eq, Subgroup.ne_bot_iff_exists_ne_one]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨⟨y, hyH, hyc⟩, hy1⟩
    exact ⟨y, hyH, fun h => hy1 (by simpa using Subtype.ext h),
      Subgroup.mem_centralizer_iff.1 hyc a rfl⟩
  · rintro ⟨y, hyH, hy1, hyc⟩
    exact ⟨⟨y, hyH, Subgroup.mem_centralizer_iff.2 fun z hz => hz ▸ hyc⟩,
      fun h => hy1 (by simpa using congrArg Subtype.val h)⟩

theorem image_coreFixedSupport (M : Subgroup G) :
    (fun x : ↥M => (x : G)) '' coreFixedSupport M
      = CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) := by
  ext a
  simp only [Set.mem_image, mem_coreFixedSupport, mem_coreFixedSet_iff]
  constructor
  · rintro ⟨x, ⟨hxK, hx1, y, hyH, hy1, hyc⟩, rfl⟩
    refine ⟨?_, fun h => hx1 (Subtype.ext h), (y : G), ⟨y, hyH, rfl⟩,
      fun h => hy1 (Subtype.ext h), congrArg Subtype.val hyc⟩
    rw [commutator_eq_subgroupOf_commutator] at hxK
    exact mem_subgroupOf.1 hxK
  · rintro ⟨haK, ha1, y, ⟨y', hy'H, rfl⟩, hy1, hyc⟩
    have haM : a ∈ M := Subgroup.commutator_le.2
      (fun _ hu _ hv => M.mul_mem (M.mul_mem (M.mul_mem hu hv) (M.inv_mem hu)) (M.inv_mem hv)) haK
    refine ⟨⟨a, haM⟩, ⟨?_, fun h => ha1 (by simpa using congrArg Subtype.val h), y', hy'H,
      fun h => hy1 (by simpa using congrArg Subtype.val h), Subtype.ext (by simpa using hyc)⟩, rfl⟩
    rw [commutator_eq_subgroupOf_commutator]
    exact mem_subgroupOf.2 (by simpa using haK)

theorem map_subgroupOf_sup {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M) :
    ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype) = W₁ ⊔ W₂ := by
  rw [← Subgroup.subgroupOf_sup h1 h2, Subgroup.map_subgroupOf_eq_of_le (sup_le h1 h2)]

theorem cyclicTIDiff_map_subgroupOf {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M) :
    cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
        ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype)
      = cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ := by
  rw [map_subgroupOf_sup h1 h2, Subgroup.map_subgroupOf_eq_of_le h1,
    Subgroup.map_subgroupOf_eq_of_le h2]

theorem mem_cyclicTIset_subgroupOf_iff {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {x : ↥M} : x ∈ cyclicTIset (W₁.subgroupOf M) (W₂.subgroupOf M) ↔
      (x : G) ∈ cyclicTIset W₁ W₂ := by
  rw [mem_cyclicTIset, mem_cyclicTIset, ← Subgroup.subgroupOf_sup h1 h2]
  refine and_congr ⟨mem_subgroupOf.1, mem_subgroupOf.2⟩ (and_congr ?_ ?_) <;>
    exact not_congr ⟨fun h => by simpa using mem_subgroupOf.1 h,
      fun h => mem_subgroupOf.2 (by simpa using h)⟩

theorem image_cyclicTIsetConj_eq {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M) :
    (fun x : ↥M => (x : G)) '' cyclicTIsetConj (W₁.subgroupOf M) (W₂.subgroupOf M)
      = CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂) := by
  ext a
  simp only [Set.mem_image, mem_cyclicTIsetConj, CFSG.FeitThompson.Prep09.conjUnion,
    Set.mem_iUnion, CFSG.FeitThompson.Prep09.conjSet, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨x, ⟨t, v, hv, rfl⟩, rfl⟩
    exact ⟨(t : G), t.2, (v : G), (mem_cyclicTIset_subgroupOf_iff h1 h2).1 hv, by simp⟩
  · rintro ⟨m, hm, v, hv, rfl⟩
    have hvM : v ∈ M := (sup_le h1 h2) (mem_cyclicTIset.1 hv).1
    exact ⟨⟨m, hm⟩⁻¹ * ⟨v, hvM⟩ * ⟨m, hm⟩, ⟨⟨m, hm⟩, ⟨v, hvM⟩,
      (mem_cyclicTIset_subgroupOf_iff h1 h2).2 hv, rfl⟩, by simp⟩

theorem setOf_conj_eq_of_isCyclicTIPair {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂) :
    {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
          ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype)
      = cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
          ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype)}
      = (((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype : Subgroup G) : Set G) := by
  rw [cyclicTIDiff_map_subgroupOf h1 h2, map_subgroupOf_sup h1 h2]
  exact hW.setOf_conj_eq_self

theorem inter_eq_empty_of_isCyclicTIPair {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂) :
    ∀ g ∉ (W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
            ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype)
        ∩ cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
            ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype) = ∅ := by
  rw [cyclicTIDiff_map_subgroupOf h1 h2, map_subgroupOf_sup h1 h2]
  exact hW.inter_eq_empty

theorem isCyclicTIPair_map_subgroupOf {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂) :
    IsCyclicTIPair ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
      ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype) := by
  rw [map_subgroupOf_sup h1 h2, Subgroup.map_subgroupOf_eq_of_le h1,
    Subgroup.map_subgroupOf_eq_of_le h2]
  exact hW

theorem le_normalizer_of_normal_coe {L : Type*} [Group L] (N : Subgroup L) [N.Normal]
    (A : Subgroup L) : A ≤ Subgroup.normalizer (N : Set L) := by
  intro x _
  rw [Subgroup.mem_normalizer_iff]
  intro n
  exact ⟨fun hn => by simpa using ‹N.Normal›.conj_mem n hn x,
    fun hn => by simpa [mul_assoc] using ‹N.Normal›.conj_mem _ hn x⁻¹⟩

theorem isChiefFactor_hallCore_bot
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsChiefFactor (hallCore ↥M) (⊥ : Subgroup ↥M) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hHne, hmin, -, -, -, -, -, -⟩ :=
    h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
      M U W₁ W₂ hM hc _ _ rfl rfl
  have hHneb : hallCore ↥M ≠ ⊥ := fun h =>
    hHne (by rw [CFSG.FeitThompson.Prep05.hallCoreOf_eq, h, Subgroup.map_bot])
  refine { normal_num := hallCore_normal
           normal_den := inferInstance
           lt := bot_lt_iff_ne_bot.2 hHneb
           not_lt_lt := ?_ }
  intro Z hZ hZbot hZlt
  have hN : Z.map M.subtype ≤ CFSG.FeitThompson.Prep05.hallCoreOf M := by
    rw [CFSG.FeitThompson.Prep05.hallCoreOf_eq]; exact Subgroup.map_mono hZlt.le
  have hnorm : M ≤ Subgroup.normalizer ((Z.map M.subtype : Subgroup G) : Set G) :=
    le_normalizer_map_subtype le_rfl (le_normalizer_of_normal_coe Z _)
  rcases hmin _ hN hnorm with h | h
  · refine absurd ?_ hZbot.ne'
    have h2 : (Z.map M.subtype).subgroupOf M = (⊥ : Subgroup G).subgroupOf M := by rw [h]
    rwa [subgroupOf_map_subtype_self, Subgroup.bot_subgroupOf] at h2
  · refine absurd ?_ hZlt.ne
    have h2 : (Z.map M.subtype).subgroupOf M
        = (CFSG.FeitThompson.Prep05.hallCoreOf M).subgroupOf M := by rw [h]
    rw [CFSG.FeitThompson.Prep05.hallCoreOf_eq] at h2
    rwa [subgroupOf_map_subtype_self, subgroupOf_map_subtype_self] at h2

theorem inf_hallCore_centralizer_eq_bot
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    hallCore ↥M ⊓ Subgroup.centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hCHU, -, -, -, -, -, -, -, -⟩ :=
    h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
      M U W₁ W₂ hM hc _ _ rfl rfl
  intro x ⟨hxH, hxc⟩
  have hxG : (x : G) ∈ CFSG.FeitThompson.Prep05.centralizerIn (CFSG.FeitThompson.Prep05.hallCoreOf M) U := by
    refine ⟨⟨x, hxH, rfl⟩, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxc ⟨g, hc.le_M_E hg⟩
      (mem_subgroupOf.2 (by simpa using hg)))
  rw [hCHU] at hxG
  exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hxG))

theorem chiefActionKer_bot (M U : Subgroup G) :
    chiefActionKer (hallCore ↥M) (⊥ : Subgroup ↥M) (U.subgroupOf M)
      = U.subgroupOf M ⊓ Subgroup.centralizer ((hallCore ↥M : Subgroup ↥M) : Set ↥M) := by
  ext u
  rw [mem_chiefActionKer_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun h g hg => ?_, fun h g hg => ?_⟩
  · have h2 := h g hg
    rw [QuotientGroup.eq, Subgroup.mem_bot, inv_mul_eq_one] at h2
    simpa [mul_assoc] using congrArg (fun z => u * z) h2
  · rw [QuotientGroup.eq, Subgroup.mem_bot, inv_mul_eq_one, mul_assoc, h g hg, ← mul_assoc,
      inv_mul_cancel, one_mul]

theorem commutator_eq_bot_of_le_isMulCommutative {L : Type*} [Group L] {C A : Subgroup L}
    [IsMulCommutative ↥A] (h : C ≤ A) : ⁅C, C⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  exact Subgroup.mem_centralizer_iff.2 fun y hy => setLike_mul_comm (h hy) (h hx)

theorem coreDetectFam_bot_eq_indFamDetect (M U : Subgroup G)
    [IsMulCommutative ↥(U.subgroupOf M)] :
    PtypeCoreCoherence.coreDetectFam M U (⊥ : Subgroup ↥M)
      = indFamDetect (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) := by
  have hC : ⁅chiefActionKer (hallCore ↥M) (⊥ : Subgroup ↥M) (U.subgroupOf M),
      chiefActionKer (hallCore ↥M) (⊥ : Subgroup ↥M) (U.subgroupOf M)⁆ = ⊥ :=
    commutator_eq_bot_of_le_isMulCommutative (A := U.subgroupOf M) (chiefActionKer_le _ _ _)
  rw [PtypeCoreCoherence.coreDetectFam_eq_indFam, hC, bot_sup_eq, Subgroup.bot_subgroupOf,
    irrKer_bot, indFamDetect_eq_indFam]

theorem isPtypeCoreConfig_bot
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    PtypeCoreCoherence.IsPtypeCoreConfig M U W₁ W₂ (⊥ : Subgroup ↥M) (coreFixedSupport M)
      (CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
        CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂))
      (CFSG.FeitThompson.Prep09.hallSignalizerOn M) where
  simple := hG.isSimpleGroup
  not_isMulCommutative := hG.not_isMulCommutative
  odd_card := hG.odd_natCard
  solvable_proper := hG.forall_isSolvable
  isCoatom := hM
  isType := Or.inl htype
  isWitnessedPConfiguration := hc
  isChiefFactor := isChiefFactor_hallCore_bot h₂ hG hM hc
  centralizer_le_H0 := inf_hallCore_centralizer_eq_bot h₂ hG hM hc
  A_subset := coreFixedSupport_subset M
  A_conj := coreFixedSupport_conj M
  centralizer_subset_A := centralizer_subset_coreFixedSupport M
  A0_eq := by
    rw [bridgeSupport_eq, Set.image_union, image_coreFixedSupport,
      image_cyclicTIsetConj_eq hc.le_M_W₁ hc.le_M_W₂]
  isDadeData := isDadeData_extendedSupport_of_isTypeII h₅ h₆ hG hM htype hc

theorem exists_isSubcoherent_detectInd_commutator {M W₁ W₂ : Subgroup G} {A : Set ↥M} {A₀ : Set G}
    {T : G → Subgroup G}
    (hodd : Odd (Nat.card G)) (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (h : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    {σ : classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) →ₗ[ℂ] classFun ↥M}
    (hσ : IsCyclicTIIsometry (W₁.subgroupOf M ⊔ W₂.subgroupOf M) (W₁.subgroupOf M)
      (W₂.subgroupOf M) σ)
    (hWH : W₂.subgroupOf M ≤ hallCore ↥M) (hHK : hallCore ↥M ≤ commutator ↥M)
    (hAconj : ∀ t : ↥M, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ hallCore ↥M, y ≠ 1 →
      ((commutator ↥M ⊓ Subgroup.centralizer ({y} : Set ↥M) : Subgroup ↥M) : Set ↥M) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥M => (x : G)) ''
      bridgeSupport A (W₁.subgroupOf M) (W₂.subgroupOf M) ⊆ A₀)
    (hD : IsDadeData M A₀ T)
    (hWpair : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : classFun ↥((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype) →ₗ[ℂ] classFun G}
    (hω : IsCyclicTIIsometry ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
      ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype) ω)
    {S : Finset (↥M → ℂ)}
    (hS : (S : Set (↥M → ℂ))
      = indFamDetect (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M))) :
    ∃ R : (↥M → ℂ) → Finset (G → ℂ), IsSubcoherent S (dadeMapFun M A₀ T) R := by
  classical
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  obtain ⟨R, hR, -⟩ := PrimeDadeSubcoherence.exists_isSubcoherent_indFamDetect (σ := σ) (ω := ω)
    hodd h hσ hWH hHK hAconj hA hA₀ hD
    (setOf_conj_eq_of_isCyclicTIPair h1 h2 hWpair)
    (inter_eq_empty_of_isCyclicTIPair h1 h2 hWpair) hω hS
  exact ⟨R, hR⟩

theorem exists_isCoherentWith_baselineMap
    {M U W₁ W₂ : Subgroup G} {H0 : Subgroup ↥M} [H0.Normal] {A : Set ↥M} {A0 : Set G}
    {T : G → Subgroup G} (hc : PtypeCoreCoherence.IsPtypeCoreConfig M U W₁ W₂ H0 A A0 T)
    {S : Finset (↥M → ℂ)} {R : (↥M → ℂ) → Finset (G → ℂ)}
    (hsub : IsSubcoherent S (dadeMapFun M A0 T) R)
    (hS : (S : Set (↥M → ℂ)) = PtypeCoreCoherence.coreDetectFam M U H0) :
    ∃ (τ : charSpanZero (PtypeCoreCoherence.coreDetectFam M U H0) →+ virtualChars G)
      (ν : Submodule.span ℤ (PtypeCoreCoherence.coreDetectFam M U H0) →+ virtualChars G),
      IsCoherentWith (PtypeCoreCoherence.coreDetectFam M U H0) τ ν ∧
      ∀ (f : Submodule.span ℤ (PtypeCoreCoherence.coreDetectFam M U H0)) (F : dadeDomain M A0),
        (f : ↥M → ℂ) = (F : ↥M → ℂ) →
        (ν f : G → ℂ) = ((dadeMap hc.isDadeData F : classFun G) : G → ℂ) := by
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 (hc.isCoherent_coreDetectFam hsub hS)
  refine ⟨hc.baselineMap, ν, hν, ?_⟩
  refine PrimeDadePivot.coe_nu_eq_coe_dadeMap hc.isDadeData hν fun f F hf => ?_
  rw [hc.coe_baselineMap, coe_dadeMap, hf]

theorem exists_isCoherentWith_detectInd_commutator
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hD : IsDadeData M
      (CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
        CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂))
      (CFSG.FeitThompson.Prep09.hallSignalizerOn M)) :
    ∃ (τ : charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G)
      (ν : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G),
      IsCoherentWith (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) τ ν ∧
      ∀ (f : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)))
        (F : dadeDomain M (CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M)
          (⁅M, M⁆ : Subgroup G) ∪ CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂))),
        (f : ↥M → ℂ) = (F : ↥M → ℂ) →
        (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hUab, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
      M U W₁ W₂ hM hc _ _ rfl rfl
  have hUabM : IsMulCommutative ↥(U.subgroupOf M) :=
    CFSG.FeitThompson.Proofs.isMulCommutative_subgroupOf hUab
  have hcfg := isPtypeCoreConfig_bot h₂ h₅ h₆ hG hM htype hc
  have hfam : PtypeCoreCoherence.coreDetectFam M U (⊥ : Subgroup ↥M)
      = detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) := by
    rw [coreDetectFam_bot_eq_indFamDetect, detectInd_commutator_eq_indFamDetect]
  rw [← hfam]
  have hP := isPrimeCyclicTIHyp_commutator hG.odd_natCard hc
  obtain ⟨σ, hσ⟩ := hP.exists_isCyclicTIIsometry
  obtain ⟨ω, hω⟩ :=
    (isCyclicTIPair_map_subgroupOf hc.le_M_W₁ hc.le_M_W₂
      (hc.isCyclicTIPair_sup_of_isAmbient h₂ hG hM)).exists_isCyclicTIIsometry
  set S : Finset (↥M → ℂ) :=
    indFamDetectFinset (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) with hSdef
  have hSc : (S : Set (↥M → ℂ))
      = indFamDetect (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) := by
    rw [hSdef]; ext f; rw [Finset.mem_coe, mem_indFamDetectFinset]
  have hHK : hallCore ↥M ≤ commutator ↥M := by
    rw [← sup_hallCore_subgroupOf_eq_commutator hc]; exact le_sup_left
  obtain ⟨R, hR⟩ := exists_isSubcoherent_detectInd_commutator (A := coreFixedSupport M)
    hG.odd_natCard hc.le_M_W₁ hc.le_M_W₂ hP hσ (le_hallCore_subgroupOf_W₂ hc) hHK
    (coreFixedSupport_conj M) (centralizer_subset_coreFixedSupport M)
    (by rw [hcfg.A0_eq]) hcfg.isDadeData (hc.isCyclicTIPair_sup_of_isAmbient h₂ hG hM) hω hSc
  exact exists_isCoherentWith_baselineMap hcfg hR
    (by rw [hSc, coreDetectFam_bot_eq_indFamDetect])

theorem commutator_sdiff_one_conj (M : Subgroup G) (t : ↥M) :
    (fun a => t⁻¹ * a * t) '' (((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1})
      = ((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1} := by
  have hN : (commutator ↥M).Normal := inferInstance
  have key : ∀ (x t : ↥M), t⁻¹ * x * t = 1 → x = 1 := by
    intro x t h
    have : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [this, h]; group
  refine Set.Subset.antisymm ?_ ?_
  · rintro a ⟨x, ⟨hxK, hx1⟩, rfl⟩
    refine ⟨by simpa using hN.conj_mem x hxK t⁻¹, fun hc => hx1 ?_⟩
    exact Set.mem_singleton_iff.2 (key x t (Set.mem_singleton_iff.1 hc))
  · intro a ⟨haK, ha1⟩
    refine ⟨t * a * t⁻¹, ⟨by simpa using hN.conj_mem a haK t, fun hc => ha1 ?_⟩, by group⟩
    refine Set.mem_singleton_iff.2 (key a t⁻¹ ?_)
    have h : t * a * t⁻¹ = 1 := Set.mem_singleton_iff.1 hc
    rw [show t⁻¹⁻¹ * a * t⁻¹ = t * a * t⁻¹ from by group, h]

theorem image_bridgeSupport_commutator_eq_dadeA0 {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M)
    (h2 : W₂ ≤ M) :
    (fun x : ↥M => (x : G)) '' bridgeSupport (((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1})
        (W₁.subgroupOf M) (W₂.subgroupOf M)
      = CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂ := by
  rw [bridgeSupport_eq, CFSG.FeitThompson.Prep06.dadeA0, Set.image_union,
    image_cyclicTIsetConj_eq h1 h2]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨y, ⟨hyK, hy1⟩, rfl⟩
    refine ⟨?_, fun hc => hy1 (Subtype.ext hc)⟩
    have h := hyK
    rw [commutator_eq_subgroupOf_commutator] at h
    exact mem_subgroupOf.1 h
  · rintro ⟨hxK, hx1⟩
    refine ⟨⟨x, Subgroup.commutator_le_self M hxK⟩, ⟨?_, ?_⟩, rfl⟩
    · rw [commutator_eq_subgroupOf_commutator]; exact mem_subgroupOf.2 hxK
    · exact fun hc => hx1 (by simpa using congrArg (fun t : ↥M => (t : G)) hc)

theorem isDadeData_dadeA0_of_isTypeIII
    (h₁ : CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsDadeData M (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂) (CFSG.FeitThompson.Prep06.dadeT M) :=
  (_root_.CFSG.FeitThompson.Proofs.FPF_type_iii_v_extended_dade_support h₁ h₃ h₄ h₅ G
    (_root_.CFSG.FeitThompson.Proofs.isMinimalOddSimple_of_isMinimalSimpleOddOrder
      (_root_.CFSG.FeitThompson.Proofs.isMinimalSimpleOddOrder_of_isAmbient hG)) M U W₁ W₂ hM
    (Or.inl htype) hc).2.2.2.1

theorem isPtypeCoreConfig_bot_typeIII
    (h₁ : CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    PtypeCoreCoherence.IsPtypeCoreConfig M U W₁ W₂ (⊥ : Subgroup ↥M)
      (((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1})
      (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂) (CFSG.FeitThompson.Prep06.dadeT M) where
  simple := hG.isSimpleGroup
  not_isMulCommutative := hG.not_isMulCommutative
  odd_card := hG.odd_natCard
  solvable_proper := hG.forall_isSolvable
  isCoatom := hM
  isType := Or.inr (Or.inl htype)
  isWitnessedPConfiguration := hc
  isChiefFactor := isChiefFactor_hallCore_bot h₂ hG hM hc
  centralizer_le_H0 := inf_hallCore_centralizer_eq_bot h₂ hG hM hc
  A_subset := le_rfl
  A_conj := commutator_sdiff_one_conj M
  centralizer_subset_A := fun _ _ _ _ hx => ⟨hx.1.1, hx.2⟩
  A0_eq := (image_bridgeSupport_commutator_eq_dadeA0 hc.le_M_W₁ hc.le_M_W₂).symm
  isDadeData := isDadeData_dadeA0_of_isTypeIII h₁ h₃ h₄ h₅ hG hM htype hc

theorem exists_isCoherentWith_detectInd_commutator_typeIII
    (h₁ : CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hD : IsDadeData M (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂) (CFSG.FeitThompson.Prep06.dadeT M)) :
    ∃ (τ : charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G)
      (ν : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G),
      IsCoherentWith (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) τ ν ∧
      ∀ (f : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)))
        (F : dadeDomain M (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂)),
        (f : ↥M → ℂ) = (F : ↥M → ℂ) →
        (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hUab, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
      M U W₁ W₂ hM hc _ _ rfl rfl
  have hUabM : IsMulCommutative ↥(U.subgroupOf M) :=
    _root_.CFSG.FeitThompson.Proofs.isMulCommutative_subgroupOf hUab
  have hcfg := isPtypeCoreConfig_bot_typeIII h₁ h₂ h₃ h₄ h₅ hG hM htype hc
  have hfam : PtypeCoreCoherence.coreDetectFam M U (⊥ : Subgroup ↥M)
      = detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) := by
    rw [coreDetectFam_bot_eq_indFamDetect, detectInd_commutator_eq_indFamDetect]
  rw [← hfam]
  have hP := isPrimeCyclicTIHyp_commutator hG.odd_natCard hc
  obtain ⟨σ, hσ⟩ := hP.exists_isCyclicTIIsometry
  obtain ⟨ω, hω⟩ :=
    (isCyclicTIPair_map_subgroupOf hc.le_M_W₁ hc.le_M_W₂
      (hc.isCyclicTIPair_sup_of_isAmbient h₂ hG hM)).exists_isCyclicTIIsometry
  set S : Finset (↥M → ℂ) :=
    indFamDetectFinset (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) with hSdef
  have hSc : (S : Set (↥M → ℂ))
      = indFamDetect (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) := by
    rw [hSdef]; ext f; rw [Finset.mem_coe, mem_indFamDetectFinset]
  have hHK : hallCore ↥M ≤ commutator ↥M := by
    rw [← sup_hallCore_subgroupOf_eq_commutator hc]; exact le_sup_left
  obtain ⟨R, hR⟩ := exists_isSubcoherent_detectInd_commutator
    (A := ((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1})
    hG.odd_natCard hc.le_M_W₁ hc.le_M_W₂ hP hσ (le_hallCore_subgroupOf_W₂ hc) hHK
    (commutator_sdiff_one_conj M) (fun _ _ _ _ hx => ⟨hx.1.1, hx.2⟩)
    (by rw [hcfg.A0_eq]) hcfg.isDadeData (hc.isCyclicTIPair_sup_of_isAmbient h₂ hG hM) hω hSc
  exact exists_isCoherentWith_baselineMap hcfg hR
    (by rw [hSc, coreDetectFam_bot_eq_indFamDetect])

theorem cyclicTIDiff_sup_subset_dadeA0 {M W₁ W₂ : Subgroup G} :
    cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ ⊆ CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂ := by
  intro v hv
  refine Or.inr (Set.mem_iUnion₂.2 ⟨(1 : G), one_mem M, v, ?_, by simp⟩)
  rw [mem_cyclicTIset]
  rwa [mem_cyclicTIDiff] at hv

theorem eq_zero_of_mem_charSpanZero_detectInd_commutator_typeIII
    (h₁ : CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) [IsMulCommutative ↥(U.subgroupOf M)]
    {f : ↥M → ℂ} (hf : f ∈ charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)))
    (x : ↥M) (hx : (x : G) ∉ CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂) :
    f x = 0 := by
  have hcfg := isPtypeCoreConfig_bot_typeIII h₁ h₂ h₃ h₄ h₅ hG hM htype hc
  have hfam : PtypeCoreCoherence.coreDetectFam M U (⊥ : Subgroup ↥M)
      = detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) := by
    rw [coreDetectFam_bot_eq_indFamDetect, detectInd_commutator_eq_indFamDetect]
  rw [← hfam] at hf
  refine hcfg.eq_zero_of_mem_charSpanZero hf fun hxA => ?_
  refine hx ?_
  rw [← image_bridgeSupport_commutator_eq_dadeA0 hc.le_M_W₁ hc.le_M_W₂, bridgeSupport_eq]
  exact ⟨x, Or.inl hxA, rfl⟩

theorem star_mem_detectInd_commutator (M : Subgroup G) {χ : ↥M → ℂ}
    (hχ : χ ∈ detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) :
    star χ ∈ detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) := by
  rw [detectInd_commutator_eq_indFamDetect] at hχ ⊢
  exact PrimeDadeSubcoherence.star_mem_indFamDetect hχ

theorem eq_zero_of_mem_charSpanZero_detectInd_commutator
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) [IsMulCommutative ↥(U.subgroupOf M)]
    {f : ↥M → ℂ} (hf : f ∈ charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)))
    (x : ↥M)
    (hx : (x : G) ∉ CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
      CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂)) :
    f x = 0 := by
  have hcfg := isPtypeCoreConfig_bot h₂ h₅ h₆ hG hM htype hc
  have hfam : PtypeCoreCoherence.coreDetectFam M U (⊥ : Subgroup ↥M)
      = detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) := by
    rw [coreDetectFam_bot_eq_indFamDetect, detectInd_commutator_eq_indFamDetect]
  rw [← hfam] at hf
  refine hcfg.eq_zero_of_mem_charSpanZero hf fun hxA => ?_
  exact hx (Or.inl (by rw [← image_coreFixedSupport]; exact ⟨x, hxA, rfl⟩))

theorem cyclicTIDiff_subset_extendedSupport {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M) :
    cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
        ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype)
      ⊆ CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
        CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂) := by
  rw [cyclicTIDiff_map_subgroupOf h1 h2]
  intro v hv
  refine Or.inr (Set.mem_iUnion₂.2 ⟨(1 : G), one_mem M, v, ?_, by simp⟩)
  rw [mem_cyclicTIset]
  rwa [mem_cyclicTIDiff] at hv

end CoherentBaseline

section SigmaLocal

variable {G : Type u} [Group G] [Fintype G]

noncomputable def supSubgroupOfEquiv {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M) :
    ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) ≃* ↥(W₁ ⊔ W₂) :=
  (MulEquiv.subgroupCongr (Subgroup.subgroupOf_sup h1 h2).symm).trans
    (Subgroup.subgroupOfEquivOfLe (sup_le h1 h2))

theorem coe_supSubgroupOfEquiv {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (z : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) :
    ((supSubgroupOfEquiv h1 h2 z : ↥(W₁ ⊔ W₂)) : G) = ((z : ↥M) : G) := (rfl)

theorem coe_supSubgroupOfEquiv_symm {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (z : ↥(W₁ ⊔ W₂)) :
    (((supSubgroupOfEquiv h1 h2).symm z : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) : ↥M)
      = ⟨(z : G), sup_le h1 h2 z.2⟩ := by
  refine Subtype.ext ?_
  have h := coe_supSubgroupOfEquiv h1 h2 ((supSubgroupOfEquiv h1 h2).symm z)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem mem_cyclicTIDiff_subgroupOf_iff {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (x : ↥M) :
    x ∈ cyclicTIDiff (W₁.subgroupOf M ⊔ W₂.subgroupOf M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      ↔ (x : G) ∈ cyclicTIset W₁ W₂ := by
  rw [mem_cyclicTIDiff, mem_cyclicTIset, ← Subgroup.subgroupOf_sup h1 h2]
  refine and_congr ⟨mem_subgroupOf.1, mem_subgroupOf.2⟩ (and_congr ?_ ?_) <;>
    exact not_congr ⟨fun h => by simpa using mem_subgroupOf.1 h,
      fun h => mem_subgroupOf.2 (by simpa using h)⟩

noncomputable def sigmaLocalHom {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} (hσ : IsTIExtension W₁ W₂ M σ) :
    classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) →ₗ[ℂ] classFun ↥M :=
  LinearMap.codRestrict _
    { toFun := fun f => σ ((f : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) → ℂ) ∘
        (supSubgroupOfEquiv h1 h2).symm)
      map_add' := fun _ _ => hσ.map_add _ _
      map_smul' := fun c _ => hσ.map_smul c _ }
    (fun f => hσ.maps_classFun _ (mem_classFun_comp_mulEquiv (supSubgroupOfEquiv h1 h2).symm f.2))

theorem coe_sigmaLocalHom {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} (hσ : IsTIExtension W₁ W₂ M σ)
    (f : classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) :
    (sigmaLocalHom h1 h2 hσ f : ↥M → ℂ)
      = σ ((f : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) → ℂ) ∘
        (supSubgroupOfEquiv h1 h2).symm) := (rfl)

theorem isCyclicTIIsometry_sigmaLocalHom {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} (hσ : IsTIExtension W₁ W₂ M σ) :
    IsCyclicTIIsometry (W₁.subgroupOf M ⊔ W₂.subgroupOf M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (sigmaLocalHom h1 h2 hσ) where
  inner_eq f g := by
    rw [coe_sigmaLocalHom, coe_sigmaLocalHom, hσ.inner_eq,
      CFSG.FeitThompson.Proofs.Recip.cfInner_comp]
  map_virtualChars f hf := by
    rw [coe_sigmaLocalHom]
    exact hσ.maps_virtualChars _
      (CFSG.FeitThompson.Proofs.Recip.virtualChars_comp (supSubgroupOfEquiv h1 h2).symm hf)
  map_principalClassFun := by
    refine Subtype.ext ?_
    rw [coe_sigmaLocalHom, coe_principalClassFun, coe_principalClassFun]
    have h1' : (1 : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) → ℂ) ∘
        (supSubgroupOfEquiv h1 h2).symm = (1 : ↥(W₁ ⊔ W₂) → ℂ) := rfl
    rw [h1', hσ.map_one]
  eq_indClassFun f hf := by
    rw [coe_sigmaLocalHom]
    have hf' : ∀ z : ↥(W₁ ⊔ W₂), (z : G) ∉ cyclicTIset W₁ W₂ →
        ((f : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) → ℂ) ∘
          (supSubgroupOfEquiv h1 h2).symm) z = 0 := by
      intro z hz
      refine hf _ fun hzz => hz ?_
      have h := (mem_cyclicTIDiff_subgroupOf_iff h1 h2
        (((supSubgroupOfEquiv h1 h2).symm z : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) : ↥M)).1 hzz
      rwa [coe_supSubgroupOfEquiv_symm] at h
    rw [hσ.eq_ind _ hf']
    exact CFSG.FeitThompson.Proofs.Recip.indClassFun_congr' (Subgroup.subgroupOf_sup h1 h2)
      (fun y => (f : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) → ℂ) ⟨(y : ↥M), by
        rw [← Subgroup.subgroupOf_sup h1 h2]; exact y.2⟩) (f : _ → ℂ) fun _ _ _ => rfl

end SigmaLocal

section RowFamily

variable {G : Type u} [Group G] [Fintype G]

noncomputable def irrEquivOfMulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Irr B ≃ Irr A where
  toFun χ := ⟨(χ : B → ℂ) ∘ e, FrobeniusInduction.mem_Irr_comp_mulEquiv χ.2 e⟩
  invFun χ := ⟨(χ : A → ℂ) ∘ e.symm, FrobeniusInduction.mem_Irr_comp_mulEquiv χ.2 e.symm⟩
  left_inv χ := Subtype.ext (by funext x; simp)
  right_inv χ := Subtype.ext (by funext x; simp)

theorem coe_irrEquivOfMulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (χ : Irr B) :
    ((irrEquivOfMulEquiv e χ : Irr A) : A → ℂ) = (χ : B → ℂ) ∘ e := (rfl)

noncomputable def localIrrEquiv {M W : Subgroup G} (h : W ≤ M) {I : Type*} (α : I → ↥W → ℂ)
    (hα : ∀ i, α i ∈ Irr ↥W) (hinj : Function.Injective α)
    (hsurj : ∀ χ ∈ Irr ↥W, ∃ i, α i = χ) : I ≃ Irr ↥(W.subgroupOf M) :=
  (irrEquivOfEnum α hα hinj hsurj).trans (irrEquivOfMulEquiv (Subgroup.subgroupOfEquivOfLe h))

theorem coe_localIrrEquiv {M W : Subgroup G} (h : W ≤ M) {I : Type*} (α : I → ↥W → ℂ)
    (hα : ∀ i, α i ∈ Irr ↥W) (hinj : Function.Injective α)
    (hsurj : ∀ χ ∈ Irr ↥W, ∃ i, α i = χ) (i : I) :
    ((localIrrEquiv h α hα hinj hsurj i : Irr ↥(W.subgroupOf M)) : ↥(W.subgroupOf M) → ℂ)
      = α i ∘ (Subgroup.subgroupOfEquivOfLe h) := by
  rw [localIrrEquiv, Equiv.trans_apply, coe_irrEquivOfMulEquiv, coe_irrEquivOfEnum_apply]

theorem localIrrEquiv_eq_principalIrr {M W : Subgroup G} (h : W ≤ M) {I : Type*} (α : I → ↥W → ℂ)
    (hα : ∀ i, α i ∈ Irr ↥W) (hinj : Function.Injective α)
    (hsurj : ∀ χ ∈ Irr ↥W, ∃ i, α i = χ) {i : I} (hi : α i = 1) :
    localIrrEquiv h α hα hinj hsurj i = principalIrr ↥(W.subgroupOf M) :=
  Subtype.ext (by rw [coe_localIrrEquiv, hi, coe_principalIrr]; rfl)

theorem localIrrEquiv_ne_principalIrr {M W : Subgroup G} (h : W ≤ M) {I : Type*} (α : I → ↥W → ℂ)
    (hα : ∀ i, α i ∈ Irr ↥W) (hinj : Function.Injective α)
    (hsurj : ∀ χ ∈ Irr ↥W, ∃ i, α i = χ) {i i0 : I} (hi0 : α i0 = 1) (hi : i ≠ i0) :
    localIrrEquiv h α hα hinj hsurj i ≠ principalIrr ↥(W.subgroupOf M) := by
  rw [← localIrrEquiv_eq_principalIrr h α hα hinj hsurj hi0]
  exact fun hc => hi ((localIrrEquiv h α hα hinj hsurj).injective hc)

theorem prodChar_comp_supSubgroupOfEquiv {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hW : IsCyclicTIPair (W₁.subgroupOf M ⊔ W₂.subgroupOf M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    {lam : ↥W₁ → ℂ} {mu : ↥W₂ → ℂ} {f : ↥(W₁ ⊔ W₂) → ℂ}
    {lam' : ↥(W₁.subgroupOf M) → ℂ} {mu' : ↥(W₂.subgroupOf M) → ℂ}
    (hlam' : lam' = lam ∘ (Subgroup.subgroupOfEquivOfLe h1))
    (hmu' : mu' = mu ∘ (Subgroup.subgroupOfEquivOfLe h2))
    (hf : ∀ (x : ↥W₁) (y : ↥W₂) (z : ↥(W₁ ⊔ W₂)), (z : G) = (x : G) * (y : G) →
      f z = lam x * mu y) :
    hW.prodChar lam' mu' = f ∘ (supSubgroupOfEquiv h1 h2) := by
  subst hlam' hmu'
  refine (prodChar_eq_of_tensor hW ?_).symm
  intro x y z hz
  refine hf ((Subgroup.subgroupOfEquivOfLe h1) x) ((Subgroup.subgroupOfEquivOfLe h2) y)
    ((supSubgroupOfEquiv h1 h2) z) ?_
  rw [coe_supSubgroupOfEquiv, Subgroup.subgroupOfEquivOfLe_apply_coe,
    Subgroup.subgroupOfEquivOfLe_apply_coe]
  exact congrArg (fun t : ↥M => (t : G)) hz

theorem coe_sigmaLocalHom_basisProdIrr {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} (hσ : IsTIExtension W₁ W₂ M σ)
    (hW : IsCyclicTIPair (W₁.subgroupOf M ⊔ W₂.subgroupOf M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    {lam : ↥W₁ → ℂ} {mu : ↥W₂ → ℂ} {f : ↥(W₁ ⊔ W₂) → ℂ}
    (i : Irr ↥(W₁.subgroupOf M)) (j : Irr ↥(W₂.subgroupOf M))
    (hi : (i : ↥(W₁.subgroupOf M) → ℂ) = lam ∘ (Subgroup.subgroupOfEquivOfLe h1))
    (hj : (j : ↥(W₂.subgroupOf M) → ℂ) = mu ∘ (Subgroup.subgroupOfEquivOfLe h2))
    (hf : ∀ (x : ↥W₁) (y : ↥W₂) (z : ↥(W₁ ⊔ W₂)), (z : G) = (x : G) * (y : G) →
      f z = lam x * mu y) :
    (sigmaLocalHom h1 h2 hσ (hW.basisProdIrr (i, j)) : ↥M → ℂ) = σ f := by
  have hcomp : ((hW.basisProdIrr (i, j) : classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) :
      ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) → ℂ) ∘ (supSubgroupOfEquiv h1 h2).symm = f := by
    rw [IsCyclicTIPair.coe_basisProdIrr_apply, prodChar_comp_supSubgroupOfEquiv h1 h2 hW hi hj hf]
    funext z
    simp
  rw [coe_sigmaLocalHom, hcomp]

theorem ell_eq_inflateLeft {M W₁ W₂ : Subgroup G} {I : Type*} {α : I → ↥W₁ → ℂ}
    (h1 : W₁ ≤ M)
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hαinj : Function.Injective α)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    {ell : I → ↥M → ℂ}
    (hell : ∀ (i : I) (k : ↥(⁅M, M⁆ : Subgroup G)) (x : ↥W₁) (z : ↥M),
      (z : G) = (k : G) * (x : G) → ell i z = α i x) (i : I) :
    ell i = hP.inflateLeft (localIrrEquiv h1 α hα hαinj hαsurj i) := by
  funext z
  obtain ⟨k, hk, x, hx, hkx⟩ := hP.exists_decomp z
  have hkG : ((k : ↥M) : G) ∈ (⁅M, M⁆ : Subgroup G) := by
    have h := hk
    rw [commutator_eq_subgroupOf_commutator] at h
    exact mem_subgroupOf.1 h
  have hxG : ((x : ↥M) : G) ∈ W₁ := mem_subgroupOf.1 hx
  have hz : (z : G) = (((⟨(k : G), hkG⟩ : ↥(⁅M, M⁆ : Subgroup G)) : G)) *
      ((⟨(x : G), hxG⟩ : ↥W₁) : G) := by rw [← hkx]; rfl
  rw [hell i ⟨(k : G), hkG⟩ ⟨(x : G), hxG⟩ z hz, ← hkx,
    hP.inflateLeft_apply_mul _ hk hx, coe_localIrrEquiv]
  simp only [Function.comp_apply]
  congr 1

section RowBridge

variable {M U W₁ W₂ : Subgroup G} {I J : Type}
  {α : I → ↥W₁ → ℂ} {β : J → ↥W₂ → ℂ} {i0 : I} {j0' : J}
  {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} {w : I → J → ↥(W₁ ⊔ W₂) → ℂ}
  {δj : J → ℂ} {μ0 : J → ↥M → ℂ} {ell : I → ↥M → ℂ} {μ : I → J → ↥M → ℂ} {Mrow : J → ↥M → ℂ}

theorem delta_eq_primeTISign
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    (hα0 : α i0 = 1) (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y)
    (hδj : ∀ j, δj j = 1 ∨ δj j = -1)
    (hμ0 : ∀ j, μ0 j = δj j • σ (w i0 j)) (hμ0Irr : ∀ j, μ0 j ∈ Irr ↥M)
    (j : J) :
    δj j = hP.primeTISign (sigmaLocalHom h1 h2 hσ)
      (localIrrEquiv h2 β hβ hβinj hβsurj j) := by
  have hσ' := isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ
  have hbase : (sigmaLocalHom h1 h2 hσ (hP.isCyclicTIPair.basisProdIrr
      (principalIrr ↥(W₁.subgroupOf M), localIrrEquiv h2 β hβ hβinj hβsurj j)) : ↥M → ℂ)
      = σ (w i0 j) := by
    rw [← localIrrEquiv_eq_principalIrr h1 α hα hαinj hαsurj hα0]
    exact coe_sigmaLocalHom_basisProdIrr h1 h2 hσ hP.isCyclicTIPair _ _
      (coe_localIrrEquiv h1 α hα hαinj hαsurj i0) (coe_localIrrEquiv h2 β hβ hβinj hβsurj j)
      (fun x y z hz => hw i0 j x y z hz)
  refine (hP.existsUnique_primeTISign hσ' (localIrrEquiv h2 β hβ hβinj hβsurj j)).unique
    ⟨hδj j, ?_⟩ ⟨hP.primeTISign_eq_one_or_eq_neg_one _, ?_⟩
  · rw [hbase, ← hμ0 j]; exact hμ0Irr j
  · have := hP.primeTIirr_principal_left_mem_Irr hσ' (localIrrEquiv h2 β hβ hβinj hβsurj j)
    rwa [hP.primeTIirr_principal_left] at this

theorem mu_eq_primeTIirr
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    (hα0 : α i0 = 1) (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y)
    (hμ0 : ∀ j, μ0 j = δj j • σ (w i0 j))
    (hell : ∀ (i : I) (k : ↥(⁅M, M⁆ : Subgroup G)) (x : ↥W₁) (z : ↥M),
      (z : G) = (k : G) * (x : G) → ell i z = α i x)
    (hμ : ∀ i j, μ i j = ell i * μ0 j)
    (hsign : ∀ j, δj j = hP.primeTISign (sigmaLocalHom h1 h2 hσ)
      (localIrrEquiv h2 β hβ hβinj hβsurj j))
    (i : I) (j : J) :
    μ i j = hP.primeTIirr (sigmaLocalHom h1 h2 hσ)
      (localIrrEquiv h1 α hα hαinj hαsurj i) (localIrrEquiv h2 β hβ hβinj hβsurj j) := by
  have hbase : (sigmaLocalHom h1 h2 hσ (hP.isCyclicTIPair.basisProdIrr
      (principalIrr ↥(W₁.subgroupOf M), localIrrEquiv h2 β hβ hβinj hβsurj j)) : ↥M → ℂ)
      = σ (w i0 j) := by
    rw [← localIrrEquiv_eq_principalIrr h1 α hα hαinj hαsurj hα0]
    exact coe_sigmaLocalHom_basisProdIrr h1 h2 hσ hP.isCyclicTIPair _ _
      (coe_localIrrEquiv h1 α hα hαinj hαsurj i0) (coe_localIrrEquiv h2 β hβ hβinj hβsurj j)
      (fun x y z hz => hw i0 j x y z hz)
  rw [hμ i j, hμ0 j, hP.primeTIirr_eq_mul, hP.primeTIirr_principal_left,
    ell_eq_inflateLeft h1 hα hαinj hαsurj hP hell i, hbase, ← hsign j]

theorem Mrow_eq_primeTIrow [Fintype I] [Fintype ↑(Irr ↥(W₁.subgroupOf M))]
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hMrow : ∀ j, Mrow j = ∑ i : I, μ i j)
    (hmu : ∀ i j, μ i j = hP.primeTIirr (sigmaLocalHom h1 h2 hσ)
      (localIrrEquiv h1 α hα hαinj hαsurj i) (localIrrEquiv h2 β hβ hβinj hβsurj j))
    (j : J) :
    Mrow j = hP.primeTIrow (sigmaLocalHom h1 h2 hσ) (localIrrEquiv h2 β hβ hβinj hβsurj j) := by
  rw [hMrow j, IsPrimeCyclicTIHyp.primeTIrow_def]
  exact Fintype.sum_equiv (localIrrEquiv h1 α hα hαinj hαsurj) _ _ fun i => hmu i j

variable [Fintype ↑(Irr ↥(W₁.subgroupOf M))]

theorem Mrow_mem_detectInd_commutator
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hβ : ∀ j, β j ∈ Irr ↥W₂) (hβinj : Function.Injective β)
    (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ) (hβ0 : β j0' = 1)
    (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hmac : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hrow : ∀ j, Mrow j = hP.primeTIrow (sigmaLocalHom h1 h2 hσ)
      (localIrrEquiv h2 β hβ hβinj hβsurj j))
    {j : J} (hj : j ≠ j0') :
    Mrow j ∈ detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) := by
  rw [detectInd_commutator_eq_indFamDetect, hrow j]
  exact hmac.primeTIrow_mem_indFamDetect hP (isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ)
    (localIrrEquiv_ne_principalIrr h2 β hβ hβinj hβsurj hβ0 hj)

theorem Mrow_mem_detectInd_fittingIn
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hβ : ∀ j, β j ∈ Irr ↥W₂) (hβinj : Function.Injective β)
    (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ) (hβ0 : β j0' = 1)
    (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hmac : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hF : coreProduct (hallCore ↥M) (U.subgroupOf M) = fittingRaw ↥M)
    (hrow : ∀ j, Mrow j = hP.primeTIrow (sigmaLocalHom h1 h2 hσ)
      (localIrrEquiv h2 β hβ hβinj hβsurj j))
    {j : J} (hj : j ≠ j0') :
    Mrow j ∈ detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M) := by
  rw [detectInd_fittingIn_eq_indFamDetect, ← hF, hrow j]
  exact hmac.primeTIrow_mem_indFamDetect_coreProduct hP
    (isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ)
    (localIrrEquiv_ne_principalIrr h2 β hβ hβinj hβsurj hβ0 hj)

theorem cfInner_self_Mrow
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hβ : ∀ j, β j ∈ Irr ↥W₂) (hβinj : Function.Injective β)
    (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hrow : ∀ j, Mrow j = hP.primeTIrow (sigmaLocalHom h1 h2 hσ)
      (localIrrEquiv h2 β hβ hβinj hβsurj j))
    (j : J) :
    cfInner (Mrow j) (Mrow j) = (Nat.card ↥W₁ : ℂ) := by
  rw [hrow j, hP.cfInner_self_primeTIrow (isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ),
    natCard_subgroupOf_eq h1]

theorem cfInner_Mrow_of_ne
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hβ : ∀ j, β j ∈ Irr ↥W₂) (hβinj : Function.Injective β)
    (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hrow : ∀ j, Mrow j = hP.primeTIrow (sigmaLocalHom h1 h2 hσ)
      (localIrrEquiv h2 β hβ hβinj hβsurj j))
    {j k : J} (hjk : j ≠ k) :
    cfInner (Mrow j) (Mrow k) = 0 := by
  classical
  rw [hrow j, hrow k,
    cfInner_primeTIrow_primeTIrow hP (isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ),
    if_neg fun hc => hjk ((localIrrEquiv h2 β hβ hβinj hβsurj).injective hc)]

theorem exists_forall_delta_eq
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    (hα0 : α i0 = 1) (hβ0 : β j0' = 1)
    (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hmac : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y)
    (hδj : ∀ j, δj j = 1 ∨ δj j = -1)
    (hμ0 : ∀ j, μ0 j = δj j • σ (w i0 j)) (hμ0Irr : ∀ j, μ0 j ∈ Irr ↥M) :
    ∃ δ : ℂ, (δ = 1 ∨ δ = -1) ∧ ∀ j : J, j ≠ j0' → δj j = δ := by
  obtain ⟨δ, hδ, hall⟩ := hmac.exists_primeTISign_eq (σ := sigmaLocalHom h1 h2 hσ) hP
    (isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ)
  refine ⟨δ, hδ, fun j hj => ?_⟩
  rw [delta_eq_primeTISign h1 h2 hα hβ hαinj hβinj hαsurj hβsurj hα0 hσ hP hw hδj hμ0 hμ0Irr j]
  exact hall _ (localIrrEquiv_ne_principalIrr h2 β hβ hβinj hβsurj hβ0 hj)

end RowBridge

section Ambient

variable {G : Type u} [Group G] [Fintype G]

theorem map_subtype_commutator (M : Subgroup G) :
    (commutator ↥M).map M.subtype = (⁅M, M⁆ : Subgroup G) := by
  rw [commutator_eq_subgroupOf_commutator]
  exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self M)

theorem le_map_subtype_commutator {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    W₂ ≤ (commutator ↥M).map M.subtype := by
  rw [map_subtype_commutator]
  exact hc.le_hallCore_W₂.trans hc.hallCore_le_commutator

theorem inf_map_subtype_commutator_eq_bot {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    W₁ ⊓ (commutator ↥M).map M.subtype = ⊥ := by
  rw [map_subtype_commutator, inf_comm]
  exact disjoint_iff.1 hc.disjoint_commutator_W₁

theorem cyclicTIDiff_sup_subset_extendedSupport {M W₁ W₂ : Subgroup G} :
    cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ ⊆
      CFSG.FeitThompson.Prep09.coreFixedSet (Prep03.hallCoreIn M) (⁅M, M⁆ : Subgroup G) ∪
        CFSG.FeitThompson.Prep09.conjUnion M (cyclicTIset W₁ W₂) := by
  intro v hv
  refine Or.inr (Set.mem_iUnion₂.2 ⟨(1 : G), one_mem M, v, ?_, by simp⟩)
  rw [mem_cyclicTIset]
  rwa [mem_cyclicTIDiff] at hv

end Ambient

section RowDifference

variable {G : Type u} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  [Fintype ↑(Irr ↥W₁)]
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {A₀ : Set G} {T : G → Subgroup G}

theorem dadeMapFun_primeTIrow_sub
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : W₂ ≤ H) {A : Set ↥L}
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂)
    (hone : ∀ i : Irr ↥W₁, h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1) :
    dadeMapFun L A₀ T (h.primeTIrow σ j - h.primeTIrow σ k)
      = h.primeTISign σ j • ∑ i : Irr ↥W₁,
          ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
              (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
            - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
              (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ k)) := by
  classical
  have hsplit : h.primeTIrow σ j - h.primeTIrow σ k
      = ∑ i : Irr ↥W₁, (h.primeTIirr σ i j - h.primeTIirr σ i k) := by
    rw [IsPrimeCyclicTIHyp.primeTIrow_def, IsPrimeCyclicTIHyp.primeTIrow_def,
      ← Finset.sum_sub_distrib]
  rw [hsplit, dadeMapFun_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmem := h.primeTIirr_sub_mem_dadeDomain hσ hWH hA hA₀ i hj hk (hone i)
  rw [← coe_dadeMap hD ⟨_, hmem⟩]
  exact h.dadeMap_primeTIirr_sub_eq hσ hWH hA hA₀ hD hstab hdisj hω i hj hk (hone i)

theorem primeTIirr_one_eq_relIndex {H U : Subgroup ↥L} (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIirr σ i j 1 = ((coreCentralizer H U).relIndex U : ℂ) := by
  rw [h.primeTIirr_one i j, ← h.primeTIres_one j, hc.primeTIres_one_eq_relIndex h hσ hj]

theorem coe_nu_primeTIrow_sub_eq {H : Subgroup ↥L} [H.Normal] {S : Set (↥L → ℂ)}
    {ν0 : Submodule.span ℤ S →+ virtualChars G}
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (hWH : W₂ ≤ H) {A : Set ↥L}
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS0 : ∀ (f : charSpanZero S) (x : ↥L), (x : G) ∉ A₀ → (f : ↥L → ℂ) x = 0)
    (hScf : ∀ f ∈ Submodule.span ℤ S, f ∈ classFun ↥L)
    (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A₀),
      (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν0 f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂)
    (hone : ∀ i : Irr ↥W₁, h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1)
    (hjS : h.primeTIrow σ j ∈ S) (hkS : h.primeTIrow σ k ∈ S) :
    (ν0 ⟨h.primeTIrow σ j, Submodule.subset_span hjS⟩ : G → ℂ)
        - (ν0 ⟨h.primeTIrow σ k, Submodule.subset_span hkS⟩ : G → ℂ)
      = h.primeTISign σ j • (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
          (irrMapSubtype L W₂ j)
        - h.primeTISign σ j • (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
          (irrMapSubtype L W₂ k) := by
  classical
  have : Fintype ↑(Irr ↥(W₁.map L.subtype)) := Fintype.ofFinite _
  have hdiff : h.primeTIrow σ j - h.primeTIrow σ k ∈ Submodule.span ℤ S :=
    sub_mem (Submodule.subset_span hjS) (Submodule.subset_span hkS)
  have h1 : (h.primeTIrow σ j - h.primeTIrow σ k) 1 = 0 := by
    simp only [Pi.sub_apply, IsPrimeCyclicTIHyp.primeTIrow_def, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hone i]
    ring
  have hzero : h.primeTIrow σ j - h.primeTIrow σ k ∈ charSpanZero S :=
    mem_charSpanZero.2 ⟨hdiff, h1⟩
  have hdom : h.primeTIrow σ j - h.primeTIrow σ k ∈ dadeDomain L A₀ :=
    mem_dadeDomain.2 ⟨hScf _ hdiff, fun x hx => hS0 ⟨_, hzero⟩ x hx⟩
  rw [CoherentRowColumn.coe_nu_sub (ν := ν0) hjS hkS, hντ ⟨_, hdiff⟩ ⟨_, hdom⟩ rfl, coe_dadeMap,
    dadeMapFun_primeTIrow_sub h hσ hWH hA hA₀ hD hstab hdisj hω hj hk hone,
    IsCyclicTIPair.prodCharEtaColSum_eq_sum, IsCyclicTIPair.prodCharEtaColSum_eq_sum,
    ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Fintype.sum_equiv (Equiv.ofBijective _ (irrMapSubtype_bijective L W₁)) _ _ fun i => rfl

end RowDifference

section Orientation

variable {G : Type u} [Group G] [Fintype G]

noncomputable def ambRow {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))] (j : Irr ↥W₂) : ↥M → ℂ :=
  hP.primeTIrow (sigmaLocalHom h1 h2 hσ)
    (irrEquivOfMulEquiv (Subgroup.subgroupOfEquivOfLe h2) j)

theorem ambRow_def {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))] (j : Irr ↥W₂) :
    ambRow h1 h2 hσ hP j = hP.primeTIrow (sigmaLocalHom h1 h2 hσ)
      (irrEquivOfMulEquiv (Subgroup.subgroupOfEquivOfLe h2) j) := (rfl)

theorem exists_isCoherentWith_ambRow
    {M U W₁ W₂ : Subgroup G}
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)}
    {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G}
    {A₀ : Set G} {T : G → Subgroup G}
    {τ : charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G}
    {ν0 : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G}
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))]
    (hodd : Odd (Nat.card G)) (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hσ : IsTIExtension W₁ W₂ M σ)
    (hWpair : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    (hω : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ω)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hD : IsDadeData M A₀ T) (hVA : cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ ⊆ A₀)
    (hS0 : ∀ (f : charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M))) (x : ↥M),
      (x : G) ∉ A₀ → (f : ↥M → ℂ) x = 0)
    (hν0 : IsCoherentWith (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) τ ν0)
    (hντ : ∀ (f : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)))
        (F : dadeDomain M A₀),
      (f : ↥M → ℂ) = (F : ↥M → ℂ) → (ν0 f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hMS : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      ambRow h1 h2 hσ hP (j : Irr ↥W₂) ∈ detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M))
    (hnorm : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      cfInner (ambRow h1 h2 hσ hP (j : Irr ↥W₂)) (ambRow h1 h2 hσ hP (j : Irr ↥W₂))
        = (Nat.card ↥W₁ : ℂ))
    (horth : ∀ j k : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂}, j ≠ k →
      cfInner (ambRow h1 h2 hσ hP (j : Irr ↥W₂)) (ambRow h1 h2 hσ hP (k : Irr ↥W₂)) = 0)
    {n : ℕ} (hn : 0 < n)
    (hdeg : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      ambRow h1 h2 hσ hP (j : Irr ↥W₂) 1 = (n : ℂ))
    {δ : ℂ} (hδ : δ = 1 ∨ δ = -1)
    (htau : ∀ j k : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      (ν0 ⟨_, Submodule.subset_span (hMS j)⟩ : G → ℂ)
        - (ν0 ⟨_, Submodule.subset_span (hMS k)⟩ : G → ℂ)
      = δ • hWpair.prodCharEtaColSum ω (j : Irr ↥W₂)
        - δ • hWpair.prodCharEtaColSum ω (k : Irr ↥W₂))
    (hclass : detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) ∩ Irr ↥M = ∅ →
      detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)
        = Set.range fun j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} =>
            ambRow h1 h2 hσ hP (j : Irr ↥W₂)) :
    ∃ ν : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G,
      IsCoherentWith (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) τ ν ∧
        ∃ e : ℕ, (e = 0 ∨ e = 1) ∧
        (∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
          (ν ⟨_, Submodule.subset_span (hMS j)⟩ : G → ℂ)
            = ((-1 : ℂ) ^ e * δ) • hWpair.prodCharEtaColSum ω (starIrr^[e] (j : Irr ↥W₂))) ∧
        (e = 1 → Nat.card ↥W₂ = 3) ∧
        ((detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) ∩ Irr ↥M).Nonempty → ν = ν0) := by
  refine CoherentSimultaneousOrientation.exists_isCoherentWith_forall_eq_signed_col
    (H := (hallCore ↥M).subgroupOf (commutator ↥M)) hodd hWpair
    (le_map_subtype_commutator hc) (inf_map_subtype_commutator_eq_bot hc) hω hD hVA
    ?_ ?_ hS0 hν0 hντ hMS hnorm horth hn hdeg hδ htau hclass
  · rw [detectInd_commutator_eq_indFamDetect]
  · exact fun χ hχ => star_mem_detectInd_commutator M hχ

theorem Mrow_eq_ambRow {M W₁ W₂ : Subgroup G} {J : Type} {β : J → ↥W₂ → ℂ}
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} {Mrow : J → ↥M → ℂ}
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))]
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    (hβ : ∀ j, β j ∈ Irr ↥W₂) (hβinj : Function.Injective β)
    (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hrow : ∀ j, Mrow j = hP.primeTIrow (sigmaLocalHom h1 h2 hσ)
      (localIrrEquiv h2 β hβ hβinj hβsurj j))
    (j : J) :
    Mrow j = ambRow h1 h2 hσ hP ⟨β j, hβ j⟩ := by
  rw [hrow j, ambRow_def]
  congr 1
  refine Subtype.ext ?_
  rw [coe_localIrrEquiv, coe_irrEquivOfMulEquiv]

theorem nu_signedIrr_of_mem_detectInd_inter_Irr
    {M U W₁ W₂ : Subgroup G}
    {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G}
    {A₀ : Set G} {T : G → Subgroup G}
    {τ : charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G}
    {ν : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G}
    (hodd : Odd (Nat.card G))
    (hWpair : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    (hω : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ω)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hD : IsDadeData M A₀ T) (hVA : cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ ⊆ A₀)
    (hS0 : ∀ (f : charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M))) (x : ↥M),
      (x : G) ∉ A₀ → (f : ↥M → ℂ) x = 0)
    (hν : IsCoherentWith (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) τ ν)
    (hντ : ∀ (f : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)))
        (F : dadeDomain M A₀),
      (f : ↥M → ℂ) = (F : ↥M → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {ξ : ↥M → ℂ} (hξS : ξ ∈ detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M))
    (hξIrr : ξ ∈ Irr ↥M) :
    (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) ∈ signedIrr G
      ∧ star (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ)
        ≠ (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ)
      ∧ (ν ⟨star ξ, Submodule.subset_span (star_mem_detectInd_commutator M hξS)⟩ : G → ℂ)
        = star (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ)
      ∧ (∀ (i : Irr ↥W₁) (j : Irr ↥W₂),
        cfInner (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) (hWpair.prodCharEta ω i j) = 0)
      ∧ (∀ v ∈ cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂,
        (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) v = 0) := by
  have hS : detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)
      ⊆ indFamDetect (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) := by
    rw [detectInd_commutator_eq_indFamDetect]
  have hSstar := fun χ (hχ : χ ∈ detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) =>
    star_mem_detectInd_commutator M hχ
  have hνiso := hν.inner_eq
  refine ⟨CoherentCore.nu_mem_signedIrr hodd hD hS hSstar hνiso hS0 hντ hξS hξIrr,
    CoherentCore.star_nu_ne hodd hD hS hSstar hνiso hS0 hντ hξS hξIrr,
    CoherentCore.nu_star_eq hodd hD hS hSstar hνiso hS0 hντ hξS hξIrr,
    fun i j => isOrthogonal_iff.1 (CoherentCore.isOrthogonal_nu_prodCharEta hodd hWpair
      (le_map_subtype_commutator hc) (inf_map_subtype_commutator_eq_bot hc) hω hD hVA hS hSstar
      hνiso hS0 hντ hξS hξIrr i j),
    fun v hv => CoherentCore.nu_apply_eq_zero_of_mem_cyclicTIDiff hodd hWpair
      (le_map_subtype_commutator hc) (inf_map_subtype_commutator_eq_bot hc) hω hD hVA hS hSstar
      hνiso hS0 hντ hξS hξIrr hv⟩

theorem exists_index_eq {W₂ : Subgroup G} {J : Type} {β : J → ↥W₂ → ℂ} {j0' : J}
    (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ) (hβ0 : β j0' = 1)
    {q : Irr ↥W₂} (hq : q ≠ principalIrr ↥W₂) :
    ∃ j : J, j ≠ j0' ∧ (⟨β j, hβ j⟩ : Irr ↥W₂) = q := by
  obtain ⟨j, hj⟩ := hβsurj (q : ↥W₂ → ℂ) q.2
  refine ⟨j, ?_, Subtype.ext hj⟩
  intro hjj
  rw [hjj, hβ0] at hj
  exact hq (Subtype.ext (by rw [coe_principalIrr, ← hj]))

theorem irrEquivOfMulEquiv_principalIrr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    irrEquivOfMulEquiv e (principalIrr B) = principalIrr A :=
  Subtype.ext (by rw [coe_irrEquivOfMulEquiv, coe_principalIrr, coe_principalIrr]; rfl)

noncomputable def nonprincipalEquiv {M W₂ : Subgroup G} (h2 : W₂ ≤ M) :
    {j : Irr ↥(W₂.subgroupOf M) // j ≠ principalIrr ↥(W₂.subgroupOf M)}
      ≃ {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} :=
  Equiv.subtypeEquiv (irrEquivOfMulEquiv (Subgroup.subgroupOfEquivOfLe h2)).symm
    fun j => by
      rw [not_iff_not, ← irrEquivOfMulEquiv_principalIrr (Subgroup.subgroupOfEquivOfLe h2)]
      exact ⟨fun hc => by rw [hc, Equiv.symm_apply_apply],
        fun hc => (irrEquivOfMulEquiv (Subgroup.subgroupOfEquivOfLe h2)).symm.injective
          (by rw [hc, Equiv.symm_apply_apply])⟩

theorem coe_nonprincipalEquiv {M W₂ : Subgroup G} (h2 : W₂ ≤ M)
    (j : {j : Irr ↥(W₂.subgroupOf M) // j ≠ principalIrr ↥(W₂.subgroupOf M)}) :
    ((nonprincipalEquiv h2 j : Irr ↥W₂))
      = (irrEquivOfMulEquiv (Subgroup.subgroupOfEquivOfLe h2)).symm (j : Irr ↥(W₂.subgroupOf M)) :=
  (rfl)

theorem ambRow_nonprincipalEquiv {M W₁ W₂ : Subgroup G} (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))]
    (j : {j : Irr ↥(W₂.subgroupOf M) // j ≠ principalIrr ↥(W₂.subgroupOf M)}) :
    ambRow h1 h2 hσ hP (nonprincipalEquiv h2 j : Irr ↥W₂)
      = hP.primeTIrow (sigmaLocalHom h1 h2 hσ) (j : Irr ↥(W₂.subgroupOf M)) := by
  rw [ambRow_def, coe_nonprincipalEquiv, Equiv.apply_symm_apply]

theorem detectInd_commutator_eq_range_ambRow {M U W₁ W₂ : Subgroup G}
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))]
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hmac : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hempty : detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) ∩ Irr ↥M = ∅) :
    detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)
      = Set.range fun j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} =>
          ambRow h1 h2 hσ hP (j : Irr ↥W₂) := by
  rw [detectInd_commutator_eq_indFamDetect] at hempty ⊢
  rw [hmac.indFamDetect_eq_union hP (isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ), hempty,
    Set.empty_union, primeTIrowFam_eq_range]
  refine Set.Subset.antisymm ?_ ?_
  · rintro f ⟨j, rfl⟩
    exact ⟨nonprincipalEquiv h2 j, ambRow_nonprincipalEquiv h1 h2 hσ hP j⟩
  · rintro f ⟨j, rfl⟩
    refine ⟨(nonprincipalEquiv h2).symm j, ?_⟩
    have h := ambRow_nonprincipalEquiv h1 h2 hσ hP ((nonprincipalEquiv h2).symm j)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

theorem irrEquivOfEnum_bar {W₂ : Subgroup G} {J : Type} {β : J → ↥W₂ → ℂ}
    (hβ : ∀ j, β j ∈ Irr ↥W₂) (hβinj : Function.Injective β)
    (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    {bar : J → J} (hbar : ∀ j, β (bar j) = fun y => (starRingEnd ℂ) (β j y)) (j : J) :
    irrEquivOfEnum β hβ hβinj hβsurj (bar j)
      = starIrr (irrEquivOfEnum β hβ hβinj hβsurj j) := by
  refine Subtype.ext ?_
  rw [coe_irrEquivOfEnum_apply, coe_starIrr_eq, coe_irrEquivOfEnum_apply, hbar j]

theorem ambIrr_bar {W₂ : Subgroup G} {J : Type} {β : J → ↥W₂ → ℂ}
    (hβ : ∀ j, β j ∈ Irr ↥W₂)
    {bar : J → J} (hbar : ∀ j, β (bar j) = fun y => (starRingEnd ℂ) (β j y)) (j : J) :
    (⟨β (bar j), hβ (bar j)⟩ : Irr ↥W₂) = starIrr ⟨β j, hβ j⟩ := by
  refine Subtype.ext ?_
  change β (bar j) = _
  rw [coe_starIrr_eq, hbar j]

theorem starIrr_iterate_iterate {X : Type*} [Group X] [Finite X] {e : ℕ} (he : e = 0 ∨ e = 1)
    (χ : Irr X) : starIrr^[e] (starIrr^[e] χ) = χ := by
  rcases he with rfl | rfl
  · simp
  · simp [starIrr_starIrr]

theorem cfInner_signed_prodCharEtaColSum_prodCharEta {W₁ W₂ : Subgroup G}
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G} (hω : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ω)
    {e : ℕ} (he : e = 0 ∨ e = 1) {δ : ℂ} (i : Irr ↥W₁) (j₀ : Irr ↥W₂) :
    cfInner (((-1 : ℂ) ^ e * δ) • hW.prodCharEtaColSum ω (starIrr^[e] (starIrr^[e] j₀)))
        (hW.prodCharEta ω i j₀)
      = (-1 : ℂ) ^ e * δ := by
  have hfin := hW.finite_right
  rw [starIrr_iterate_iterate he, cfInner_smul_left,
    hW.cfInner_prodCharEtaColSum_prodCharEta hω j₀ i j₀, if_pos rfl, mul_one]

theorem prodCharEtaColSum_eq_sum_eta {W₁ W₂ : Subgroup G} {I J : Type} [Fintype I]
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)))
    {α : I → ↥W₁ → ℂ} {β : J → ↥W₂ → ℂ}
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    {w : I → J → ↥(W₁ ⊔ W₂) → ℂ}
    (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y)
    {η : I → J → G → ℂ} (hη : ∀ i j, η i j = ω (w i j)) (j : J) :
    hW.prodCharEtaColSum (tiExtensionHom hω) (irrEquivOfEnum β hβ hβinj hβsurj j)
      = fun x => ∑ i : I, η i j x := by
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  rw [IsCyclicTIPair.prodCharEtaColSum_eq_sum]
  funext x
  rw [Finset.sum_apply]
  refine (Fintype.sum_equiv (irrEquivOfEnum α hα hαinj hαsurj) _ _ fun i => ?_).symm
  rw [eta_eq_prodCharEta hW hω hα hβ hαinj hβinj hαsurj hβsurj hw hη i j]

end Orientation

end RowFamily

section Coefficients

variable {G : Type u} [Group G] [Fintype G]

omit [Fintype G] in
theorem apply_eq_zero_of_mem_span_int {L : Type*} {X : Set (L → ℂ)} {y : L}
    (hX : ∀ f ∈ X, f y = 0) {f : L → ℂ} (hf : f ∈ Submodule.span ℤ X) : f y = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf => exact hX f hf
  | zero => rfl
  | add f g _ _ hf hg => simp [hf, hg]
  | smul n f _ hf => simp [hf]

theorem mem_classFun_of_mem_span_detectInd {M Y H : Subgroup G}
    {f : ↥M → ℂ} (hf : f ∈ Submodule.span ℤ (detectInd M Y H)) : f ∈ classFun ↥M := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨θ, -, -, rfl⟩ := hf
    exact indClassFun_mem_classFun _ θ
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul n f _ hf =>
    rw [← Int.cast_smul_eq_zsmul ℂ]
    exact Submodule.smul_mem _ _ hf

theorem cfInner_ofSpanHom_eq_zero_of_mem_span
    {L : Subgroup G} {S X : Set (↥L → ℂ)} (ν : Submodule.span ℤ S →+ virtualChars G)
    (hXS : X ⊆ S) {g : G → ℂ}
    (hX : ∀ ξ (h : ξ ∈ X), cfInner (ν ⟨ξ, Submodule.subset_span (hXS h)⟩ : G → ℂ) g = 0)
    {f : ↥L → ℂ} (hf : f ∈ Submodule.span ℤ X) : cfInner (ofSpanHom ν f) g = 0 := by
  rw [ofSpanHom_apply_of_mem ν (Submodule.span_mono hXS hf)]
  induction hf using Submodule.span_induction with
  | mem f hf => exact hX f hf
  | zero =>
    have h0 : (⟨0, Submodule.span_mono hXS (Submodule.zero_mem _)⟩ : Submodule.span ℤ S) = 0 :=
      rfl
    rw [h0, map_zero]
    exact cfInner_zero_left g
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    have h : (⟨f₁ + f₂, Submodule.span_mono hXS (add_mem h₁ h₂)⟩ : Submodule.span ℤ S)
        = ⟨f₁, Submodule.span_mono hXS h₁⟩ + ⟨f₂, Submodule.span_mono hXS h₂⟩ := rfl
    rw [h, map_add, AddSubmonoid.coe_add, cfInner_add_left, ih₁, ih₂, add_zero]
  | smul n f₁ h₁ ih =>
    have h : (⟨n • f₁, Submodule.span_mono hXS (Submodule.smul_mem _ n h₁)⟩ :
        Submodule.span ℤ S) = n • ⟨f₁, Submodule.span_mono hXS h₁⟩ := rfl
    rw [h, map_zsmul]
    change cfInner (n • (ν ⟨f₁, _⟩ : G → ℂ)) g = 0
    rw [← Int.cast_smul_eq_zsmul ℂ, cfInner_smul_left, ih, mul_zero]

theorem coe_nu_eq_dadeMap_of_isCoherentWith {M : Subgroup G}
    {S : Set (↥M → ℂ)} {A₀ : Set G} {T : G → Subgroup G}
    {τ : charSpanZero S →+ virtualChars G} {ν ν0 : Submodule.span ℤ S →+ virtualChars G}
    (hν : IsCoherentWith S τ ν) (hν0 : IsCoherentWith S τ ν0) (hD : IsDadeData M A₀ T)
    (hντ0 : ∀ (f : Submodule.span ℤ S) (F : dadeDomain M A₀),
      (f : ↥M → ℂ) = (F : ↥M → ℂ) → (ν0 f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (f : Submodule.span ℤ S) (F : dadeDomain M A₀) (hfF : (f : ↥M → ℂ) = (F : ↥M → ℂ)) :
    (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have h1 : (f : ↥M → ℂ) 1 = 0 := by
    rw [hfF]
    refine (mem_dadeDomain.1 F.2).2 1 fun h => (hD.subset_sdiff h).2 ?_
    simp
  have hz : (f : ↥M → ℂ) ∈ charSpanZero S := mem_charSpanZero.2 ⟨f.2, h1⟩
  have hinc : Submodule.inclusion (charSpanZero_le S) ⟨_, hz⟩ = f := Subtype.ext rfl
  have e1 := hν.eq_on_zero ⟨_, hz⟩
  have e0 := hν0.eq_on_zero ⟨_, hz⟩
  rw [hinc] at e1 e0
  rw [e1, ← e0]
  exact hντ0 f F hfF

theorem exists_isCyclicTIIsometry_prodCharEtaColSum_eq
    {W W1 W2 W' W1' W2' : Subgroup G}
    (e : W' = W) (e1 : W1' = W1) (e2 : W2' = W2)
    (hp : IsCyclicTIPair W W1 W2) (hp' : IsCyclicTIPair W' W1' W2')
    {ω : classFun ↥W →ₗ[ℂ] classFun G} (hω : IsCyclicTIIsometry W W1 W2 ω) :
    ∃ ω' : classFun ↥W' →ₗ[ℂ] classFun G, IsCyclicTIIsometry W' W1' W2' ω' ∧
      ∀ (j' : Irr ↥W2') (j : Irr ↥W2),
        (∀ (x : ↥W2') (hx : (x : G) ∈ W2), (j' : ↥W2' → ℂ) x = (j : ↥W2 → ℂ) ⟨x, hx⟩) →
        hp'.prodCharEtaColSum ω' j' = hp.prodCharEtaColSum ω j := by
  subst e e1 e2
  refine ⟨ω, hω, fun j' j hj => ?_⟩
  have : j' = j := Subtype.ext (funext fun x => hj x x.2)
  subst this
  rfl

theorem irrEquivOfMulEquiv_ne_principalIrr {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {j : Irr B} (hj : j ≠ principalIrr B) : irrEquivOfMulEquiv e j ≠ principalIrr A := by
  rw [← irrEquivOfMulEquiv_principalIrr e]
  exact fun h => hj ((irrEquivOfMulEquiv e).injective h)

omit [Fintype G] in
theorem fittingIn_le_commutator [Finite G] {M U W₁ W₂ : Subgroup G}
    (hmac : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hF : coreProduct (hallCore ↥M) (U.subgroupOf M) = fittingRaw ↥M) :
    Prep03.fittingIn M ≤ ⁅M, M⁆ := by
  have : Fintype G := Fintype.ofFinite G
  change (fittingRaw ↥M).map M.subtype ≤ _
  rw [← hF, ← map_subtype_commutator M]
  exact Subgroup.map_mono hmac.coreProduct_le

theorem exists_dadeBaseline
    (h₁ : CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ∃ (A : Set ↥M) (A₀ : Set G) (T : G → Subgroup G) (hD : IsDadeData M A₀ T)
      (τ : charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+ virtualChars G)
      (ν0 : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) →+
        virtualChars G),
      (∀ y ∈ hallCore ↥M, y ≠ 1 →
        ((commutator ↥M ⊓ Subgroup.centralizer ({y} : Set ↥M) : Subgroup ↥M) : Set ↥M) \ {1}
          ⊆ A) ∧
      (fun x : ↥M => (x : G)) '' bridgeSupport A (W₁.subgroupOf M) (W₂.subgroupOf M) ⊆ A₀ ∧
      cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ ⊆ A₀ ∧
      (∀ (f : charSpanZero (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M))) (x : ↥M),
        (x : G) ∉ A₀ → (f : ↥M → ℂ) x = 0) ∧
      IsCoherentWith (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) τ ν0 ∧
      (∀ (f : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)))
        (F : dadeDomain M A₀),
        (f : ↥M → ℂ) = (F : ↥M → ℂ) → (ν0 f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ)) ∧
      ((Prep03.fittingIn M : Set G) \ {1} ⊆ A₀) := by
  obtain ⟨htype, -, -, -, -, -, -, hUab, -, -, -, -, -, -, -, -, hHne, -, -, -, hdir,
    hFab, -, -⟩ :=
    h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
      M U W₁ W₂ hM hc _ _ rfl rfl
  have hUabM : IsMulCommutative ↥(U.subgroupOf M) :=
    CFSG.FeitThompson.Proofs.isMulCommutative_subgroupOf hUab
  have hmac := isMinimalAbelianCore_of_isWitnessedPConfiguration h₂ hG hM hc
  have hF := coreProduct_eq_fittingRaw hc.le_M_E hdir
  have hFK := fittingIn_le_commutator hmac hF
  rcases htype with htype | htype
  · have hD := isDadeData_extendedSupport_of_isTypeII h₅ h₆ hG hM htype hc
    have hcfg := isPtypeCoreConfig_bot h₂ h₅ h₆ hG hM htype hc
    obtain ⟨τ, ν0, hν0, hντ⟩ :=
      exists_isCoherentWith_detectInd_commutator h₂ h₅ h₆ hG hM htype hc hD
    refine ⟨coreFixedSupport M, _, _, hD, τ, ν0, centralizer_subset_coreFixedSupport M,
      by rw [hcfg.A0_eq], cyclicTIDiff_sup_subset_extendedSupport,
      fun f x hx =>
        eq_zero_of_mem_charSpanZero_detectInd_commutator h₂ h₅ h₆ hG hM htype hc f.2 x hx,
      hν0, hντ, ?_⟩
    rintro x ⟨hxF, hx1⟩
    left
    rw [mem_coreFixedSet_iff]
    refine ⟨hFK hxF, hx1, ?_⟩
    obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hHne
    have hxF' : x ∈ CFSG.FeitThompson.Prep05.fittingOf M := hxF
    have := hFab
    exact ⟨y, y.2, fun h => hy1 (Subtype.ext h), setLike_mul_comm hxF' (hdir.left_le y.2)⟩
  · have hD := isDadeData_dadeA0_of_isTypeIII h₁ h₃ h₄ h₅ hG hM htype hc
    obtain ⟨τ, ν0, hν0, hντ⟩ :=
      exists_isCoherentWith_detectInd_commutator_typeIII h₁ h₂ h₃ h₄ h₅ hG hM htype hc hD
    refine ⟨((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1}, _, _, hD, τ, ν0,
      fun _ _ _ _ hx => ⟨hx.1.1, hx.2⟩,
      (image_bridgeSupport_commutator_eq_dadeA0 hc.le_M_W₁ hc.le_M_W₂).le,
      cyclicTIDiff_sup_subset_dadeA0,
      fun f x hx => eq_zero_of_mem_charSpanZero_detectInd_commutator_typeIII h₁ h₂ h₃ h₄ h₅ hG hM
        htype hc f.2 x hx,
      hν0, hντ, ?_⟩
    rintro x ⟨hxF, hx1⟩
    exact Or.inl ⟨hFK hxF, hx1⟩

theorem eq_ambRow_or_mem_span_inter_Irr {M U W₁ W₂ : Subgroup G}
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))]
    (h1 : W₁ ≤ M) (h2 : W₂ ≤ M)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥M → ℂ)} (hσ : IsTIExtension W₁ W₂ M σ)
    (hP : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hmac : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hF : coreProduct (hallCore ↥M) (U.subgroupOf M) = fittingRaw ↥M)
    {ζ : ↥M → ℂ} (hζ : ζ ∈ detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M)) :
    (∃ k : Irr ↥W₂, k ≠ principalIrr ↥W₂ ∧ ζ = ambRow h1 h2 hσ hP k) ∨
      ζ ∈ Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) ∩ Irr ↥M) := by
  classical
  have : (coreProduct (hallCore ↥M) (U.subgroupOf M)).Normal := by
    rw [hF]; exact fittingRaw_normal ↥M
  rw [detectInd_fittingIn_eq_indFamDetect, ← hF] at hζ
  rcases hmac.eq_primeTIrow_or_exists_sum_of_mem_indFamDetect_coreProduct hP
      (isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ) hζ with ⟨j, hj, rfl⟩ | ⟨n, hn, rfl⟩
  · left
    exact ⟨nonprincipalEquiv h2 ⟨j, hj⟩, (nonprincipalEquiv h2 ⟨j, hj⟩).2,
      (ambRow_nonprincipalEquiv h1 h2 hσ hP ⟨j, hj⟩).symm⟩
  · right
    refine Submodule.sum_mem _ fun χ _ => ?_
    by_cases hχ : n χ = 0
    · rw [hχ, Nat.cast_zero, zero_smul]; exact Submodule.zero_mem _
    · rw [Nat.cast_smul_eq_nsmul]
      refine Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ?_)
      rw [detectInd_commutator_eq_indFamDetect]
      exact hn χ hχ

end Coefficients

end OrientedCoreFamily

private theorem orientedCoreFamily_aux
    (_h₁ : CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (_h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (_h₃ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (_h₄ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (_h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (_h₆ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u}) :
    CFSG.FeitThompson.Statements.FCH_type_p_oriented_core_family.{u} := by
  classical
  open OrientedCoreFamily in
  intro G _ _ _ M U W₁ W₂ hcfg u hu I J _ _ i0 j0' α β hα hβ hαinj hβinj hαsurj hβsurj
    hα0 hβ0 bar hbar w hw σ ω hσ hω δj μ0 ell μ Mrow η hδj hμ0 hμ0Irr hell hμ hMrow hη
    Sfam Tfam hS hT
  refine ⟨⟨σ, ω, hσ, hω⟩, ?_⟩
  subst hS hT
  have hG := hcfg.ambient
  have hM := hcfg.isCoatom
  have hc := hcfg.config
  have h1 := hc.le_M_W₁
  have h2 := hc.le_M_W₂
  have hodd := hG.odd_natCard
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdir, -, -, hTIF⟩ :=
    _h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
      M U W₁ W₂ hM hc _ _ rfl rfl
  have hmac := isMinimalAbelianCore_of_isWitnessedPConfiguration _h₂ hG hM hc
  have hF := coreProduct_eq_fittingRaw hc.le_M_E hdir
  have hP := isPrimeCyclicTIHyp_commutator hodd hc
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  have hWpair := hc.isCyclicTIPair_sup_of_isAmbient _h₂ hG hM
  have hωL := isCyclicTIIsometry_tiExtensionHom hω
  have hσ' := isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ
  have hsign := delta_eq_primeTISign h1 h2 hα hβ hαinj hβinj hαsurj hβsurj hα0 hσ hP hw hδj
    hμ0 hμ0Irr
  have hmu := mu_eq_primeTIirr h1 h2 hα hβ hαinj hβinj hαsurj hβsurj hα0 hσ hP hw hμ0 hell hμ
    hsign
  have hrow := Mrow_eq_primeTIrow h1 h2 hα hβ hαinj hβinj hαsurj hβsurj hσ hP hMrow hmu
  obtain ⟨δ, hδ, hδall⟩ := hmac.exists_primeTISign_eq hP hσ'
  obtain ⟨A, A₀, T, hD, τ, ν0, hA, hA₀, hVA, hS0, hν0, hντ0, hFA⟩ :=
    exists_dadeBaseline _h₁ _h₂ _h₃ _h₄ _h₅ _h₆ hG hM hc
  have hMS : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      ambRow h1 h2 hσ hP (j : Irr ↥W₂) ∈ detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) := by
    intro j
    rw [ambRow_def, detectInd_commutator_eq_indFamDetect]
    exact hmac.primeTIrow_mem_indFamDetect hP hσ' (irrEquivOfMulEquiv_ne_principalIrr _ j.2)
  have hMT : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      ambRow h1 h2 hσ hP (j : Irr ↥W₂) ∈ detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M) := by
    intro j
    rw [ambRow_def, detectInd_fittingIn_eq_indFamDetect, ← hF]
    exact hmac.primeTIrow_mem_indFamDetect_coreProduct hP hσ'
      (irrEquivOfMulEquiv_ne_principalIrr _ j.2)
  have hnorm : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      cfInner (ambRow h1 h2 hσ hP (j : Irr ↥W₂)) (ambRow h1 h2 hσ hP (j : Irr ↥W₂))
        = (Nat.card ↥W₁ : ℂ) := by
    intro j
    rw [ambRow_def, hP.cfInner_self_primeTIrow hσ', natCard_subgroupOf_eq h1]
  have horth : ∀ j k : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂}, j ≠ k →
      cfInner (ambRow h1 h2 hσ hP (j : Irr ↥W₂)) (ambRow h1 h2 hσ hP (k : Irr ↥W₂)) = 0 := by
    intro j k hjk
    rw [ambRow_def, ambRow_def, cfInner_primeTIrow_primeTIrow hP hσ',
      if_neg fun h => hjk (Subtype.ext ((irrEquivOfMulEquiv _).injective h))]
  have hupos : 0 < Nat.card ↥W₁ * u := by
    refine Nat.mul_pos Nat.card_pos (Nat.pos_of_ne_zero ?_)
    rw [hu, Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hdeg : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      ambRow h1 h2 hσ hP (j : Irr ↥W₂) 1 = ((Nat.card ↥W₁ * u : ℕ) : ℂ) := fun j =>
    apply_one_of_mem_detectInd_fittingIn' hc.le_M_E h1 hP hmac hF hu (hMT j)
  obtain ⟨ωM, hωM, hcol⟩ := exists_isCyclicTIIsometry_prodCharEtaColSum_eq
    (map_subgroupOf_sup h1 h2) (Subgroup.map_subgroupOf_eq_of_le h1)
    (Subgroup.map_subgroupOf_eq_of_le h2) hWpair
    (hP.isCyclicTIPair_map_subtype (setOf_conj_eq_of_isCyclicTIPair h1 h2 hWpair)
      (inter_eq_empty_of_isCyclicTIPair h1 h2 hWpair)) hωL
  have hirr : ∀ j : Irr ↥W₂, ∀ (x : ↥((W₂.subgroupOf M).map M.subtype)) (hx : (x : G) ∈ W₂),
      ((irrMapSubtype M (W₂.subgroupOf M)
        (irrEquivOfMulEquiv (Subgroup.subgroupOfEquivOfLe h2) j) : Irr _) :
        ↥((W₂.subgroupOf M).map M.subtype) → ℂ) x = (j : ↥W₂ → ℂ) ⟨x, hx⟩ := by
    intro j x hx
    rw [coe_irrMapSubtype, Function.comp_apply, coe_irrEquivOfMulEquiv, Function.comp_apply]
    refine congrArg (j : ↥W₂ → ℂ) (Subtype.ext ?_)
    have h := coe_mapSubtypeEquiv M (W₂.subgroupOf M)
      ((mapSubtypeEquiv M (W₂.subgroupOf M)).symm x)
    rw [MulEquiv.apply_symm_apply] at h
    rw [Subgroup.subgroupOfEquivOfLe_apply_coe, ← h]
  have htau : ∀ j k : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      (ν0 ⟨_, Submodule.subset_span (hMS j)⟩ : G → ℂ)
        - (ν0 ⟨_, Submodule.subset_span (hMS k)⟩ : G → ℂ)
      = δ • hWpair.prodCharEtaColSum (tiExtensionHom hω) (j : Irr ↥W₂)
        - δ • hWpair.prodCharEtaColSum (tiExtensionHom hω) (k : Irr ↥W₂) := by
    intro j k
    have hj := irrEquivOfMulEquiv_ne_principalIrr (Subgroup.subgroupOfEquivOfLe h2) j.2
    have hk := irrEquivOfMulEquiv_ne_principalIrr (Subgroup.subgroupOfEquivOfLe h2) k.2
    have key := coe_nu_primeTIrow_sub_eq (ν0 := ν0) (ω := ωM) hP hσ'
      (le_hallCore_subgroupOf_W₂ hc) (H := hallCore ↥M) (A := A)
      (by have := @hallCore_normal ↥M _; exact hA) hA₀ hD
      (setOf_conj_eq_of_isCyclicTIPair h1 h2 hWpair)
      (inter_eq_empty_of_isCyclicTIPair h1 h2 hWpair) hωM hS0
      (fun f hf => mem_classFun_of_mem_span_detectInd hf) hντ0 hj hk
      (fun i => by rw [primeTIirr_one_eq_relIndex hP hmac hσ' i hj,
        primeTIirr_one_eq_relIndex hP hmac hσ' i hk])
      (by rw [← ambRow_def]; exact hMS j) (by rw [← ambRow_def]; exact hMS k)
    rw [hδall _ hj, hcol _ _ (hirr j), hcol _ _ (hirr k)] at key
    simpa only [ambRow_def] using key
  have hclass := fun hempty => detectInd_commutator_eq_range_ambRow h1 h2 hσ hP hmac hempty
  obtain ⟨ν, hν, e, he, hνrow, he3, -⟩ := exists_isCoherentWith_ambRow hodd h1 h2 hσ hWpair
    hωL hP hc hD hVA hS0 hν0 (fun f F hfF => hντ0 f F hfF) hMS hnorm horth hupos hdeg hδ htau
    hclass
  have hνD : ∀ (f : Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)))
      (F : dadeDomain M A₀), (f : ↥M → ℂ) = (F : ↥M → ℂ) →
      (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) :=
    fun f F hfF => coe_nu_eq_dadeMap_of_isCoherentWith hν hν0 hD hντ0 f F hfF
  have hTS := detectInd_fittingIn_subset_span_detectInd_commutator hP hmac hσ' hF
  have hSirr := fun {ξ : ↥M → ℂ}
      (hξ : ξ ∈ detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M) ∩ Irr ↥M) =>
    nu_signedIrr_of_mem_detectInd_inter_Irr hodd hWpair hωL hc hD hVA hS0 hν hνD hξ.1 hξ.2
  have hbeta : ∀ j, irrEquivOfEnum β hβ hβinj hβsurj j = ⟨β j, hβ j⟩ := fun j =>
    Subtype.ext (coe_irrEquivOfEnum_apply β hβ hβinj hβsurj j)
  have hηeq : ∀ i j, η i j = hWpair.prodCharEta (tiExtensionHom hω)
      (irrEquivOfEnum α hα hαinj hαsurj i) ⟨β j, hβ j⟩ := fun i j => by
    rw [← hbeta]; exact eta_eq_prodCharEta hWpair hω hα hβ hαinj hβinj hαsurj hβsurj hw hη i j
  have hPair : ∀ (c : ℂ) (l : Irr ↥W₂) (i : I) (j : J),
      cfInner (c • hWpair.prodCharEtaColSum (tiExtensionHom hω) l) (η i j)
        = if l = ⟨β j, hβ j⟩ then c else 0 := by
    intro c l i j
    rw [hηeq, cfInner_smul_left, hWpair.cfInner_prodCharEtaColSum_prodCharEta hωL]
    split_ifs <;> simp
  have hkIdx : ∀ j, starIrr^[e] (⟨β j, hβ j⟩ : Irr ↥W₂)
      = ⟨β (if e = 0 then j else bar j), hβ _⟩ := by
    intro j
    rcases he with rfl | rfl
    · rfl
    · exact (ambIrr_bar hβ hbar j).symm
  have hνamb : ∀ k : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      ofSpanHom ν (ambRow h1 h2 hσ hP (k : Irr ↥W₂))
        = ((-1 : ℂ) ^ e * δ) • hWpair.prodCharEtaColSum (tiExtensionHom hω)
            (starIrr^[e] (k : Irr ↥W₂)) := fun k => by
    rw [ofSpanHom_apply_of_mem ν (Submodule.subset_span (hMS k))]; exact hνrow k
  have hMamb := Mrow_eq_ambRow h1 h2 hβ hβinj hβsurj hσ hP hrow
  have hne0 : ∀ j, j ≠ j0' → (⟨β j, hβ j⟩ : Irr ↥W₂) ≠ principalIrr ↥W₂ := by
    intro j hj h
    refine hj (hβinj ?_)
    have := congrArg Subtype.val h
    rw [coe_principalIrr] at this
    rw [hβ0]; exact this
  have hprinc : (⟨β j0', hβ j0'⟩ : Irr ↥W₂) = principalIrr ↥W₂ :=
    Subtype.ext (by rw [coe_principalIrr]; exact hβ0)
  have hiter_ne : ∀ k : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      starIrr^[e] (k : Irr ↥W₂) ≠ principalIrr ↥W₂ := by
    intro k
    rcases he with rfl | rfl
    · exact k.2
    · exact starIrr_ne_principalIrr k.2
  have hcoef : ∀ ζ ∈ detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M), ∀ (i : I) (j₀ : J),
      (∀ k : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂}, ζ = ambRow h1 h2 hσ hP (k : Irr ↥W₂) →
        starIrr^[e] (k : Irr ↥W₂) ≠ ⟨β j₀, hβ j₀⟩) →
      cfInner (ofSpanHom ν ζ) (η i j₀) = 0 := by
    intro ζ hζ i j₀ hnot
    rcases eq_ambRow_or_mem_span_inter_Irr h1 h2 hσ hP hmac hF hζ with ⟨k, hk0, rfl⟩ | hspan
    · rw [show ofSpanHom ν (ambRow h1 h2 hσ hP k) = _ from hνamb ⟨k, hk0⟩, hPair]
      exact if_neg (hnot ⟨k, hk0⟩ rfl)
    · exact cfInner_ofSpanHom_eq_zero_of_mem_span ν Set.inter_subset_left
        (fun ξ hξ => by rw [hηeq]; exact (hSirr hξ).2.2.2.1 _ _) hspan
  have hcolη : ∀ l : J, hWpair.prodCharEtaColSum (tiExtensionHom hω) ⟨β l, hβ l⟩
      = fun x => ∑ i : I, η i l x := fun l => by
    rw [← hbeta]
    exact prodCharEtaColSum_eq_sum_eta hWpair hω hα hβ hαinj hβinj hαsurj hβsurj hw hη l
  refine ⟨ofSpanHom ν, δ, e, hδ, he, isAdditiveIsometryOn_ofSpanHom_of_isCoherentWith hν, hTS,
    fun f hf => apply_one_of_mem_detectInd_fittingIn' hc.le_M_E h1 hP hmac hF hu hf,
    ?_, ?_, ?_, he3, ?_, ?_, ?_⟩
  ·
    intro f hf hf1
    have hfS : f ∈ Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) :=
      Submodule.span_le.2 hTS hf
    have hdom : f ∈ dadeDomain M ((Prep03.fittingIn M : Set G) \ {1}) := by
      refine mem_dadeDomain.2 ⟨mem_classFun_of_mem_span_detectInd hf, fun x hx => ?_⟩
      by_cases hx1 : x = 1
      · rw [hx1, hf1]
      · refine apply_eq_zero_of_mem_span_int (fun g hg => ?_) hf
        refine eq_zero_of_mem_detectInd_fittingIn hg fun hxF => hx ⟨hxF, fun h => hx1 ?_⟩
        exact Subtype.ext h
    rw [ofSpanHom_apply_of_mem ν hfS, hνD ⟨f, hfS⟩ ⟨f, dadeDomain_mono hFA hdom⟩ rfl,
      dadeMap_eq_indClassFun hD hTIF hFA f hdom]
    rfl
  · intro j hj
    rw [hsign j]
    exact hδall _ (localIrrEquiv_ne_principalIrr h2 β hβ hβinj hβsurj hβ0 hj)
  · intro j hj
    rw [hMamb j, hνamb ⟨⟨β j, hβ j⟩, hne0 j hj⟩, hkIdx, hcolη]
    funext x
    simp [Pi.smul_apply, smul_eq_mul]
  · intro ξ hξ
    obtain ⟨hs, hnr, hstar, horthη, hV⟩ := hSirr hξ
    rw [ofSpanHom_apply_of_mem ν (Submodule.subset_span hξ.1)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rcases mem_signedIrr.1 hs with h | h
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr (neg_neg _).symm⟩
    · intro h
      refine hnr (funext fun x => ?_)
      rw [Pi.star_apply, Complex.star_def]
      exact (congrFun h x).symm
    · have hsξ : (fun x => (starRingEnd ℂ) (ξ x)) = star ξ := by
        funext x; rw [Pi.star_apply, Complex.star_def]
      rw [hsξ, ofSpanHom_apply_of_mem ν
        (Submodule.subset_span (star_mem_detectInd_commutator M hξ.1)), hstar]
      funext x; rw [Pi.star_apply, Complex.star_def]
    · intro i j; rw [hηeq]; exact horthη _ _
    · intro x hx; exact hV x (by rwa [cyclicTIDiff_sup_eq_cyclicTIset])
  · intro i _ ζ hζ
    exact hcoef ζ hζ i j0' fun k _ h => hiter_ne k (h.trans hprinc)
  · intro j₀ hj₀
    have hstar : starIrr^[e] (⟨β (if e = 0 then j₀ else bar j₀), hβ _⟩ : Irr ↥W₂)
        = ⟨β j₀, hβ j₀⟩ := by
      rw [← hkIdx]; exact starIrr_iterate_iterate he _
    have hne' : (if e = 0 then j₀ else bar j₀) ≠ j0' := by
      intro h
      apply hne0 j₀ hj₀
      have hp : (⟨β (if e = 0 then j₀ else bar j₀), hβ _⟩ : Irr ↥W₂) = principalIrr ↥W₂ :=
        Subtype.ext (by rw [coe_principalIrr]; change β _ = 1; rw [h, hβ0])
      rw [← hstar, hp]
      rcases he with rfl | rfl
      · rfl
      · exact starIrr_principalIrr
    refine ⟨?_, cfInner_self_Mrow h1 h2 hβ hβinj hβsurj hσ hP hrow _, ?_, ?_⟩
    · rw [hMamb]; exact hMT ⟨_, hne0 _ hne'⟩
    · rw [hMamb, hνamb ⟨_, hne0 _ hne'⟩, hPair]
      exact if_pos hstar
    · intro ζ hζ hne
      refine hcoef ζ hζ i0 j₀ fun k hk h => hne ?_
      have hk' : (k : Irr ↥W₂) = ⟨β (if e = 0 then j₀ else bar j₀), hβ _⟩ := by
        rw [← starIrr_iterate_iterate he (k : Irr ↥W₂), h, hkIdx]
      rw [hk, hk', hMamb]

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FCH_type_p_oriented_core_family
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FCH_type_p_oriented_core_family.{u} := by
  intro G _ _ hG M U W₁ W₂ hcfg u hu I J fI fJ i0 j0' α β hα hβ hαinj hβinj hαsurj hβsurj
    hα0 hβ0 bar hbar w hw σ ω hσ hω δj μ0 ell μ Mrow η hδj hμ0 hμ0Irr hell hμ hMrow hη
    Sfam Tfam hS hT
  refine ⟨⟨σ, ω, hσ, hω⟩, ?_⟩
  exact (orientedCoreFamily_aux h₁ h₂ h₃ h₄ h₅ h₆ G hG M U W₁ W₂ hcfg u hu I J fI fJ i0 j0'
    α β hα hβ hαinj hβinj hαsurj hβsurj hα0 hβ0 bar hbar w hw σ ω hσ hω δj μ0 ell μ Mrow η
    hδj hμ0 hμ0Irr hell hμ hMrow hη Sfam Tfam hS hT).2

end CFSG.FeitThompson.Proofs

end
