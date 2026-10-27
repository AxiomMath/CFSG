module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Representations.TypeIFrobeniusCoherentFamily
public import CFSG.FeitThompson.Local.DisjointDSetsNonconjugateMaximals
public import CFSG.FeitThompson.Local.NonconjugateMaximaHallCoresCoprime
public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
public import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
public import CFSG.FeitThompson.Representations.CrossedDadeScalarProductNonzero
public import CFSG.FeitThompson.Representations.CrossedCoefficientOppositeKernelIndex
import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Local.PrimeCentralizerTransitiveHyperplanes
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis

namespace CFSG.FeitThompson.Proofs

namespace CrossedTypeI

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem conjSubgroup_eq_prep08 (Y : Subgroup G) (g : G) :
    CFSG.FeitThompson.conjSubgroup Y g = CFSG.FeitThompson.Prep08.conjSubgroup Y g := (rfl)

theorem dadeDomain_eq_sigmaPacketSupport [Finite G] {L : Subgroup G}
    (hSL : sigmaCore L = CFSG.FeitThompson.hallCoreIn L) :
    CFSG.FeitThompson.dadeSupportDomain L = CFSG.FeitThompson.Prep08.sigmaPacketSupport G L := by
  rw [CFSG.FeitThompson.dadeSupportDomain_eq, CFSG.FeitThompson.Prep08.sigmaPacketSupport_eq_totalDadeSupport, hSL]
  rfl

theorem hallCoreIn_eq_map (L : Subgroup G) :
    CFSG.FeitThompson.hallCoreIn L = (hallCore ↥L).map L.subtype := (rfl)

theorem image_coe_hallCore_sdiff_one (L : Subgroup G) :
    (fun x : ↥L => (x : G)) '' (((hallCore ↥L : Subgroup ↥L) : Set ↥L) \ {1})
      = (CFSG.FeitThompson.hallCoreIn L : Set G) \ {1} := by
  ext z
  simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    hallCoreIn_eq_map, Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨hx, hx1⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun h => hx1 (Subtype.ext h)⟩
  · rintro ⟨⟨x, hx, rfl⟩, hz1⟩
    exact ⟨x, ⟨hx, fun h => hz1 (congrArg (fun y : ↥L => (y : G)) h)⟩, rfl⟩

theorem extendSub_eq_extendByZero (K : Subgroup G) (θ : ↥K → ℂ) :
    CFSG.FeitThompson.extendSub K θ = extendByZero K θ := by
  funext z
  by_cases hz : z ∈ K
  · rw [show z = ((⟨z, hz⟩ : ↥K) : G) from rfl, CFSG.FeitThompson.extendSub_apply_coe,
      extendByZero_apply_coe]
  · rw [CFSG.FeitThompson.extendSub_apply_of_notMem K θ hz, extendByZero_of_notMem K θ hz]

theorem tauDade_eq_dadeMap [Finite G] {L : Subgroup G} {f : ↥L → ℂ}
    (hD : IsDadeData L ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1})
      CFSG.FeitThompson.sigCoreSignalizer)
    (hf : f ∈ dadeDomain L ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1})) :
    CFSG.FeitThompson.tauDade L f = ((dadeMap hD ⟨f, hf⟩ : classFun G) : G → ℂ) := by
  rw [dadeMap_apply_coe, CFSG.FeitThompson.tauDade, extendSub_eq_extendByZero]

theorem comp_equiv_eq_one_iff {A B : Type*} (e : A ≃ B) (θ : B → ℂ) :
    (fun y => θ (e y)) = (1 : A → ℂ) ↔ θ = (1 : B → ℂ) := by
  constructor
  · intro h
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    exact congrFun h y
  · rintro rfl
    rfl

noncomputable def hallCoreEquiv (L : Subgroup G) :
    ↥(hallCore ↥L) ≃* ↥(CFSG.FeitThompson.hallCoreIn L) :=
  (hallCore ↥L).equivMapOfInjective L.subtype L.subtype_injective

theorem coe_hallCoreEquiv (L : Subgroup G) (y : ↥(hallCore ↥L)) :
    (((hallCoreEquiv L) y : ↥(CFSG.FeitThompson.hallCoreIn L)) : G) = ((y : ↥L) : G) := (rfl)

theorem indBetween_hallCoreIn_eq_indClassFun [Finite G] (L : Subgroup G) [Fintype ↥L]
    (θ : ↥(CFSG.FeitThompson.hallCoreIn L) → ℂ) :
    CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L) L θ
      = indClassFun (hallCore ↥L) (fun y => θ (hallCoreEquiv L y)) := by
  classical
  funext y
  rw [CFSG.FeitThompson.indBetween_apply, indClassFun_apply]
  have hcard : Nat.card ↥(hallCore ↥L) = Nat.card ↥(CFSG.FeitThompson.hallCoreIn L) :=
    Nat.card_congr (hallCoreEquiv L).toEquiv
  rw [hcard]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hmem : ((t : ↥L)⁻¹ * y * t) ∈ hallCore ↥L
  · rw [dif_pos hmem]
    have hmemG : ((t : G)⁻¹ * (y : G) * (t : G)) ∈ CFSG.FeitThompson.hallCoreIn L :=
      ⟨(t : ↥L)⁻¹ * y * t, hmem, rfl⟩
    rw [show ((t : G)⁻¹ * (y : G) * (t : G))
        = (((⟨_, hmemG⟩ : ↥(CFSG.FeitThompson.hallCoreIn L))) : G) from rfl,
      CFSG.FeitThompson.extendSub_apply_coe]
    rfl
  · rw [dif_neg hmem]
    refine CFSG.FeitThompson.extendSub_apply_of_notMem _ θ ?_
    rintro ⟨x, hx, hxe⟩
    exact hmem (by rwa [show x = (t : ↥L)⁻¹ * y * t from Subtype.ext hxe] at hx)

theorem calLFam_eq_indFam [Finite G] (L : Subgroup G) [Fintype ↥L] :
    CFSG.FeitThompson.calLFam L = indFam (hallCore ↥L) (Irr ↥(hallCore ↥L) \ {1}) := by
  ext f
  rw [CFSG.FeitThompson.mem_calLFam]
  simp only [mem_indFam, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨θ, ⟨hθ, hθ1⟩, rfl⟩
    refine ⟨fun y => θ (hallCoreEquiv L y),
      ⟨FrobeniusInduction.mem_Irr_comp_mulEquiv hθ (hallCoreEquiv L), ?_⟩,
      (indBetween_hallCoreIn_eq_indClassFun L θ).symm⟩
    intro h
    exact hθ1 ((comp_equiv_eq_one_iff (hallCoreEquiv L).toEquiv θ).1 h)
  · rintro ⟨θ, ⟨hθ, hθ1⟩, rfl⟩
    refine ⟨fun x => θ ((hallCoreEquiv L).symm x),
      ⟨FrobeniusInduction.mem_Irr_comp_mulEquiv hθ (hallCoreEquiv L).symm, ?_⟩, ?_⟩
    · intro h
      exact hθ1 ((comp_equiv_eq_one_iff (hallCoreEquiv L).toEquiv.symm θ).1 h)
    · refine (indBetween_hallCoreIn_eq_indClassFun L
        (fun x => θ ((hallCoreEquiv L).symm x))).trans ?_
      simp

@[expose]
def calLEnum [Finite G] (L : Subgroup G) : ↥(CFSG.FeitThompson.calLFam L) → (↥L → ℂ) := Subtype.val

@[simp]
theorem calLEnum_mk [Finite G] {L : Subgroup G} {φ : ↥L → ℂ}
    (hφ : φ ∈ CFSG.FeitThompson.calLFam L) : calLEnum L ⟨φ, hφ⟩ = φ := rfl

@[simp]
theorem range_calLEnum [Finite G] (L : Subgroup G) :
    Set.range (calLEnum L) = CFSG.FeitThompson.calLFam L := Subtype.range_coe

theorem injective_calLEnum [Finite G] (L : Subgroup G) :
    Function.Injective (calLEnum L) := Subtype.val_injective

theorem finite_calLFam [Finite G] {L : Subgroup G} (hIrr : CFSG.FeitThompson.calLFam L ⊆ Irr ↥L) :
    Finite ↥(CFSG.FeitThompson.calLFam L) :=
  (Set.Finite.subset finite_Irr hIrr).to_subtype

theorem hallIndFamily_eq_calLFam [Fintype G] (L : Subgroup G) [inst : Fintype ↥L] :
    CFSG.FeitThompson.Prep03.hallIndFamily L = CFSG.FeitThompson.calLFam L := by
  rw [calLFam_eq_indFam]
  ext f
  rw [mem_indFam (hallCore ↥L)]
  have hind : ∀ θ : ↥(hallCore ↥L) → ℂ,
      @indClassFun ↥L _ (hallCore ↥L) (CFSG.FeitThompson.subgroupFintype L) θ
        = @indClassFun ↥L _ (hallCore ↥L) inst θ :=
    fun θ => by congr 1; exact Subsingleton.elim _ _
  constructor
  · rintro ⟨θ, hθ, hne, hf⟩; exact ⟨θ, ⟨hθ, hne⟩, (hind θ).symm.trans hf⟩
  · rintro ⟨θ, ⟨hθ, hne⟩, hf⟩; exact ⟨θ, hθ, hne, (hind θ).trans hf⟩

theorem range_calLEnum_eq_indFam [Finite G] (L : Subgroup G) [Fintype ↥L] :
    Set.range (calLEnum L) = indFam (hallCore ↥L) (Irr ↥(hallCore ↥L) \ {1}) := by
  rw [range_calLEnum, calLFam_eq_indFam]

theorem span_range_calLEnum [Finite G] (L : Subgroup G) :
    Submodule.span ℤ (Set.range (calLEnum L)) = Submodule.span ℤ (CFSG.FeitThompson.calLFam L) := by
  rw [range_calLEnum]

theorem mem_span_calLFam_of_mem_span_range [Finite G] {L : Subgroup G}
    (f : ↥(Submodule.span ℤ (Set.range (calLEnum L)))) :
    (f : ↥L → ℂ) ∈ Submodule.span ℤ (CFSG.FeitThompson.calLFam L) := by
  rw [← span_range_calLEnum]; exact f.2

noncomputable def coherentDadeHom [Finite G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν) :
    Submodule.span ℤ (Set.range (calLEnum L)) →+ virtualChars G :=
  AddMonoidHom.mk' (fun f => ⟨ν (f : ↥L → ℂ), hν.2.1 _ (mem_span_calLFam_of_mem_span_range f)⟩)
    (fun f g => Subtype.ext (hν.1 _ (mem_span_calLFam_of_mem_span_range f) _
      (mem_span_calLFam_of_mem_span_range g)))

theorem coe_coherentDadeHom [Finite G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν)
    (f : ↥(Submodule.span ℤ (Set.range (calLEnum L)))) :
    ((coherentDadeHom hν f : ↥(virtualChars G)) : G → ℂ) = ν (f : ↥L → ℂ) := (rfl)

theorem coherentVal_coherentDadeHom [Finite G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν)
    (χ : ↥(Set.range (calLEnum L))) :
    coherentVal (coherentDadeHom hν) χ = ν (χ : ↥L → ℂ) := by
  rw [coherentVal_apply]; exact coe_coherentDadeHom hν _

theorem coherentImage_coherentDadeHom [Finite G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν)
    (k : ↥(CFSG.FeitThompson.calLFam L)) :
    CrossFamilyProjection.coherentImage (calLEnum L) (coherentDadeHom hν) k = ν (k : ↥L → ℂ) := by
  rw [CrossFamilyProjection.coherentImage_apply]; exact coe_coherentDadeHom hν _

theorem cfInner_coherentDadeHom [Finite G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν)
    (f h : ↥(Submodule.span ℤ (Set.range (calLEnum L)))) :
    cfInner ((coherentDadeHom hν f : ↥(virtualChars G)) : G → ℂ)
        ((coherentDadeHom hν h : ↥(virtualChars G)) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ) := by
  have h2 := hν.2.2.1 _ (mem_span_calLFam_of_mem_span_range f) _
    (mem_span_calLFam_of_mem_span_range h)
  rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner, CFSG.FeitThompson.cfInnerFin_eq_cfInner] at h2
  rw [coe_coherentDadeHom, coe_coherentDadeHom]
  exact h2

noncomputable def baselineDadeHom [Finite G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν) :
    charSpanZero (Set.range (calLEnum L)) →+ virtualChars G :=
  (coherentDadeHom hν).comp
    (Submodule.inclusion (charSpanZero_le (Set.range (calLEnum L)))).toAddMonoidHom

theorem isCoherentWith_coherentDadeHom [Finite G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν) :
    IsCoherentWith (Set.range (calLEnum L)) (baselineDadeHom hν) (coherentDadeHom hν) :=
  ⟨cfInner_coherentDadeHom hν, fun _ => rfl⟩

theorem coe_coherentDadeHom_eq_dadeMap [Finite G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν)
    (hD : IsDadeData L ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1}) CFSG.FeitThompson.sigCoreSignalizer)
    (f : ↥(Submodule.span ℤ (Set.range (calLEnum L))))
    (F : ↥(dadeDomain L ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1})))
    (hf : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    ((coherentDadeHom hν f : ↥(virtualChars G)) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have h1 : (f : ↥L → ℂ) 1 = 0 := by
    rw [hf]; exact (mem_dadeDomain.1 F.2).2 1 (by simp)
  rw [coe_coherentDadeHom, hν.2.2.2 _ (mem_span_calLFam_of_mem_span_range f) h1,
    tauDade_eq_dadeMap hD (hf ▸ F.2 : (f : ↥L → ℂ) ∈ _)]
  congr 2
  exact Subtype.ext hf

theorem coe_baselineDadeHom_eq_dadeMap [Finite G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν)
    (hD : IsDadeData L ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1}) CFSG.FeitThompson.sigCoreSignalizer)
    (f : ↥(charSpanZero (Set.range (calLEnum L))))
    (F : ↥(dadeDomain L ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1})))
    (hf : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    ((baselineDadeHom hν f : ↥(virtualChars G)) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) :=
  coe_coherentDadeHom_eq_dadeMap hν hD _ F hf

theorem isFullCoherentFamily_calLEnum [Finite G] [Fintype G] (hodd : Odd (Nat.card G))
    {L : Subgroup G} [Fintype ↥L]
    (hD : IsDadeData L ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1}) CFSG.FeitThompson.sigCoreSignalizer)
    (hIrr : CFSG.FeitThompson.calLFam L ⊆ Irr ↥L)
    {ν : (↥L → ℂ) → (G → ℂ)} (hν : CFSG.FeitThompson.IsCoherentDade L ν) :
    DisjointCoherentFamilies.IsFullCoherentFamily (calLEnum L) (baselineDadeHom hν)
      (coherentDadeHom hν) (CFSG.FeitThompson.dadeSupportDomain L) := by
  rw [CFSG.FeitThompson.dadeSupportDomain_eq L]
  exact DisjointCoherentFamilies.isFullCoherentFamily_of_isDadeData (H := hallCore ↥L)
    hodd hD (image_coe_hallCore_sdiff_one L).symm (range_calLEnum_eq_indFam L)
    (by rw [range_calLEnum]; exact hIrr)
    (fun f hf => coe_baselineDadeHom_eq_dadeMap hν hD _ ⟨_, hf⟩ rfl)
    (isCoherentWith_coherentDadeHom hν)

theorem natCard_hallCore_eq (L : Subgroup G) :
    Nat.card ↥(hallCore ↥L) = Nat.card ↥(CFSG.FeitThompson.hallCoreIn L) :=
  Nat.card_congr (hallCoreEquiv L).toEquiv

theorem index_hallCore_eq_relIndex (L : Subgroup G) :
    (hallCore ↥L).index = (CFSG.FeitThompson.hallCoreIn L).relIndex L := by
  rw [hallCoreIn_eq_map, relIndex_map_subtype]

theorem two_mul_index_add_one_le [Finite G] {L : Subgroup G}
    (hbd : 2 * (CFSG.FeitThompson.hallCoreIn L).relIndex L
      ≤ Nat.card ↥(CFSG.FeitThompson.hallCoreIn L) - 1) :
    2 * (hallCore ↥L).index + 1 ≤ Nat.card ↥(hallCore ↥L) := by
  rw [index_hallCore_eq_relIndex, natCard_hallCore_eq]
  have : 0 < Nat.card ↥(CFSG.FeitThompson.hallCoreIn L) := Nat.card_pos
  omega

theorem indBetween_one_eq_indClassFun_one [Finite G] (L : Subgroup G) [Fintype ↥L] :
    CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L) L 1
      = indClassFun (hallCore ↥L) (1 : ↥(hallCore ↥L) → ℂ) := by
  rw [indBetween_hallCoreIn_eq_indClassFun L 1]; rfl

theorem tauDade_indBetween_sub_eq_dadeBeta [Finite G] {L : Subgroup G} [Fintype ↥L] {φ : ↥L → ℂ}
    (hD : IsDadeData L ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1}) CFSG.FeitThompson.sigCoreSignalizer)
    (hφS : φ ∈ indFam (hallCore ↥L) (Irr ↥(hallCore ↥L) \ {1}))
    (hφ1 : φ 1 = ((hallCore ↥L).index : ℂ)) :
    CFSG.FeitThompson.tauDade L (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L) L 1 - φ)
      = NormalInducedFamily.dadeBeta ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1})
        CFSG.FeitThompson.sigCoreSignalizer (hallCore ↥L) φ := by
  have hdom : indClassFun (hallCore ↥L) (1 : ↥(hallCore ↥L) → ℂ) - φ
      ∈ dadeDomain L ((CFSG.FeitThompson.hallCoreIn L : Set G) \ {1}) :=
    NormalInducedFamily.indClassFun_one_sub_mem_dadeDomain
      (image_coe_hallCore_sdiff_one L).symm hφS hφ1
  rw [NormalInducedFamily.dadeBeta_eq_dadeMap hD hdom,
    ← tauDade_eq_dadeMap hD hdom, indBetween_one_eq_indClassFun_one]

theorem div_index_le_index_sub_one_pair [Fintype G] (hodd : Odd (Nat.card G))
    {L₁ L₂ : Subgroup G} [i₁ : Fintype ↥L₁] [i₂ : Fintype ↥L₂]
    {H₁ : Subgroup ↥L₁} {H₂ : Subgroup ↥L₂} [n₁ : H₁.Normal] [n₂ : H₂.Normal]
    {A₁ A₂ : Set G} {R : G → Subgroup G}
    {κ₁ κ₂ : Type v} [f₁ : Finite κ₁] [f₂ : Finite κ₂]
    {ξ₁ : κ₁ → (↥L₁ → ℂ)} {ξ₂ : κ₂ → (↥L₂ → ℂ)} {k₁ : κ₁} {k₂ : κ₂}
    {τ₁ : charSpanZero (Set.range ξ₁) →+ virtualChars G}
    {τ₂ : charSpanZero (Set.range ξ₂) →+ virtualChars G}
    {ν₁ : Submodule.span ℤ (Set.range ξ₁) →+ virtualChars G}
    {ν₂ : Submodule.span ℤ (Set.range ξ₂) →+ virtualChars G}
    (hD₁ : IsDadeData L₁ A₁ R) (hD₂ : IsDadeData L₂ A₂ R)
    (hA₁ : A₁ = (fun x : ↥L₁ => (x : G)) '' ((H₁ : Set ↥L₁) \ {1}))
    (hA₂ : A₂ = (fun x : ↥L₂ => (x : G)) '' ((H₂ : Set ↥L₂) \ {1}))
    (hS₁ : Set.range ξ₁ = indFam H₁ (Irr ↥H₁ \ {1}))
    (hS₂ : Set.range ξ₂ = indFam H₂ (Irr ↥H₂ \ {1}))
    (hinj₁ : Function.Injective ξ₁) (hinj₂ : Function.Injective ξ₂)
    (hIrr₁ : Set.range ξ₁ ⊆ Irr ↥L₁) (hIrr₂ : Set.range ξ₂ ⊆ Irr ↥L₂)
    (hτ₁ : ∀ (f : charSpanZero (Set.range ξ₁)) (F : dadeDomain L₁ A₁),
      (f : ↥L₁ → ℂ) = (F : ↥L₁ → ℂ) → (τ₁ f : G → ℂ) = ((dadeMap hD₁ F : classFun G) : G → ℂ))
    (hτ₂ : ∀ (f : charSpanZero (Set.range ξ₂)) (F : dadeDomain L₂ A₂),
      (f : ↥L₂ → ℂ) = (F : ↥L₂ → ℂ) → (τ₂ f : G → ℂ) = ((dadeMap hD₂ F : classFun G) : G → ℂ))
    (hν₁ : IsCoherentWith (Set.range ξ₁) τ₁ ν₁) (hν₂ : IsCoherentWith (Set.range ξ₂) τ₂ ν₂)
    (hζ₁1 : ξ₁ k₁ 1 = (H₁.index : ℂ)) (hζ₂1 : ξ₂ k₂ 1 = (H₂.index : ℂ))
    (hdisj : Disjoint (totalDadeSupport A₁ R) (totalDadeSupport A₂ R))
    (hbd₁ : 2 * H₁.index + 1 ≤ Nat.card ↥H₁) (hbd₂ : 2 * H₂.index + 1 ≤ Nat.card ↥H₂)
    (hc : cfInner (NormalInducedFamily.dadeBeta A₁ R H₁ (ξ₁ k₁))
      (CrossFamilyProjection.coherentImage ξ₂ ν₂ k₂) ≠ 0) :
    ((Nat.card ↥H₂ : ℝ) - 1) / (H₂.index : ℝ) ≤ (H₁.index : ℝ) - 1 := by
  classical
  exact @CrossedKernelIndexBound.div_index_le_index_sub_one_of_cfInner_ne_zero G _ _ Bool
    (fun b => Bool.rec (motive := fun _ => Subgroup G) L₁ L₂ b)
    (fun b => Bool.rec (motive := fun b =>
      Fintype ↥(Bool.rec (motive := fun _ => Subgroup G) L₁ L₂ b)) i₁ i₂ b)
    (fun b => Bool.rec (motive := fun _ => Set G) A₁ A₂ b)
    (fun _ => R)
    (fun b => Bool.rec (motive := fun b =>
      Subgroup ↥(Bool.rec (motive := fun _ => Subgroup G) L₁ L₂ b)) H₁ H₂ b)
    (fun b => Bool.rec (motive := fun b => (Bool.rec (motive := fun b =>
      Subgroup ↥(Bool.rec (motive := fun _ => Subgroup G) L₁ L₂ b)) H₁ H₂ b).Normal) n₁ n₂ b)
    (fun b => Bool.rec (motive := fun _ => Type v) κ₁ κ₂ b)
    (fun b => Bool.rec (motive := fun b =>
      Finite (Bool.rec (motive := fun _ => Type v) κ₁ κ₂ b)) f₁ f₂ b)
    (fun b => Bool.rec (motive := fun b => (Bool.rec (motive := fun _ => Type v) κ₁ κ₂ b) →
      (↥(Bool.rec (motive := fun _ => Subgroup G) L₁ L₂ b) → ℂ)) ξ₁ ξ₂ b)
    (fun b => Bool.rec (motive := fun b => Bool.rec (motive := fun _ => Type v) κ₁ κ₂ b) k₁ k₂ b)
    (fun b => Bool.rec (motive := fun b => charSpanZero (Set.range
      (Bool.rec (motive := fun b => (Bool.rec (motive := fun _ => Type v) κ₁ κ₂ b) →
        (↥(Bool.rec (motive := fun _ => Subgroup G) L₁ L₂ b) → ℂ)) ξ₁ ξ₂ b)) →+
      virtualChars G) τ₁ τ₂ b)
    (fun b => Bool.rec (motive := fun b => Submodule.span ℤ (Set.range
      (Bool.rec (motive := fun b => (Bool.rec (motive := fun _ => Type v) κ₁ κ₂ b) →
        (↥(Bool.rec (motive := fun _ => Subgroup G) L₁ L₂ b) → ℂ)) ξ₁ ξ₂ b)) →+
      virtualChars G) ν₁ ν₂ b)
    hodd
    (fun b => by cases b
                 · exact hD₁
                 · exact hD₂)
    (fun b => by cases b
                 · exact hA₁
                 · exact hA₂)
    (fun b => by cases b
                 · exact hS₁
                 · exact hS₂)
    (fun b => by cases b
                 · exact hinj₁
                 · exact hinj₂)
    (fun b => by cases b
                 · exact hIrr₁
                 · exact hIrr₂)
    (fun b => by cases b
                 · exact hτ₁
                 · exact hτ₂)
    (fun b => by cases b
                 · exact hν₁
                 · exact hν₂)
    (fun b => by cases b
                 · exact hζ₁1
                 · exact hζ₂1)
    (by
      intro a b hab
      cases a <;> cases b
      · exact absurd rfl hab
      · exact hdisj
      · exact hdisj.symm
      · exact absurd rfl hab)
    (fun b => by cases b
                 · exact hbd₁
                 · exact hbd₂) false true Bool.false_ne_true hc

theorem crossed_clauses_of_isDadeData [Finite G] (hodd : Odd (Nat.card G))
    {L₁ L₂ : Subgroup G}
    (hD₁ : IsDadeData L₁ ((CFSG.FeitThompson.hallCoreIn L₁ : Set G) \ {1})
      CFSG.FeitThompson.sigCoreSignalizer)
    (hD₂ : IsDadeData L₂ ((CFSG.FeitThompson.hallCoreIn L₂ : Set G) \ {1})
      CFSG.FeitThompson.sigCoreSignalizer)
    (hIrr₁ : CFSG.FeitThompson.calLFam L₁ ⊆ Irr ↥L₁) (hIrr₂ : CFSG.FeitThompson.calLFam L₂ ⊆ Irr ↥L₂)
    (hdisj : CFSG.FeitThompson.dadeSupportDomain L₁ ∩ CFSG.FeitThompson.dadeSupportDomain L₂ = ∅)
    (hbd₁ : 2 * (CFSG.FeitThompson.hallCoreIn L₁).relIndex L₁
      ≤ Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₁) - 1)
    (hbd₂ : 2 * (CFSG.FeitThompson.hallCoreIn L₂).relIndex L₂
      ≤ Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₂) - 1)
    {ν₁ : (↥L₁ → ℂ) → (G → ℂ)} (hν₁ : CFSG.FeitThompson.IsCoherentDade L₁ ν₁)
    {ν₂ : (↥L₂ → ℂ) → (G → ℂ)} (hν₂ : CFSG.FeitThompson.IsCoherentDade L₂ ν₂)
    {φ₁ : ↥L₁ → ℂ} (hφ₁ : φ₁ ∈ CFSG.FeitThompson.calLFam L₁)
    (hφ₁deg : φ₁ 1 = ((CFSG.FeitThompson.hallCoreIn L₁).relIndex L₁ : ℂ))
    {φ₂ : ↥L₂ → ℂ} (hφ₂ : φ₂ ∈ CFSG.FeitThompson.calLFam L₂)
    (hφ₂deg : φ₂ 1 = ((CFSG.FeitThompson.hallCoreIn L₂).relIndex L₂ : ℂ)) :
    (∀ ξ ∈ CFSG.FeitThompson.calLFam L₁, ∀ ζ ∈ CFSG.FeitThompson.calLFam L₂,
        CFSG.FeitThompson.cfInnerFin (ν₁ ξ) (ν₂ ζ) = 0) ∧
      (CFSG.FeitThompson.cfInnerFin (CFSG.FeitThompson.tauDade L₁
          (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L₁) L₁ 1 - φ₁)) (ν₂ φ₂) ≠ 0 ∨
        CFSG.FeitThompson.cfInnerFin (CFSG.FeitThompson.tauDade L₂
          (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L₂) L₂ 1 - φ₂)) (ν₁ φ₁) ≠ 0) ∧
      (CFSG.FeitThompson.cfInnerFin (CFSG.FeitThompson.tauDade L₁
          (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L₁) L₁ 1 - φ₁)) (ν₂ φ₂) ≠ 0 →
        ((Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₂) : ℚ) - 1)
            / ((CFSG.FeitThompson.hallCoreIn L₂).relIndex L₂ : ℚ)
          ≤ ((CFSG.FeitThompson.hallCoreIn L₁).relIndex L₁ : ℚ) - 1) ∧
      (CFSG.FeitThompson.cfInnerFin (CFSG.FeitThompson.tauDade L₂
          (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L₂) L₂ 1 - φ₂)) (ν₁ φ₁) ≠ 0 →
        ((Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₁) : ℚ) - 1)
            / ((CFSG.FeitThompson.hallCoreIn L₁).relIndex L₁ : ℚ)
          ≤ ((CFSG.FeitThompson.hallCoreIn L₂).relIndex L₂ : ℚ) - 1) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have _ : Fintype ↥L₁ := Fintype.ofFinite _
  have _ : Fintype ↥L₂ := Fintype.ofFinite _
  have _ : Finite ↥(CFSG.FeitThompson.calLFam L₁) := finite_calLFam hIrr₁
  have _ : Finite ↥(CFSG.FeitThompson.calLFam L₂) := finite_calLFam hIrr₂
  have hS₁ : Set.range (calLEnum L₁) = indFam (hallCore ↥L₁) (Irr ↥(hallCore ↥L₁) \ {1}) :=
    range_calLEnum_eq_indFam L₁
  have hS₂ : Set.range (calLEnum L₂) = indFam (hallCore ↥L₂) (Irr ↥(hallCore ↥L₂) \ {1}) :=
    range_calLEnum_eq_indFam L₂
  have hφ₁S : φ₁ ∈ Set.range (calLEnum L₁) := by rw [range_calLEnum]; exact hφ₁
  have hφ₂S : φ₂ ∈ Set.range (calLEnum L₂) := by rw [range_calLEnum]; exact hφ₂
  have hφ₁1 : φ₁ 1 = ((hallCore ↥L₁).index : ℂ) := by rw [hφ₁deg, index_hallCore_eq_relIndex]
  have hφ₂1 : φ₂ 1 = ((hallCore ↥L₂).index : ℂ) := by rw [hφ₂deg, index_hallCore_eq_relIndex]
  have hdisj' : Disjoint (totalDadeSupport ((CFSG.FeitThompson.hallCoreIn L₁ : Set G) \ {1})
      CFSG.FeitThompson.sigCoreSignalizer)
      (totalDadeSupport ((CFSG.FeitThompson.hallCoreIn L₂ : Set G) \ {1})
        CFSG.FeitThompson.sigCoreSignalizer) := Set.disjoint_iff_inter_eq_empty.2 hdisj
  have hβ₁ : CFSG.FeitThompson.tauDade L₁
      (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L₁) L₁ 1 - φ₁)
        = NormalInducedFamily.dadeBeta ((CFSG.FeitThompson.hallCoreIn L₁ : Set G) \ {1})
          CFSG.FeitThompson.sigCoreSignalizer (hallCore ↥L₁) φ₁ :=
    tauDade_indBetween_sub_eq_dadeBeta hD₁ (hS₁ ▸ hφ₁S) hφ₁1
  have hβ₂ : CFSG.FeitThompson.tauDade L₂
      (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L₂) L₂ 1 - φ₂)
        = NormalInducedFamily.dadeBeta ((CFSG.FeitThompson.hallCoreIn L₂ : Set G) \ {1})
          CFSG.FeitThompson.sigCoreSignalizer (hallCore ↥L₂) φ₂ :=
    tauDade_indBetween_sub_eq_dadeBeta hD₂ (hS₂ ▸ hφ₂S) hφ₂1
  have hc₁₂ : CFSG.FeitThompson.cfInnerFin (CFSG.FeitThompson.tauDade L₁
      (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L₁) L₁ 1 - φ₁)) (ν₂ φ₂)
      = cfInner (NormalInducedFamily.dadeBeta ((CFSG.FeitThompson.hallCoreIn L₁ : Set G) \ {1})
          CFSG.FeitThompson.sigCoreSignalizer (hallCore ↥L₁) (calLEnum L₁ ⟨φ₁, hφ₁⟩))
        (CrossFamilyProjection.coherentImage (calLEnum L₂) (coherentDadeHom hν₂) ⟨φ₂, hφ₂⟩) := by
    rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner, hβ₁, coherentImage_coherentDadeHom, calLEnum_mk]
  have hc₂₁ : CFSG.FeitThompson.cfInnerFin (CFSG.FeitThompson.tauDade L₂
      (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn L₂) L₂ 1 - φ₂)) (ν₁ φ₁)
      = cfInner (NormalInducedFamily.dadeBeta ((CFSG.FeitThompson.hallCoreIn L₂ : Set G) \ {1})
          CFSG.FeitThompson.sigCoreSignalizer (hallCore ↥L₂) (calLEnum L₂ ⟨φ₂, hφ₂⟩))
        (CrossFamilyProjection.coherentImage (calLEnum L₁) (coherentDadeHom hν₁) ⟨φ₁, hφ₁⟩) := by
    rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner, hβ₂, coherentImage_coherentDadeHom, calLEnum_mk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ξ hξ ζ hζ
    have key := DisjointCoherentFamilies.cfInner_coherentVal_coherentVal_eq_zero
      (isFullCoherentFamily_calLEnum hodd hD₁ hIrr₁ hν₁)
      (isFullCoherentFamily_calLEnum hodd hD₂ hIrr₂ hν₂)
      (Set.disjoint_iff_inter_eq_empty.2 hdisj)
      ⟨ξ, by rw [range_calLEnum]; exact hξ⟩ ⟨ζ, by rw [range_calLEnum]; exact hζ⟩
    rw [coherentVal_coherentDadeHom, coherentVal_coherentDadeHom] at key
    rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner]
    exact key
  · have key := NormalInducedFamily.cfInner_dadeBeta_nu_ne_zero_or_swap
      (ν₁ := coherentDadeHom hν₁) (ν₂ := coherentDadeHom hν₂)
      hodd hD₁ hD₂ (image_coe_hallCore_sdiff_one L₁).symm (image_coe_hallCore_sdiff_one L₂).symm
      hS₁ hS₂ (cfInner_coherentDadeHom hν₁) (cfInner_coherentDadeHom hν₂)
      (coe_coherentDadeHom_eq_dadeMap hν₁ hD₁) (coe_coherentDadeHom_eq_dadeMap hν₂ hD₂)
      hφ₁S (hIrr₁ hφ₁) hφ₁1 hφ₂S (hIrr₂ hφ₂) hφ₂1 hdisj'
    rw [coe_coherentDadeHom, coe_coherentDadeHom] at key
    rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner, CFSG.FeitThompson.cfInnerFin_eq_cfInner, hβ₁, hβ₂]
    exact key
  · intro hne
    rw [hc₁₂] at hne
    have key := div_index_le_index_sub_one_pair hodd hD₁ hD₂
      (image_coe_hallCore_sdiff_one L₁).symm (image_coe_hallCore_sdiff_one L₂).symm hS₁ hS₂
      (injective_calLEnum L₁) (injective_calLEnum L₂)
      (by rw [range_calLEnum]; exact hIrr₁) (by rw [range_calLEnum]; exact hIrr₂)
      (coe_baselineDadeHom_eq_dadeMap hν₁ hD₁) (coe_baselineDadeHom_eq_dadeMap hν₂ hD₂)
      (isCoherentWith_coherentDadeHom hν₁) (isCoherentWith_coherentDadeHom hν₂)
      (k₁ := ⟨φ₁, hφ₁⟩) (k₂ := ⟨φ₂, hφ₂⟩)
      (by rw [calLEnum_mk]; exact hφ₁1) (by rw [calLEnum_mk]; exact hφ₂1) hdisj'
      (two_mul_index_add_one_le hbd₁) (two_mul_index_add_one_le hbd₂) hne
    rw [natCard_hallCore_eq, index_hallCore_eq_relIndex, index_hallCore_eq_relIndex] at key
    have hq : ((((Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₂) : ℚ) - 1)
        / ((CFSG.FeitThompson.hallCoreIn L₂).relIndex L₂ : ℚ) : ℚ) : ℝ)
        ≤ ((((CFSG.FeitThompson.hallCoreIn L₁).relIndex L₁ : ℚ) - 1 : ℚ) : ℝ) := by
      push_cast
      exact key
    exact_mod_cast hq
  · intro hne
    rw [hc₂₁] at hne
    have key := div_index_le_index_sub_one_pair hodd hD₂ hD₁
      (image_coe_hallCore_sdiff_one L₂).symm (image_coe_hallCore_sdiff_one L₁).symm hS₂ hS₁
      (injective_calLEnum L₂) (injective_calLEnum L₁)
      (by rw [range_calLEnum]; exact hIrr₂) (by rw [range_calLEnum]; exact hIrr₁)
      (coe_baselineDadeHom_eq_dadeMap hν₂ hD₂) (coe_baselineDadeHom_eq_dadeMap hν₁ hD₁)
      (isCoherentWith_coherentDadeHom hν₂) (isCoherentWith_coherentDadeHom hν₁)
      (k₁ := ⟨φ₂, hφ₂⟩) (k₂ := ⟨φ₁, hφ₁⟩)
      (by rw [calLEnum_mk]; exact hφ₂1) (by rw [calLEnum_mk]; exact hφ₁1) hdisj'.symm
      (two_mul_index_add_one_le hbd₂) (two_mul_index_add_one_le hbd₁) hne
    rw [natCard_hallCore_eq, index_hallCore_eq_relIndex, index_hallCore_eq_relIndex] at key
    have hq : ((((Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₁) : ℚ) - 1)
        / ((CFSG.FeitThompson.hallCoreIn L₁).relIndex L₁ : ℚ) : ℚ) : ℝ)
        ≤ ((((CFSG.FeitThompson.hallCoreIn L₂).relIndex L₂ : ℚ) - 1 : ℚ) : ℝ) := by
      push_cast
      exact key
    exact_mod_cast hq


end

end CrossedTypeI

public section

open Subgroup CFSG.FeitThompson
  CFSG.FeitThompson CrossedTypeI

universe u

theorem dadeDomain_inter_eq_empty
    (h₁ : Statements.FPF_type_I_frobenius.{u})
    (h₂ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₃ : Statements.FTS_sigma_prime_separation.{u})
    (h₄ : Statements.FTS_type_I_dade_support.{u})
    (G : Type u) [Group G] [Finite G] (hG : IsOddOrderMinimalSimple G)
    {L₁ L₂ : Subgroup G} (hL₁ : IsCoatom L₁) (hL₂ : IsCoatom L₂)
    (hnc : ∀ g : G, L₂ ≠ CFSG.FeitThompson.conjSubgroup L₁ g)
    (hI₁ : IsTypeI L₁) (hI₂ : IsTypeI L₂) :
    CFSG.FeitThompson.dadeSupportDomain L₁ ∩ CFSG.FeitThompson.dadeSupportDomain L₂ = ∅ := by
  have : Fintype G := Fintype.ofFinite G
  have hcf := FCH_type_I_frobenius_coherent_family h₁ h₄ G
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, hS₁, -⟩ := hcf L₁ hL₁ hI₁
  obtain ⟨-, hS₂, -⟩ := hcf L₂ hL₂ hI₂
  have hS₁' : sigmaCore L₁ = CFSG.FeitThompson.hallCoreIn L₁ := hS₁
  have hS₂' : sigmaCore L₂ = CFSG.FeitThompson.hallCoreIn L₂ := hS₂
  rw [dadeDomain_eq_sigmaPacketSupport hS₁', dadeDomain_eq_sigmaPacketSupport hS₂']
  exact FTS_nonconjugate_packets_disjoint h₂ h₃ G
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
    L₁ L₂ hL₁ hL₂ (fun g => by rw [← conjSubgroup_eq_prep08]; exact hnc g)

theorem natCard_hallCoreIn_ne
    (h₁ : Statements.FPF_type_I_frobenius.{u})
    (h₃ : Statements.FTS_sigma_prime_separation.{u})
    (h₄ : Statements.FTS_type_I_dade_support.{u})
    (G : Type u) [Group G] [Finite G] (hG : IsOddOrderMinimalSimple G)
    {L₁ L₂ : Subgroup G} (hL₁ : IsCoatom L₁) (hL₂ : IsCoatom L₂)
    (hnc : ∀ g : G, L₂ ≠ CFSG.FeitThompson.conjSubgroup L₁ g)
    (hI₂ : IsTypeI L₂) :
    Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₁) ≠ Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₂) := by
  have : Fintype G := Fintype.ofFinite G
  have hcf := FCH_type_I_frobenius_coherent_family h₁ h₄ G
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, hh₂, -⟩ := hcf L₂ hL₂ hI₂
  have hh₂' : 1 < Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₂) := hh₂
  have hcop := FNI_nonconjugate_maxima_hall_cores_coprime h₃ G
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    L₂ L₁ hL₂ hL₁ (fun g h => hnc g h.symm)
  have hcop' : Nat.Coprime (Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₁))
    (Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₂)) := (hcop.1).symm
  intro heq
  rw [heq, Nat.coprime_self] at hcop'
  omega

theorem FCH_actual_type_I_crossed_control
    (h₁ : Statements.FPF_type_I_frobenius.{u})
    (h₂ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₃ : Statements.FTS_sigma_prime_separation.{u})
    (h₄ : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FCH_actual_type_I_crossed_control.{u} := by
  intro G _ _ hG L₁ L₂ hL₁ hL₂ hnc hI₁ hI₂ n₁ n₂ m₁ m₂ hn₁ hn₂ hm₁ hm₂
    ν₁ hν₁ ν₂ hν₂ φ₁ hφ₁ hφ₁deg φ₂ hφ₂ hφ₂deg β₁ β₂ hβ₁ hβ₂ c₁₂ c₂₁ hc₁₂ hc₂₁
  subst hn₁ hn₂ hm₁ hm₂ hβ₁ hβ₂ hc₁₂ hc₂₁
  have hcf := FCH_type_I_frobenius_coherent_family h₁ h₄ G
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, -, hbd₁, hD₁, -, -, -, hIrr₁, -⟩ := hcf L₁ hL₁ hI₁
  obtain ⟨-, -, -, -, hbd₂, hD₂, -, -, -, hIrr₂, -⟩ := hcf L₂ hL₂ hI₂
  have hbd₁' : 2 * (CFSG.FeitThompson.hallCoreIn L₁).relIndex L₁
    ≤ Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₁) - 1 := hbd₁
  have hbd₂' : 2 * (CFSG.FeitThompson.hallCoreIn L₂).relIndex L₂
    ≤ Nat.card ↥(CFSG.FeitThompson.hallCoreIn L₂) - 1 := hbd₂
  have hD₁' : IsDadeData L₁ ((CFSG.FeitThompson.hallCoreIn L₁ : Set G) \ {1})
    CFSG.FeitThompson.sigCoreSignalizer := hD₁
  have hD₂' : IsDadeData L₂ ((CFSG.FeitThompson.hallCoreIn L₂ : Set G) \ {1})
    CFSG.FeitThompson.sigCoreSignalizer := hD₂
  have _ : Fintype ↥L₁ := CFSG.FeitThompson.subgroupFintype L₁
  have _ : Fintype ↥L₂ := CFSG.FeitThompson.subgroupFintype L₂
  have hIrr₁' : CFSG.FeitThompson.calLFam L₁ ⊆ Irr ↥L₁ := by
    rw [← hallIndFamily_eq_calLFam L₁]; exact hIrr₁
  have hIrr₂' : CFSG.FeitThompson.calLFam L₂ ⊆ Irr ↥L₂ := by
    rw [← hallIndFamily_eq_calLFam L₂]; exact hIrr₂
  have hdisj := dadeDomain_inter_eq_empty h₁ h₂ h₃ h₄ G hG hL₁ hL₂ hnc hI₁ hI₂
  obtain ⟨ho, hnz, hb₁, hb₂⟩ := crossed_clauses_of_isDadeData hG.odd_natCard hD₁' hD₂'
    hIrr₁' hIrr₂' hdisj hbd₁' hbd₂' hν₁ hν₂ hφ₁ hφ₁deg hφ₂ hφ₂deg
  exact ⟨hdisj, ho, hnz, hb₁, hb₂⟩

end

end CFSG.FeitThompson.Proofs
