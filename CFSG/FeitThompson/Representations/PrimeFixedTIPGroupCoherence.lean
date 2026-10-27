module

public import CFSG.FeitThompson.Representations.CoreDetectingFamilyAntirealBlocks
public import CFSG.FeitThompson.Representations.CentralLinearJoinedFamilyFullExtension
public import CFSG.FeitThompson.Representations.QuotientLayerDegreeSquareSum
public import CFSG.FeitThompson.Representations.CentralSectionThresholdWeightedCoherence
public import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
public import CFSG.FeitThompson.Representations.CoprimeDegreeInvariantCharExtends
public import CFSG.FeitThompson.Representations.PrimeFixedTIPGroupCoherenceSupport
import CFSG.FeitThompson.Representations.FreeCentralSectionJointCoherence
import CFSG.FeitThompson.Representations.CentralPrimeCoherentCentralLinear
import CFSG.FeitThompson.Representations.CrossMaximalFirstWitnessValue
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
public import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
public import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
public import Mathlib.GroupTheory.SpecificGroups.ZGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PrimeFixedTIPGroupCoherence

open Subgroup

section Family

variable {L : Type*} [Group L] [Fintype L]

theorem irrDetect_top_eq_sdiff (K : Type*) [Group K] [Finite K] :
    irrDetect ℂ (⊤ : Subgroup K) = Irr K \ {1} := by
  ext θ
  rw [mem_irrDetect, Set.mem_sdiff, Set.mem_singleton_iff, ← Irr_eq_irrChar]
  refine and_congr_right fun hθ => ?_
  constructor
  · intro hker hθ1
    refine hker fun x _ => mem_charValueKernel.2 ?_
    simp [hθ1]
  · intro hne hker
    exact hne (eq_one_of_mem_Irr_of_forall_apply_eq hθ
      fun k => mem_charValueKernel.1 (hker (Subgroup.mem_top k)))

theorem indFamDetect_self_eq_indFam_sdiff (K : Subgroup L) :
    indFamDetect K (K.subgroupOf K) = indFam K (Irr ↥K \ {1}) := by
  rw [Subgroup.subgroupOf_self, indFamDetect_eq_indFam, irrDetect_top_eq_sdiff]

theorem coe_fullFamily_eq_indFam_sdiff (K : Subgroup L) :
    (CentralSectionFullExtension.fullFamily K : Set (L → ℂ)) = indFam K (Irr ↥K \ {1}) := by
  ext f
  rw [Finset.mem_coe, CentralSectionFullExtension.fullFamily,
    NormalInducedFamily.mem_kerLayerIndFinset, CentralSectionCoherence.kerLayerIndFam_bot]

theorem coe_fullFamily_eq_indFamDetect_self (K : Subgroup L) :
    (CentralSectionFullExtension.fullFamily K : Set (L → ℂ))
      = indFamDetect K (K.subgroupOf K) := by
  rw [coe_fullFamily_eq_indFam_sdiff, indFamDetect_self_eq_indFam_sdiff]

end Family

section Support

variable {L : Type*} [Group L]

private theorem eq_one_of_conj_eq_one {y g : L} (h : g⁻¹ * y * g = 1) : y = 1 := by
  have hy : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  rw [h] at hy
  simpa using hy

theorem conj_image_punctured_eq (K : Subgroup L) [K.Normal] (t : L) :
    (fun a => t⁻¹ * a * t) '' ((K : Set L) \ {1}) = (K : Set L) \ {1} := by
  have hmem : ∀ (y g : L), y ∈ K → g⁻¹ * y * g ∈ K := by
    intro y g hy
    simpa [mul_assoc] using ‹K.Normal›.conj_mem y hy g⁻¹
  ext x
  constructor
  · rintro ⟨y, ⟨hyK, hy1⟩, rfl⟩
    refine ⟨hmem y t hyK, ?_⟩
    simp only [Set.mem_singleton_iff] at hy1 ⊢
    exact fun hc => hy1 (eq_one_of_conj_eq_one hc)
  · rintro ⟨hxK, hx1⟩
    refine ⟨t * x * t⁻¹, ⟨?_, ?_⟩, by group⟩
    · simpa [mul_assoc] using ‹K.Normal›.conj_mem x hxK t
    · simp only [Set.mem_singleton_iff] at hx1 ⊢
      exact fun hc => hx1 (eq_one_of_conj_eq_one (g := t⁻¹) (by simpa using hc))

theorem centralizer_sdiff_subset_punctured (K : Subgroup L) (y : L) :
    ((K ⊓ Subgroup.centralizer ({y} : Set L) : Subgroup L) : Set L) \ {1}
      ⊆ (K : Set L) \ {1} :=
  fun _ hx => ⟨hx.1.1, hx.2⟩

end Support

section FixedCoset

variable {L : Type*} [Group L] [Finite L]

private theorem map_zpowers' {M N : Type*} [Group M] [Group N] (f : M →* N) (x : M) :
    Subgroup.map f (zpowers x) = zpowers (f x) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, by simp⟩
  · rintro ⟨n, rfl⟩
    exact ⟨x ^ n, ⟨n, rfl⟩, by simp⟩

theorem mem_commutator_of_fixed_coset {K W₁ W₂ : Subgroup L}
    (h : IsPrimeCyclicTIHyp K W₁ W₂) [Group.IsSolvable ↥K] (hW₂ : W₂ ≤ ⁅K, K⁆)
    {u : L} (hu : u ∈ W₁) (hu1 : u ≠ 1) {k : L} (hk : k ∈ K)
    (hfix : k⁻¹ * (u⁻¹ * k * u) ∈ (⁅K, K⁆ : Subgroup L)) : k ∈ ⁅K, K⁆ := by
  have hKn := h.normal
  have hNn : (⁅K, K⁆ : Subgroup L).Normal := Subgroup.commutator_normal K K
  set N : Subgroup L := ⁅K, K⁆ with hN
  set q : L →* L ⧸ N := QuotientGroup.mk' N with hq
  have hcop : (Nat.card ↥(zpowers u)).Coprime (Nat.card ↥K) :=
    (h.coprime_natCard.coprime_dvd_right
      (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hu))).symm
  have hnorm : (zpowers u) ≤ Subgroup.normalizer (K : Set L) := by
    intro x _
    refine Subgroup.mem_set_normalizer_iff''.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · simpa [mul_assoc] using hKn.conj_mem y hy x⁻¹
    · simpa [mul_assoc] using hKn.conj_mem _ hy x
  have hkey := inf_centralizer_map_mk'_eq_map (N := N) (Q := K) (A := zpowers u) hcop hnorm
  have hcent : (K ⊓ Subgroup.centralizer ((zpowers u : Subgroup L) : Set L)) = W₂ := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact h.centralizer_eq u hu hu1
  have himg :
      Subgroup.map q (K ⊓ Subgroup.centralizer ((zpowers u : Subgroup L) : Set L)) = ⊥ := by
    rw [hcent, eq_bot_iff]
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff _).2 (hW₂ hy))
  have hbase : Commute (q u) (q k) := by
    have h1 : q (k⁻¹ * (u⁻¹ * k * u)) = 1 := (QuotientGroup.eq_one_iff _).2 hfix
    simp only [map_mul, map_inv] at h1
    have h2 : q k = (q u)⁻¹ * q k * q u := inv_mul_eq_one.1 h1
    change q u * q k = q k * q u
    calc q u * q k = q u * ((q u)⁻¹ * q k * q u) := by rw [← h2]
      _ = q k * q u := by group
  have hqk : q k ∈ Subgroup.map q K ⊓
      Subgroup.centralizer ((Subgroup.map q (zpowers u) : Subgroup (L ⧸ N)) : Set (L ⧸ N)) := by
    refine Subgroup.mem_inf.2 ⟨⟨k, hk, rfl⟩, ?_⟩
    rw [map_zpowers' q u, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.2 hbase.symm.eq
  rw [hkey, himg, Subgroup.mem_bot] at hqk
  exact (QuotientGroup.eq_one_iff _).1 hqk

theorem fixesOnlyCommutatorCoset_of_isPrimeCyclicTIHyp {K W₁ W₂ : Subgroup L}
    (h : IsPrimeCyclicTIHyp K W₁ W₂)
    [Group.IsSolvable ↥K] (hW₂ : W₂ ≤ ⁅K, K⁆) :
    FrobeniusQuotientLayer.FixesOnlyCommutatorCoset K W₁ := by
  have hKn := h.normal
  rw [FrobeniusQuotientLayer.fixesOnlyCommutatorCoset_iff_forall_fixedPointFree]
  intro u hu hu1 x hx
  obtain ⟨k, rfl⟩ := abelianization_of_surjective ↥K x
  rw [FrobeniusQuotientLayer.conjAbelianizationAut_of,
    FrobeniusQuotientLayer.abelianization_of_eq_iff] at hx
  rw [FrobeniusQuotientLayer.abelianization_of_eq_one_iff,
    ← NormalLinearInduced.coe_mem_commutator_iff K]
  refine mem_commutator_of_fixed_coset h hW₂ hu hu1 k.2 ?_
  have h2 := (NormalLinearInduced.coe_mem_commutator_iff K).2 hx
  rw [Subgroup.coe_mul, Subgroup.coe_inv, conjNormal_inv_coe] at h2
  have h3 := inv_mem h2
  rwa [show ((u⁻¹ * (k : L) * u)⁻¹ * (k : L))⁻¹ = (k : L)⁻¹ * (u⁻¹ * (k : L) * u) by group] at h3

end FixedCoset

section Config

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]

structure IsPrimeFixedTIPGroupData (p a : ℕ) (K W₁ W₂ : Subgroup ↥L)
    [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L)
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G)
    (A₀ : Set G) (T : G → Subgroup G) (ζ : ↥L → ℂ) : Prop where
  primeCyclicTI : IsPrimeCyclicTIHyp K W₁ W₂
  sigma_isometry : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ
  odd_natCard : Odd (Nat.card G)
  isDadeData : IsDadeData L A₀ T
  image_subset :
    (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀
  stabilizer_cyclicTIDiff_eq :
    {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G)
  inter_cyclicTIDiff_eq_empty : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
    (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅
  omega_isometry : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
    (W₂.map L.subtype) ω
  zeta_mem : ζ ∈ indFam K (Irr ↥K \ {1})
  zeta_irr : ζ ∈ Irr ↥L
  zeta_apply_one : ζ 1 = (Nat.card ↥W₁ : ℂ)
  prime : p.Prime
  odd_prime : Odd p
  one_le_exponent : 1 ≤ a
  not_isMulCommutative : ¬ IsMulCommutative ↥K
  natCard_eq_pow : Nat.card ↥K = p ^ a
  natCard_right_eq_prime : Nat.card ↥W₂ = p
  right_le_commutator : W₂ ≤ ⁅K, K⁆
  stabilizer_punctured_eq :
    {g : G | (fun x => g⁻¹ * x * g) '' (((K.map L.subtype : Subgroup G) : Set G) \ {1})
      = ((K.map L.subtype : Subgroup G) : Set G) \ {1}} = (L : Set G)
  inter_conj_punctured_eq_empty : ∀ g ∉ L,
    (((K.map L.subtype : Subgroup G) : Set G) \ {1})
      ∩ ((fun x => g⁻¹ * x * g) '' (((K.map L.subtype : Subgroup G) : Set G) \ {1})) = ∅

namespace IsPrimeFixedTIPGroupData

variable [Fintype ↑(Irr ↥W₁)] {p a : ℕ} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G} {A₀ : Set G} {T : G → Subgroup G}
  {ζ : ↥L → ℂ} (h : IsPrimeFixedTIPGroupData p a K W₁ W₂ σ ω A₀ T ζ)

include h

theorem normal : K.Normal := h.primeCyclicTI.normal

theorem isNilpotent : Group.IsNilpotent ↥K :=
  isNilpotent_of_natCard_eq_prime_pow h.prime h.natCard_eq_pow

theorem isSolvable : Group.IsSolvable ↥K :=
  have := h.isNilpotent
  inferInstance

theorem fixesOnlyCommutatorCoset :
    FrobeniusQuotientLayer.FixesOnlyCommutatorCoset K W₁ :=
  have := h.isSolvable
  fixesOnlyCommutatorCoset_of_isPrimeCyclicTIHyp h.primeCyclicTI h.right_le_commutator

theorem exists_isSubcoherent_fullFamily :
    ∃ R : (↥L → ℂ) → Finset (G → ℂ),
      IsSubcoherent (CentralSectionFullExtension.fullFamily K) (dadeMapFun L A₀ T) R := by
  have hKn := h.normal
  obtain ⟨R, hR, -⟩ := PrimeDadeSubcoherence.exists_isSubcoherent_indFamDetect
    (ω := ω) (A₀ := A₀) (T := T) h.odd_natCard h.primeCyclicTI h.sigma_isometry
    (H := K) h.primeCyclicTI.right_le le_rfl (A := (K : Set ↥L) \ {1})
    (fun t => conj_image_punctured_eq K t)
    (fun y _ _ => centralizer_sdiff_subset_punctured K y)
    h.image_subset h.isDadeData h.stabilizer_cyclicTIDiff_eq h.inter_cyclicTIDiff_eq_empty
    h.omega_isometry (coe_fullFamily_eq_indFamDetect_self K)
  exact ⟨R, hR⟩

end IsPrimeFixedTIPGroupData

end Config

section Node

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  [Fintype ↑(Irr ↥W₁)] {p a : ℕ} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G} {A₀ : Set G} {T : G → Subgroup G}
  {ζ : ↥L → ℂ}

open PrimeFixedTIPGroupTransport CentralSectionFullExtension
open WeightedFeitExtension (subTauHom subTauHom_apply)
open NormalLinearInduced (indFamLinear)

namespace IsPrimeFixedTIPGroupData

variable (h : IsPrimeFixedTIPGroupData p a K W₁ W₂ σ ω A₀ T ζ)

include h

theorem left_ne_bot : K ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card ↥K = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [h.natCard_eq_pow] at h1
  have h2 : 1 < p ^ a := Nat.one_lt_pow (by have := h.one_le_exponent; omega) h.prime.one_lt
  omega

theorem punctured_nonempty :
    (((K.map L.subtype : Subgroup G) : Set G) \ {1}).Nonempty := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.left_ne_bot
  exact ⟨((x : ↥L) : G), ⟨x, x.2, rfl⟩, by
    simp only [Set.mem_singleton_iff]
    exact fun hc => hx (Subtype.ext (by simpa using hc))⟩

theorem dadeMapFun_eq_indClassFun {f : ↥L → ℂ}
    (hf : f ∈ Submodule.span ℤ (indFam K (Irr ↥K \ {1}))) (hf1 : f 1 = 0) :
    dadeMapFun L A₀ T f = indClassFun L f := by
  have hKn := h.normal
  set D : Set G := ((K.map L.subtype : Subgroup G) : Set G) \ {1} with hD
  have hDimg : D = (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) := (image_coe_sdiff_one K).symm
  have hDA₀ : D ⊆ A₀ := by
    rw [hDimg]; exact (Set.image_mono subset_bridgeSupport_left).trans h.image_subset
  have hfd : f ∈ dadeDomain L D :=
    NormalInducedFamily.mem_dadeDomain_of_mem_span_indFam hDimg
      (indFam_mono K (fun _ hx => hx.1)) hf hf1
  obtain ⟨hfc, hf0⟩ := mem_dadeDomain.1 hfd
  have hfA₀ : f ∈ dadeDomain L A₀ :=
    mem_dadeDomain.2 ⟨hfc, fun x hx => hf0 x (fun hc => hx (hDA₀ hc))⟩
  have hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' D = D ↔ g ∈ L := by
    intro g
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · have hmem : g ∈ {g : G | (fun x => g⁻¹ * x * g) '' D = D} := hg
      rw [hD, h.stabilizer_punctured_eq] at hmem
      exact hmem
    · have hmem : g ∈ (L : Set G) := hg
      rw [← h.stabilizer_punctured_eq] at hmem
      exact hmem
  have key := dadeMap_eq_indClassFun_of_stabilizer_eq h.isDadeData hDA₀ h.punctured_nonempty
    hstab h.inter_conj_punctured_eq_empty f hfd
  rw [coe_dadeMap h.isDadeData ⟨f, hfA₀⟩] at key
  exact key

theorem isComplement' : K.IsComplement' W₁ := by
  have hKn := h.normal
  refine (isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ h.primeCyclicTI.inf_eq_bot).symm
  refine SetLike.ext' (Set.eq_univ_of_forall fun x => ?_)
  obtain ⟨k, hk, w, hw, rfl⟩ := h.primeCyclicTI.exists_decomp x
  exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hw)

theorem isPrimeFixedTISetup :
    IsPrimeFixedTISetup G p a L (K.map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) :=
  isPrimeFixedTISetup_map_subtype h.prime h.odd_prime h.one_le_exponent h.odd_natCard
    h.primeCyclicTI h.not_isMulCommutative h.natCard_eq_pow h.natCard_right_eq_prime
    h.right_le_commutator h.stabilizer_punctured_eq h.inter_conj_punctured_eq_empty

theorem forall_mem_commutator_of_fixed_coset :
    ∀ u ∈ W₁, u ≠ 1 → ∀ k ∈ K, k⁻¹ * (u⁻¹ * k * u) ∈ (⁅K, K⁆ : Subgroup ↥L) →
      k ∈ (⁅K, K⁆ : Subgroup ↥L) :=
  have := h.isSolvable
  fun u hu hu1 k hk hfx =>
    mem_commutator_of_fixed_coset h.primeCyclicTI h.right_le_commutator hu hu1 hk hfx

end IsPrimeFixedTIPGroupData

theorem indFamNonprincipalFinset_eq_fullFamily (K : Subgroup ↥L) :
    indFamNonprincipalFinset ((K.map L.subtype).subgroupOf L) = fullFamily K := by
  rw [subgroupOf_map_subtype_self]
  ext f
  rw [mem_indFamNonprincipalFinset, nonprincipalIrr_eq_sdiff_singleton, fullFamily,
    NormalInducedFamily.mem_kerLayerIndFinset, CentralSectionCoherence.kerLayerIndFam_bot]

theorem centralFam_eq_coe_fullFamily (K : Subgroup ↥L) :
    CentralPrimeInduction.centralFam L (K.map L.subtype)
      = (fullFamily K : Set (↥L → ℂ)) := by
  rw [CentralPrimeInduction.centralFam_eq_indFam, subgroupOf_map_subtype_self,
    nonprincipalIrr_eq_sdiff_singleton, coe_fullFamily_eq_indFam_sdiff]

theorem coe_joinedFamily_eq_union (K Zl : Subgroup ↥L) :
    indFamDetect K (Zl.subgroupOf K) ∪ indFamLinear K = (joinedFamily K Zl : Set (↥L → ℂ)) := by
  rw [coe_joinedFamily, FrobeniusQuotientLayer.kerLayerIndFam_commutator_eq_indFamLinear]

theorem isSubcoherent_congr_baseline {S : Finset (↥L → ℂ)} {tau tau' : (↥L → ℂ) → (G → ℂ)}
    {R : (↥L → ℂ) → Finset (G → ℂ)} (hc : IsSubcoherent S tau R)
    (heq : ∀ f ∈ intSpanZeroAtOne (S : Set (↥L → ℂ)), tau' f = tau f) :
    IsSubcoherent S tau' R where
  isCharacter := hc.isCharacter
  ne_zero := hc.ne_zero
  star_mem := hc.star_mem
  star_ne := hc.star_ne
  charInner_eq_zero := hc.charInner_eq_zero
  map_add f hf g hg := by
    rw [heq _ (add_mem hf hg), heq _ hf, heq _ hg]; exact hc.map_add f hf g hg
  tau_mem f hf := by rw [heq _ hf]; exact hc.tau_mem f hf
  charInner_tau_tau f hf g hg := by
    rw [heq _ hf, heq _ hg]; exact hc.charInner_tau_tau f hf g hg
  tau_apply_one f hf := by rw [heq _ hf]; exact hc.tau_apply_one f hf
  R_subset := hc.R_subset
  charInner_R_self := hc.charInner_R_self
  charInner_R_of_ne := hc.charInner_R_of_ne
  tau_sub_star χ hχ := by rw [heq _ (hc.sub_star_mem hχ)]; exact hc.tau_sub_star χ hχ
  charInner_R_R := hc.charInner_R_R

theorem isCoherent_indFam_sdiff
    (_h : IsPrimeFixedTIPGroupData p a K W₁ W₂ σ ω A₀ T ζ)
    (τ : charSpanZero (indFam K (Irr ↥K \ {1})) →+ virtualChars G)
    (_hτ : ∀ f : charSpanZero (indFam K (Irr ↥K \ {1})),
      ((τ f : virtualChars G) : G → ℂ) = dadeMapFun L A₀ T (f : ↥L → ℂ)) :
    IsCoherent (indFam K (Irr ↥K \ {1})) τ := by
  classical
  have hKn := _h.normal
  have hLodd : Odd (Nat.card ↥L) := odd_natCard_subgroup _h.odd_natCard L
  have hs := _h.isPrimeFixedTISetup
  obtain ⟨R, hRdade⟩ := _h.exists_isSubcoherent_fullFamily
  have hspan0 : ∀ f ∈ intSpanZeroAtOne ((fullFamily K : Finset (↥L → ℂ)) : Set (↥L → ℂ)),
      f ∈ Submodule.span ℤ (indFam K (Irr ↥K \ {1})) ∧ f 1 = 0 := by
    intro f hf
    obtain ⟨hspan, h1⟩ := mem_intSpanZeroAtOne.1 hf
    rw [coe_fullFamily_eq_indFam_sdiff] at hspan
    exact ⟨hspan, h1⟩
  have hRind : IsSubcoherent (fullFamily K) (indClassFun L) R :=
    isSubcoherent_congr_baseline hRdade
      fun f hf => (_h.dadeMapFun_eq_indClassFun (hspan0 f hf).1 (hspan0 f hf).2).symm
  set Z : Subgroup G := centralSection (K.map L.subtype) (W₂.map L.subtype) with hZdef
  set Zl : Subgroup ↥L := Z.subgroupOf L with hZldef
  have hZL : Z ≤ L := hs.centralSection_le_middle
  have hZlnormal : Zl.Normal := hs.centralSection_normal_subgroupOf
  have hZlK : Zl ≤ K :=
    subgroupOf_le_of_le_map (hs.centralSection_le.trans (inf_le_left.trans inf_le_left))
  have hZlcomm : Zl ≤ ⁅K, K⁆ := subgroupOf_le_of_le_map (X := ⁅K, K⁆) (Z := Z)
    (by rw [← commutator_map_subtype_self]; exact hs.centralSection_le.trans inf_le_right)
  have hZlcent : Zl ≤ Subgroup.centralizer (K : Set ↥L) :=
    subgroupOf_le_centralizer (hs.centralSection_le.trans (inf_le_left.trans inf_le_right))
  have hZlbot : ⊥ < Zl :=
    bot_lt_iff_ne_bot.2 (subgroupOf_ne_bot_of_ne_bot hZL hs.centralSection_ne_bot)
  have hW₁nt : Nontrivial ↥W₁ :=
    (Subgroup.nontrivial_iff_ne_bot W₁).2 _h.primeCyclicTI.left_ne_bot
  have hbranchset : indFamDetect K (Zl.subgroupOf K) ∪ indFamLinear K
      = (joinedFamily K Zl : Set (↥L → ℂ)) := coe_joinedFamily_eq_union K Zl
  have hUS : indFamDetect K (Zl.subgroupOf K) ∪ indFamLinear K
      ⊆ ((fullFamily K : Finset (↥L → ℂ)) : Set (↥L → ℂ)) := by
    rw [hbranchset]; exact fun x hx => joinedFamily_subset hx
  have hfixG : FrobeniusQuotientLayer.FixesOnlyCommutatorCoset
      ((K.map L.subtype).subgroupOf L) ((W₁.map L.subtype).subgroupOf L) := by
    rw [subgroupOf_map_subtype_self, subgroupOf_map_subtype_self]
    exact _h.fixesOnlyCommutatorCoset
  have hbranch : IsCoherent (indFamDetect K (Zl.subgroupOf K) ∪ indFamLinear K)
      (subTauHom hRind hUS) := by
    by_cases hQ : (W₂.map L.subtype) ⊓ ((K.map L.subtype) ⊓
        Subgroup.centralizer ((K.map L.subtype : Subgroup G) : Set G)) = ⊥
    ·
      have hfcs := isFreeCentralSection_centralSection hs hQ hLodd _h.primeCyclicTI.mul_eq_univ
        _h.primeCyclicTI.inf_eq_bot _h.primeCyclicTI.left_ne_bot _h.stabilizer_punctured_eq
        _h.inter_conj_punctured_eq_empty
      have hPn : ((K.map L.subtype).subgroupOf L).Normal := hfcs.normal_subgroupOf
      have hZn : (Z.subgroupOf L).Normal := hZlnormal
      have hsetA : indFamDetect ((K.map L.subtype).subgroupOf L)
            ((Z.subgroupOf L).subgroupOf ((K.map L.subtype).subgroupOf L)) ∪
              indFamLinear ((K.map L.subtype).subgroupOf L)
          = indFamDetect K (Zl.subgroupOf K) ∪ indFamLinear K := by
        rw [subgroupOf_map_subtype_self]
      have hUS' : indFamDetect ((K.map L.subtype).subgroupOf L)
            ((Z.subgroupOf L).subgroupOf ((K.map L.subtype).subgroupOf L)) ∪
              indFamLinear ((K.map L.subtype).subgroupOf L)
          ⊆ ((fullFamily K : Finset (↥L → ℂ)) : Set (↥L → ℂ)) := by rw [hsetA]; exact hUS
      refine isCoherent_subTauHom_congr hRind hsetA (hUS := hUS') (hU'S := hUS) ?_
      exact FreeCentralSectionJointCoherence.IsFreeCentralSection.isCoherent_indFamDetect_union_indFamLinear
        hfcs
        (not_isMulCommutative_map_subtype _h.not_isMulCommutative)
        (isCyclic_map_subtype _h.primeCyclicTI.isCyclic_left)
        (hs.centralSection_le.trans inf_le_right) hfixG
        (indFamNonprincipalFinset_eq_fullFamily K).symm hRind _
        (fun f => subTauHom_apply hRind hUS' f)
    ·
      have hcpi := isCentralPrimeInduction_centralSection hs hQ _h.primeCyclicTI.mul_eq_univ
        _h.primeCyclicTI.inf_eq_bot _h.primeCyclicTI.left_ne_bot
        _h.forall_mem_commutator_of_fixed_coset _h.stabilizer_punctured_eq
        _h.inter_conj_punctured_eq_empty
      have hPn : ((K.map L.subtype).subgroupOf L).Normal := hcpi.normal_subgroupOf
      have hsetB : CentralPrimeInduction.centralDetectFam L (K.map L.subtype) Z ∪
            indFamLinear ((K.map L.subtype).subgroupOf L)
          = indFamDetect K (Zl.subgroupOf K) ∪ indFamLinear K := by
        rw [CentralPrimeInduction.centralDetectFam_eq_indFamDetect, subgroupOf_map_subtype_self]
      have hUS' : CentralPrimeInduction.centralDetectFam L (K.map L.subtype) Z ∪
            indFamLinear ((K.map L.subtype).subgroupOf L)
          ⊆ ((fullFamily K : Finset (↥L → ℂ)) : Set (↥L → ℂ)) := by rw [hsetB]; exact hUS
      refine isCoherent_subTauHom_congr hRind hsetB (hUS := hUS') (hU'S := hUS) ?_
      exact CentralPrimeInduction.exists_isCoherent_centralDetectFam_union_indFamLinear
        hcpi (centralFam_eq_coe_fullFamily K).symm hRind _
        (fun f => subTauHom_apply hRind hUS' f)
  have hjoin : IsCoherent (joinedFamily K Zl : Set (↥L → ℂ))
      (subTauHom hRdade (joinedFamily_subset (P := K) (Z := Zl))) := by
    refine CentralSectionCoherence.isCoherent_of_eq hbranchset (fun f h1 h2 => ?_) hbranch
    rw [subTauHom_apply hRind hUS ⟨f, h1⟩,
      subTauHom_apply hRdade (joinedFamily_subset (P := K) (Z := Zl)) ⟨f, h2⟩]
    refine (_h.dadeMapFun_eq_indClassFun ?_ (mem_charSpanZero.1 h2).2).symm
    have hsub : ((joinedFamily K Zl : Finset (↥L → ℂ)) : Set (↥L → ℂ))
        ⊆ indFam K (Irr ↥K \ {1}) := by
      rw [← coe_fullFamily_eq_indFam_sdiff]
      exact fun x hx => joinedFamily_subset hx
    exact Submodule.span_mono hsub (mem_charSpanZero.1 h2).1
  have hcase : (∀ u ∈ W₁, u ≠ 1 → Zl ⊓ Subgroup.centralizer {u} = ⊥) ∨
      (∀ u ∈ W₁, u ≠ 1 → K ⊓ Subgroup.centralizer {u} = Zl) := by
    by_cases hQ : (W₂.map L.subtype) ⊓ ((K.map L.subtype) ⊓
        Subgroup.centralizer ((K.map L.subtype : Subgroup G) : Set G)) = ⊥
    · refine Or.inl fun u hu hu1 => subgroupOf_inf_centralizer_singleton_eq_bot ?_
      exact hs.inf_centralizer_singleton_centralSection_eq_bot hQ ⟨u, hu, rfl⟩
        (fun hc => hu1 (Subtype.ext hc))
    · refine Or.inr fun u hu hu1 => ?_
      have hZW₂ : Zl = W₂ := by
        rw [hZldef, hZdef, centralSection_of_inf_ne_bot hQ, subgroupOf_map_subtype_self]
      rw [hZW₂]
      exact _h.primeCyclicTI.centralizer_eq u hu hu1
  obtain ⟨ν₀, hν₀⟩ := isCoherent_iff.1 hjoin
  have hfull := isCoherent_fullFamily hRdade _h.prime _h.odd_prime _h.one_le_exponent
    _h.natCard_eq_pow hLodd _h.isComplement' _h.primeCyclicTI.coprime_natCard
    _h.primeCyclicTI.isCyclic_left hZlbot hZlK hZlcomm hZlcent _h.primeCyclicTI.mul_eq_univ
    _h.fixesOnlyCommutatorCoset hcase hν₀
  refine CentralSectionCoherence.isCoherent_of_eq (coe_fullFamily_eq_indFam_sdiff K)
    (fun f h1 h2 => ?_) hfull
  rw [subTauHom_apply hRdade (Finset.Subset.rfl (s := fullFamily K)) ⟨f, h1⟩, _hτ ⟨f, h2⟩]

end Node

end PrimeFixedTIPGroupCoherence

end CFSG.FeitThompson
