module

import CFSG.FeitThompson.Representations.TypePNoFittingInducedWitness
import CFSG.FeitThompson.Local.PairedFittingSaturationsDisjoint
import CFSG.FeitThompson.Representations.ActualPairedSupportSaturation
import CFSG.FeitThompson.Representations.TypeIIIToVCoherenceFrobeniusPartner
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
import CFSG.FeitThompson.Local.SplitPrimeKernelFreeComplement
public import CFSG.FeitThompson.Representations.TypePOrientedCoreFamily

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PairedFittingWitness

open Subgroup
open CFSG.FeitThompson (fittingIn hallCoreIn indBetween)

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

variable {G : Type*} [Group G]

theorem apply_one_eq_zero_of_additive {H : Type*} [Group H] {E : Type*} [AddCommGroup E]
    {ι : H → E} (hadd : ∀ x y : H, ι (x * y) = ι x + ι y) : ι 1 = 0 := by
  have h := hadd 1 1
  rw [one_mul] at h
  exact left_eq_add.mp h

theorem apply_pow_of_additive {H : Type*} [Group H] {E : Type*} [AddCommGroup E]
    {ι : H → E} (hadd : ∀ x y : H, ι (x * y) = ι x + ι y) (x : H) (n : ℕ) :
    ι (x ^ n) = n • ι x := by
  induction n with
  | zero => simpa using apply_one_eq_zero_of_additive hadd
  | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]

theorem natCast_eq_zero_of_card_eq_pow {E : Type*} [Field E] [Finite E] {q p : ℕ}
    (hq : q.Prime) (hp : p ≠ 0) (hcard : Nat.card E = q ^ p) : (q : E) = 0 := by
  have : Fintype E := Fintype.ofFinite E
  have hchar : CharP E (ringChar E) := ringChar.charP E
  have hprime : (ringChar E).Prime := CharP.char_is_prime E _
  obtain ⟨n, -, hcard'⟩ := FiniteField.card E (ringChar E)
  rw [Nat.card_eq_fintype_card] at hcard
  have hq' : ringChar E = q := by
    have hdvd : q ∣ (ringChar E) ^ (n : ℕ) := by
      rw [← hcard', hcard]; exact dvd_pow_self q hp
    exact ((Nat.prime_dvd_prime_iff_eq hq hprime).1 (hq.dvd_of_dvd_pow hdvd)).symm
  rw [← hq', CharP.cast_eq_zero]

theorem pow_eq_one_of_additive_field {E : Type*} [Field E] [Finite E] {q p : ℕ}
    (hq : q.Prime) (hp : p ≠ 0) (hcard : Nat.card E = q ^ p)
    {H : Subgroup G} {ι : ↥H → E} (hinj : Function.Injective ι)
    (hadd : ∀ x y : ↥H, ι (x * y) = ι x + ι y) {x : G} (hx : x ∈ H) : x ^ q = 1 := by
  have h1 : (⟨x, hx⟩ : ↥H) ^ q = 1 := by
    refine hinj ?_
    rw [apply_pow_of_additive hadd, apply_one_eq_zero_of_additive hadd, nsmul_eq_mul,
      natCast_eq_zero_of_card_eq_pow hq hp hcard, zero_mul]
  exact congrArg Subtype.val h1

theorem mul_comm_of_additive {E : Type*} [AddCommGroup E] {H : Subgroup G} {ι : ↥H → E}
    (hinj : Function.Injective ι) (hadd : ∀ x y : ↥H, ι (x * y) = ι x + ι y)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x := by
  have h : (⟨x, hx⟩ : ↥H) * ⟨y, hy⟩ = (⟨y, hy⟩ : ↥H) * ⟨x, hx⟩ := by
    refine hinj ?_
    rw [hadd, hadd, add_comm]
  exact congrArg Subtype.val h

theorem conjSub_eq_self_of_forall {K V₀ : Subgroup G}
    (hinv : ∀ x ∈ V₀, ∀ h ∈ K, x⁻¹ * h * x ∈ K) :
    ∀ g ∈ V₀, CFSG.FeitThompson.Prep03.conjSub K g = K := by
  intro g hg
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.1 hy
    simpa [MulAut.conj_apply] using hinv g hg y₀ hy₀
  · intro y hy
    refine Subgroup.mem_map.2 ⟨g * y * g⁻¹, by simpa using hinv g⁻¹ (inv_mem hg) y hy, ?_⟩
    change g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y
    group

noncomputable def multEquivULiftOfAdditive {H : Type*} [Group H] {E : Type*} [AddCommGroup E]
    {ι : H → E} (hbij : Function.Bijective ι) (hadd : ∀ x y : H, ι (x * y) = ι x + ι y) :
    H ≃* Multiplicative (ULift.{u} E) :=
  MulEquiv.mk' (((Equiv.ofBijective ι hbij).trans Equiv.ulift.symm).trans Multiplicative.ofAdd)
    (fun x y => by
      change Multiplicative.ofAdd (ULift.up (ι (x * y)))
        = Multiplicative.ofAdd (ULift.up (ι x)) * Multiplicative.ofAdd (ULift.up (ι y))
      rw [hadd]
      rfl)

theorem down_toAdd_multEquivULiftOfAdditive {H : Type*} [Group H] {E : Type*} [AddCommGroup E]
    {ι : H → E} (hbij : Function.Bijective ι) (hadd : ∀ x y : H, ι (x * y) = ι x + ι y) (x : H) :
    (Multiplicative.toAdd (multEquivULiftOfAdditive.{u} hbij hadd x)).down = ι x := (rfl)

noncomputable def fittingInEquiv [Finite G] (M : Subgroup G) :
    ↥(fittingRaw ↥M) ≃* ↥(fittingIn M) :=
  (fittingRaw ↥M).equivMapOfInjective M.subtype (Subgroup.subtype_injective M)

theorem coe_fittingInEquiv [Finite G] (M : Subgroup G) (x : ↥(fittingRaw ↥M)) :
    ((fittingInEquiv M x : ↥(fittingIn M)) : G) = ((x : ↥M) : G) := (rfl)

theorem mem_fittingIn_iff [Finite G] (M : Subgroup G) (z : ↥M) :
    ((z : G) ∈ fittingIn M) ↔ z ∈ fittingRaw ↥M := by
  constructor
  · intro h
    exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective M)).1
      (by simpa [CFSG.FeitThompson.fittingIn] using h)
  · intro h
    simpa [CFSG.FeitThompson.fittingIn] using Subgroup.mem_map_of_mem (M.subtype) h

theorem indBetween_eq_indClassFun_of_map [Fintype G] (L : Subgroup G) (K : Subgroup ↥L)
    (N : Subgroup G) (e : ↥K ≃* ↥N) (he : ∀ x : ↥K, ((e x : ↥N) : G) = ((x : ↥L) : G))
    (hmem : ∀ z : ↥L, ((z : G) ∈ N) ↔ z ∈ K) (θ : ↥N → ℂ) :
    indBetween N L θ = indClassFun K (θ ∘ e) := by
  classical
  funext y
  rw [CFSG.FeitThompson.indBetween_apply, indClassFun_apply]
  have hcard : Nat.card ↥N = Nat.card ↥K := (Nat.card_eq_of_bijective _ e.bijective).symm
  rw [hcard]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have hcoe : (((t : ↥L)⁻¹ * y * t : ↥L) : G)
      = ((t : ↥L) : G)⁻¹ * ((y : ↥L) : G) * ((t : ↥L) : G) := by simp
  by_cases hz : ((t : ↥L)⁻¹ * y * t) ∈ K
  · have hz' : ((t : ↥L) : G)⁻¹ * ((y : ↥L) : G) * ((t : ↥L) : G) ∈ N := by
      rw [← hcoe]; exact (hmem _).2 hz
    rw [dif_pos hz]
    have heq : e ⟨(t : ↥L)⁻¹ * y * t, hz⟩
        = ⟨((t : ↥L) : G)⁻¹ * ((y : ↥L) : G) * ((t : ↥L) : G), hz'⟩ := by
      apply Subtype.ext; rw [he]; exact hcoe
    rw [show ((t : ↥L) : G)⁻¹ * ((y : ↥L) : G) * ((t : ↥L) : G)
        = ((⟨_, hz'⟩ : ↥N) : G) from rfl, CFSG.FeitThompson.extendSub_apply_coe]
    simp only [Function.comp_apply, heq]
  · have hz' : ((t : ↥L) : G)⁻¹ * ((y : ↥L) : G) * ((t : ↥L) : G) ∉ N := by
      intro hcon
      rw [← hcoe] at hcon
      exact hz ((hmem _).1 hcon)
    rw [dif_neg hz, CFSG.FeitThompson.extendSub_apply_of_notMem N θ hz']

theorem indBetween_fittingIn [Fintype G] (M : Subgroup G) (θ : ↥(fittingIn M) → ℂ) :
    indBetween (fittingIn M) M θ = indClassFun (fittingRaw ↥M) (θ ∘ fittingInEquiv M) :=
  indBetween_eq_indClassFun_of_map M (fittingRaw ↥M) (fittingIn M) (fittingInEquiv M)
    (coe_fittingInEquiv M) (mem_fittingIn_iff M) θ

theorem exists_fittingWitness_iff [Fintype G] (M : Subgroup G) :
    (∃ ψ : ↥(fittingIn M) → ℂ, ψ ∈ Irr ↥(fittingIn M) ∧ ψ 1 = 1 ∧
        indBetween (fittingIn M) M ψ ∈ Irr ↥M ∧
        ¬ (∀ x : ↥M, (x : G) ∈ hallCoreIn M →
          indBetween (fittingIn M) M ψ x = indBetween (fittingIn M) M ψ 1)) ↔
      ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
        indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
        ¬ ∀ x : ↥M, (x : G) ∈ hallCoreIn M →
          indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1 := by
  constructor
  · rintro ⟨ψ, hirr, h1, hind, hker⟩
    refine ⟨ψ ∘ fittingInEquiv M,
      FrobeniusInduction.mem_Irr_comp_mulEquiv hirr (fittingInEquiv M), by simpa using h1, ?_, ?_⟩
    · rw [← indBetween_fittingIn]; exact hind
    · rw [← indBetween_fittingIn]; exact hker
  · rintro ⟨φ, hirr, h1, hind, hker⟩
    refine ⟨φ ∘ (fittingInEquiv M).symm,
      FrobeniusInduction.mem_Irr_comp_mulEquiv hirr (fittingInEquiv M).symm,
      by simpa using h1, ?_, ?_⟩
    · rw [indBetween_fittingIn]
      simpa [Function.comp_assoc] using hind
    · rw [indBetween_fittingIn]
      simpa [Function.comp_assoc] using hker

theorem indClassFun_eq_zero_of_notMem_satSet_sdiff_one [Fintype G]
    {M F : Subgroup G} {f : ↥M → ℂ}
    (hf : ∀ y : ↥M, (y : G) ∉ (F : Set G) \ {1} → f y = 0) {x : G}
    (hx : x ∉ CFSG.FeitThompson.satSet (F : Set G) \ {1}) : indClassFun M f x = 0 := by
  classical
  rw [indClassFun_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
  split_ifs with h
  · refine hf _ fun hmem => hx ⟨?_, ?_⟩
    · rw [CFSG.FeitThompson.mem_satSet_iff]
      refine ⟨t⁻¹, ?_⟩
      simp only [CFSG.FeitThompson.conjSet, Set.mem_image]
      exact ⟨_, hmem.1, by group⟩
    · intro hx1
      apply hmem.2
      rw [Set.mem_singleton_iff] at hx1 ⊢
      simp [hx1]
  · rfl

theorem mem_of_mem_span_int_of_subset_Irr {H : Type*} [Group H] [Fintype H] {X : Set (H → ℂ)}
    (hX : X ⊆ Irr H) {ξ : H → ℂ} (hξ : ξ ∈ Irr H) (hspan : ξ ∈ Submodule.span ℤ X) :
    ξ ∈ X := by
  classical
  by_contra hnot
  have key : ∀ f ∈ Submodule.span ℤ X, cfInner f ξ = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      rw [cfInner_eq_ite_of_mem_Irr (hX hf) hξ, if_neg fun h => hnot (by rw [← h]; exact hf)]
    | zero => exact cfInner_zero_left ξ
    | add f g _ _ hf hg => rw [cfInner_add_left, hf, hg, add_zero]
    | smul n f _ hf => rw [← Int.cast_smul_eq_zsmul ℂ, cfInner_smul_left, hf, mul_zero]
  have h1 := key ξ hspan
  rw [cfInner_eq_ite_of_mem_Irr hξ hξ, if_pos rfl] at h1
  exact one_ne_zero h1

theorem exists_mem_Irr_mem_detectInd_fittingIn [Fintype G] {M : Subgroup G}
    (hwit : ∃ ψ : ↥(fittingIn M) → ℂ, ψ ∈ Irr ↥(fittingIn M) ∧ ψ 1 = 1 ∧
      indBetween (fittingIn M) M ψ ∈ Irr ↥M ∧
      ¬ (∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indBetween (fittingIn M) M ψ x = indBetween (fittingIn M) M ψ 1)) :
    ∃ ξ : ↥M → ℂ, ξ ∈ Irr ↥M ∧ ξ ∈ CFSG.FeitThompson.Prep03.detectInd M
      (CFSG.FeitThompson.Prep03.fittingIn M) (CFSG.FeitThompson.Prep03.hallCoreIn M) := by
  obtain ⟨ψ, hψ, -, hlam, hker⟩ := (exists_fittingWitness_iff M).1 hwit
  refine ⟨_, hlam, ?_⟩
  rw [OrientedCoreFamily.detectInd_fittingIn_eq_indFamDetect, mem_indFamDetect_subgroupOf]
  refine ⟨ψ, by rw [← Irr_eq_irrChar]; exact hψ, ?_, rfl⟩
  by_contra hcon
  push Not at hcon
  apply hker
  intro x hx
  have hxH : x ∈ hallCore ↥M := (Subgroup.mem_map_iff_mem M.subtype_injective).1 hx
  have hsub := (subset_charValueKernel_indClassFun_iff (Z := hallCore ↥M)
    hallCore_le_fittingRaw hψ).2 (fun y hy => mem_charValueKernel.2 (hcon y hy))
  exact mem_charValueKernel.1 (hsub hxH)

end PairedFittingWitness

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup
open CFSG.FeitThompson
open CFSG.FeitThompson (fittingIn hallCoreIn indBetween satSet)
open CFSG.FeitThompson.PairedFittingWitness

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

private theorem exists_fittingInducedImage_aux
    (_h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (_h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (_h₃ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (_h₄ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (_h₅ : Statements.FTS_canonical_signalizer_structure.{u})
    (_h₆ : Statements.FTS_type_II_extended_support_ti.{u})
    {G : Type u} [Group G] [Fintype G]
    (_hG : CFSG.FeitThompson.IsOddOrderMinimalSimple G)
    {M U W W₁ W₂ : Subgroup G} [Fintype ↥W] [Fintype ↑(Irr ↥W₁)]
    (_hM : IsCoatom M) (_hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hW : IsCyclicTIPair W W₁ W₂)
    {ω : classFun ↥W →ₗ[ℂ] classFun G} (_hω : IsCyclicTIIsometry W W₁ W₂ ω)
    (_hwit : ∃ ψ : ↥(fittingIn M) → ℂ, ψ ∈ Irr ↥(fittingIn M) ∧ ψ 1 = 1 ∧
      indBetween (fittingIn M) M ψ ∈ Irr ↥M ∧
      ¬ (∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indBetween (fittingIn M) M ψ x = indBetween (fittingIn M) M ψ 1)) :
    ∃ (ρ : G → ℂ) (ε : ℂ) (j₀ : ↑(Irr ↥W₂)),
      ρ ∈ signedIrr G ∧ (ρ ≠ fun x => (starRingEnd ℂ) (ρ x)) ∧
      (∀ i j, cfInner ρ (hW.prodCharEta ω i j) = 0) ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ x ∉ (satSet (fittingIn M : Set G) \ {1}), ρ x - (starRingEnd ℂ) (ρ x) = 0) ∧
      (∀ x ∉ (satSet (fittingIn M : Set G) \ {1}),
        (ρ - ε • ∑ i : ↑(Irr ↥W₁), hW.prodCharEta ω i j₀) x = 0) := by
  classical
  open OrientedCoreFamily in
  have hG : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨_hG.odd_natCard, _hG.isSimpleGroup, _hG.not_isMulCommutative, _hG.isSolvable_of_ne_top⟩
  have hc := _hc
  have hM := _hM
  have hWeq : W = W₁ ⊔ W₂ :=
    eq_sup_of_coe_eq_mul hW.mul_eq.symm fun x hx y hy => hW.commute x hx y hy
  subst hWeq
  obtain rfl := Subsingleton.elim ‹Fintype ↥(W₁ ⊔ W₂)›
    (CFSG.FeitThompson.subgroupFintype _)
  have h1 := hc.le_M_W₁
  have h2 := hc.le_M_W₂
  have hodd := hG.odd_natCard
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdir, -, -, hTIF⟩ :=
    _h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
      M U W₁ W₂ hM hc _ _ rfl rfl
  have hmac := OrientedCoreFamily.isMinimalAbelianCore_of_isWitnessedPConfiguration _h₂ hG hM hc
  have hF := OrientedCoreFamily.coreProduct_eq_fittingRaw hc.le_M_E hdir
  have hP := OrientedCoreFamily.isPrimeCyclicTIHyp_commutator hodd hc
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  obtain ⟨τl, hτl⟩ := (hc.isPrimeCyclicTIHyp_subgroupOf hodd).exists_isCyclicTIIsometry
  have hσ : CFSG.FeitThompson.Prep03.IsTIExtension W₁ W₂ M
      ⇑(Recip.sigmaT h1 h2 hW.isCyclic τl) :=
    isTIExtension_sigma (sup_le h1 h2) (Recip.isSigmaMap_sigmaT h1 h2 hW.isCyclic hτl)
  have hσ' := OrientedCoreFamily.isCyclicTIIsometry_sigmaLocalHom h1 h2 hσ
  obtain ⟨δ, hδ, hδall⟩ := hmac.exists_primeTISign_eq hP hσ'
  obtain ⟨A, A₀, T, hD, τ, ν0, hA, hA₀, hVA, hS0, hν0, hντ0, hFA⟩ :=
    OrientedCoreFamily.exists_dadeBaseline _h₁ _h₂ _h₃ _h₄ _h₅ _h₆ hG hM hc
  have hMS : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      OrientedCoreFamily.ambRow h1 h2 hσ hP (j : Irr ↥W₂) ∈
        CFSG.FeitThompson.Prep03.detectInd M (⁅M, M⁆ : Subgroup G)
          (CFSG.FeitThompson.Prep03.hallCoreIn M) := by
    intro j
    rw [OrientedCoreFamily.ambRow_def, OrientedCoreFamily.detectInd_commutator_eq_indFamDetect]
    exact hmac.primeTIrow_mem_indFamDetect hP hσ'
      (OrientedCoreFamily.irrEquivOfMulEquiv_ne_principalIrr _ j.2)
  have hMT : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      OrientedCoreFamily.ambRow h1 h2 hσ hP (j : Irr ↥W₂) ∈
        CFSG.FeitThompson.Prep03.detectInd M
          (CFSG.FeitThompson.Prep03.fittingIn M)
          (CFSG.FeitThompson.Prep03.hallCoreIn M) := by
    intro j
    rw [OrientedCoreFamily.ambRow_def, OrientedCoreFamily.detectInd_fittingIn_eq_indFamDetect,
      ← hF]
    exact hmac.primeTIrow_mem_indFamDetect_coreProduct hP hσ'
      (OrientedCoreFamily.irrEquivOfMulEquiv_ne_principalIrr _ j.2)
  have hnorm : ∀ j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      cfInner (OrientedCoreFamily.ambRow h1 h2 hσ hP (j : Irr ↥W₂))
        (OrientedCoreFamily.ambRow h1 h2 hσ hP (j : Irr ↥W₂)) = (Nat.card ↥W₁ : ℂ) := by
    intro j
    rw [OrientedCoreFamily.ambRow_def, hP.cfInner_self_primeTIrow hσ', natCard_subgroupOf_eq h1]
  have horth : ∀ j k : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂}, j ≠ k →
      cfInner (OrientedCoreFamily.ambRow h1 h2 hσ hP (j : Irr ↥W₂))
        (OrientedCoreFamily.ambRow h1 h2 hσ hP (k : Irr ↥W₂)) = 0 := by
    intro j k hjk
    rw [OrientedCoreFamily.ambRow_def, OrientedCoreFamily.ambRow_def,
      cfInner_primeTIrow_primeTIrow hP hσ',
      if_neg fun h => hjk (Subtype.ext ((OrientedCoreFamily.irrEquivOfMulEquiv _).injective h))]
  have hupos : 0 < Nat.card ↥W₁ *
      (CFSG.FeitThompson.Prep03.cent U
        (CFSG.FeitThompson.Prep03.hallCoreIn M : Set G)).relIndex U := by
    refine Nat.mul_pos Nat.card_pos (Nat.pos_of_ne_zero ?_)
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hdegT : ∀ f ∈ CFSG.FeitThompson.Prep03.detectInd M
      (CFSG.FeitThompson.Prep03.fittingIn M)
      (CFSG.FeitThompson.Prep03.hallCoreIn M),
      f 1 = ((Nat.card ↥W₁ * (CFSG.FeitThompson.Prep03.cent U
        (CFSG.FeitThompson.Prep03.hallCoreIn M : Set G)).relIndex U :
          ℕ) : ℂ) :=
    fun f hf => OrientedCoreFamily.apply_one_of_mem_detectInd_fittingIn' hc.le_M_E h1 hP hmac hF
      rfl hf
  have hdeg := fun j => hdegT _ (hMT j)
  obtain ⟨ωM, hωM, hcol⟩ := OrientedCoreFamily.exists_isCyclicTIIsometry_prodCharEtaColSum_eq
    (OrientedCoreFamily.map_subgroupOf_sup h1 h2) (Subgroup.map_subgroupOf_eq_of_le h1)
    (Subgroup.map_subgroupOf_eq_of_le h2) hW
    (hP.isCyclicTIPair_map_subtype (OrientedCoreFamily.setOf_conj_eq_of_isCyclicTIPair h1 h2 hW)
      (OrientedCoreFamily.inter_eq_empty_of_isCyclicTIPair h1 h2 hW)) _hω
  have hirr : ∀ j : Irr ↥W₂, ∀ (x : ↥((W₂.subgroupOf M).map M.subtype)) (hx : (x : G) ∈ W₂),
      ((irrMapSubtype M (W₂.subgroupOf M)
        (OrientedCoreFamily.irrEquivOfMulEquiv (Subgroup.subgroupOfEquivOfLe h2) j) : Irr _) :
        ↥((W₂.subgroupOf M).map M.subtype) → ℂ) x = (j : ↥W₂ → ℂ) ⟨x, hx⟩ := by
    intro j x hx
    rw [coe_irrMapSubtype, Function.comp_apply, OrientedCoreFamily.coe_irrEquivOfMulEquiv,
      Function.comp_apply]
    refine congrArg (j : ↥W₂ → ℂ) (Subtype.ext ?_)
    have h := coe_mapSubtypeEquiv M (W₂.subgroupOf M)
      ((mapSubtypeEquiv M (W₂.subgroupOf M)).symm x)
    rw [MulEquiv.apply_symm_apply] at h
    rw [Subgroup.subgroupOfEquivOfLe_apply_coe, ← h]
  have htau : ∀ j k : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      (ν0 ⟨_, Submodule.subset_span (hMS j)⟩ : G → ℂ)
        - (ν0 ⟨_, Submodule.subset_span (hMS k)⟩ : G → ℂ)
      = δ • hW.prodCharEtaColSum ω (j : Irr ↥W₂)
        - δ • hW.prodCharEtaColSum ω (k : Irr ↥W₂) := by
    intro j k
    have hj := OrientedCoreFamily.irrEquivOfMulEquiv_ne_principalIrr
      (Subgroup.subgroupOfEquivOfLe h2) j.2
    have hk := OrientedCoreFamily.irrEquivOfMulEquiv_ne_principalIrr
      (Subgroup.subgroupOfEquivOfLe h2) k.2
    have key := OrientedCoreFamily.coe_nu_primeTIrow_sub_eq (ν0 := ν0) (ω := ωM) hP hσ'
      (OrientedCoreFamily.le_hallCore_subgroupOf_W₂ hc) (H := hallCore ↥M) (A := A)
      (by have := @hallCore_normal ↥M _; exact hA) hA₀ hD
      (OrientedCoreFamily.setOf_conj_eq_of_isCyclicTIPair h1 h2 hW)
      (OrientedCoreFamily.inter_eq_empty_of_isCyclicTIPair h1 h2 hW) hωM hS0
      (fun f hf => OrientedCoreFamily.mem_classFun_of_mem_span_detectInd hf) hντ0 hj hk
      (fun i => by rw [OrientedCoreFamily.primeTIirr_one_eq_relIndex hP hmac hσ' i hj,
        OrientedCoreFamily.primeTIirr_one_eq_relIndex hP hmac hσ' i hk])
      (by rw [← OrientedCoreFamily.ambRow_def]; exact hMS j)
      (by rw [← OrientedCoreFamily.ambRow_def]; exact hMS k)
    rw [hδall _ hj, hcol _ _ (hirr j), hcol _ _ (hirr k)] at key
    simpa only [OrientedCoreFamily.ambRow_def] using key
  have hclass := fun hempty =>
    OrientedCoreFamily.detectInd_commutator_eq_range_ambRow h1 h2 hσ hP hmac hempty
  obtain ⟨ν, hν, e, he, hνrow, -, -⟩ := OrientedCoreFamily.exists_isCoherentWith_ambRow hodd h1
    h2 hσ hW _hω hP hc hD hVA hS0 hν0 (fun f F hfF => hντ0 f F hfF) hMS hnorm horth hupos hdeg
    hδ htau hclass
  have hνD := fun f F hfF =>
    OrientedCoreFamily.coe_nu_eq_dadeMap_of_isCoherentWith hν hν0 hD hντ0 f F hfF
  have hsupp : ∀ (f : ↥M → ℂ) (hf : f ∈ Submodule.span ℤ
      (CFSG.FeitThompson.Prep03.detectInd M (⁅M, M⁆ : Subgroup G)
        (CFSG.FeitThompson.Prep03.hallCoreIn M))),
      (∀ y : ↥M, (y : G) ∉ (fittingIn M : Set G) \ {1} → f y = 0) →
      ∀ x ∉ satSet (fittingIn M : Set G) \ {1}, (ν ⟨f, hf⟩ : G → ℂ) x = 0 := by
    intro f hf hf0 x hx
    have hdom : f ∈ dadeDomain M ((fittingIn M : Set G) \ {1}) :=
      mem_dadeDomain.2 ⟨OrientedCoreFamily.mem_classFun_of_mem_span_detectInd hf, hf0⟩
    rw [hνD ⟨f, hf⟩ ⟨f, dadeDomain_mono hFA hdom⟩ rfl, dadeMap_eq_indClassFun hD hTIF hFA f hdom]
    exact indClassFun_eq_zero_of_notMem_satSet_sdiff_one hf0 hx
  have hTdiff : ∀ f g : ↥M → ℂ,
      (∀ y : ↥M, (y : G) ∉ fittingIn M → f y = 0) →
      (∀ y : ↥M, (y : G) ∉ fittingIn M → g y = 0) → f 1 = g 1 →
      ∀ y : ↥M, (y : G) ∉ (fittingIn M : Set G) \ {1} → (f - g) y = 0 := by
    intro f g hf hg h1' y hy
    by_cases hyF : (y : G) ∈ fittingIn M
    · have hy1 : y = 1 := by
        by_contra hne
        exact hy ⟨hyF, fun h => hne (Subtype.ext h)⟩
      rw [hy1, Pi.sub_apply, h1', sub_self]
    · rw [Pi.sub_apply, hf y hyF, hg y hyF, sub_zero]
  obtain ⟨ξ, hξIrr, hξT⟩ := exists_mem_Irr_mem_detectInd_fittingIn _hwit
  have hξS : ξ ∈ CFSG.FeitThompson.Prep03.detectInd M
      (⁅M, M⁆ : Subgroup G) (CFSG.FeitThompson.Prep03.hallCoreIn M) := by
    rcases OrientedCoreFamily.eq_ambRow_or_mem_span_inter_Irr h1 h2 hσ hP hmac hF hξT with
      ⟨k, hk, hξk⟩ | hspan
    · exfalso
      have hn := hnorm ⟨k, hk⟩
      rw [← hξk, cfInner_eq_ite_of_mem_Irr hξIrr hξIrr, if_pos rfl] at hn
      have h1lt : 1 < Nat.card ↥W₁ := (Subgroup.one_lt_card_iff_ne_bot W₁).2 hc.ne_bot_W₁
      have : (Nat.card ↥W₁ : ℂ) = 1 := hn.symm
      exact absurd (by exact_mod_cast this : Nat.card ↥W₁ = 1) h1lt.ne'
    · exact (mem_of_mem_span_int_of_subset_Irr Set.inter_subset_right hξIrr hspan).1
  obtain ⟨hρs, hρnr, hρstar, hρη, -⟩ :=
    OrientedCoreFamily.nu_signedIrr_of_mem_detectInd_inter_Irr hodd hW _hω hc hD hVA hS0 hν hνD
      hξS hξIrr
  obtain ⟨k, hk⟩ := exists_ne_principalIrr hc.ne_bot_W₂ hc.isCyclic_W₂
  have hξ0 : ∀ y : ↥M, (y : G) ∉ fittingIn M → ξ y = 0 := fun y hy =>
    eq_zero_of_mem_detectInd_fittingIn hξT hy
  have hsS := OrientedCoreFamily.star_mem_detectInd_commutator M hξS
  refine ⟨(ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ), (-1 : ℂ) ^ e * δ, starIrr^[e] k, hρs,
    ?_, hρη, ?_, ?_, ?_⟩
  · intro h
    refine hρnr (funext fun x => ?_)
    rw [Pi.star_apply, Complex.star_def]
    exact (congrFun h x).symm
  · rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> norm_num
  · intro x hx
    have hsub := CoherentRowColumn.coe_nu_sub (ν := ν) hξS hsS
    rw [hρstar] at hsub
    have h0 := hsupp _ (sub_mem (Submodule.subset_span hξS) (Submodule.subset_span hsS))
      (hTdiff ξ (star ξ) hξ0 (fun y hy => by rw [Pi.star_apply, hξ0 y hy, star_zero])
        (by rw [Pi.star_apply, hdegT ξ hξT, star_natCast])) x hx
    rw [← hsub, Pi.sub_apply, Pi.star_apply, Complex.star_def] at h0
    exact h0
  · intro x hx
    have hsub := CoherentRowColumn.coe_nu_sub (ν := ν) hξS (hMS ⟨k, hk⟩)
    rw [hνrow ⟨k, hk⟩, IsCyclicTIPair.prodCharEtaColSum_eq_sum] at hsub
    have h0 := hsupp _
      (sub_mem (Submodule.subset_span hξS) (Submodule.subset_span (hMS ⟨k, hk⟩)))
      (hTdiff ξ _ hξ0 (fun y hy => eq_zero_of_mem_detectInd_fittingIn (hMT ⟨k, hk⟩) hy)
        (by rw [hdegT ξ hξT, hdegT _ (hMT ⟨k, hk⟩)])) x hx
    rw [← hsub] at h0
    exact h0

private theorem noPartnerWitness_aux
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : Statements.FTS_type_II_extended_support_ti.{u})
    (G : Type u) [Group G] [Fintype G]
    (hG : CFSG.FeitThompson.IsOddOrderMinimalSimple G)
    {M U W₁ W₂ N V₀ : Subgroup G} (hM : IsCoatom M)
    (hcM : IsWitnessedPConfiguration M U W₁ W₂) (hN : IsCoatom N) (hNM : N ≠ M)
    (hV₀N : V₀ ≤ N) (hcN : IsWitnessedPConfiguration N V₀ W₂ W₁)
    (hwit : ∃ ψ : ↥(fittingIn M) → ℂ, ψ ∈ Irr ↥(fittingIn M) ∧ ψ 1 = 1 ∧
      indBetween (fittingIn M) M ψ ∈ Irr ↥M ∧
      ¬ (∀ x : ↥M, (x : G) ∈ hallCoreIn M →
        indBetween (fittingIn M) M ψ x = indBetween (fittingIn M) M ψ 1)) :
    ¬ ∃ φ : ↥(fittingIn N) → ℂ, φ ∈ Irr ↥(fittingIn N) ∧ φ 1 = 1 ∧
      indBetween (fittingIn N) N φ ∈ Irr ↥N ∧
      ¬ (∀ x : ↥N, (x : G) ∈ hallCoreIn N →
        indBetween (fittingIn N) N φ x = indBetween (fittingIn N) N φ 1) := by
  classical
  intro hwitN
  have _ : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have _ : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  have hA : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ :=
    hcM.isCyclicTIPair_sup_of_isAmbient h₂ hA hM
  obtain ⟨ω, hω⟩ := hW.exists_isCyclicTIIsometry
  obtain ⟨ρ, ε, jM, hρ, hρnr, hρη, hε, hρD, hρD'⟩ :=
    exists_fittingInducedImage_aux h₁ h₂ h₃ h₄ h₅ h₆ hG hM hcM hW hω hwit
  obtain ⟨s, δ, iN, hs, hsnr, hsη, hδ, hsE, hsE'⟩ :=
    exists_fittingInducedImage_aux h₁ h₂ h₃ h₄ h₅ h₆ hG hN hcN hW.swap hω.swap hwitN
  have hdisj : Disjoint (satSet (fittingIn M : Set G) \ {1})
      (satSet (fittingIn N : Set G) \ {1}) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact FCH_paired_fitting_saturations_disjoint h₂ G hG M U W₁ W₂ hM hcM _ _ _ rfl rfl rfl
      _ _ _ rfl rfl rfl N V₀ hN hNM hV₀N hcN _ _ _ rfl rfl rfl _ rfl
  refine not_of_disjoint_support_of_row_column
    (η := fun i j => hW.prodCharEta ω i j)
    (fun i j => hW.prodCharEta_mem_virtualChars hω i j)
    (fun i j i' j' => ?_) hρ hs hsnr hρη ?_ hdisj iN jM hε hδ hρD hρD' hsE ?_
  · rw [hW.cfInner_prodCharEta hω i i' j j']
    congr 1
  ·
    intro i j
    rw [← prodCharEta_swap hW hW.swap ω i j]
    exact hsη j i
  ·
    intro x hx
    have h := hsE' x hx
    have hsum : (∑ i : ↑(Irr ↥W₂), hW.swap.prodCharEta ω i iN)
        = ∑ j : ↑(Irr ↥W₂), hW.prodCharEta ω iN j :=
      Finset.sum_congr rfl fun j _ => prodCharEta_swap hW hW.swap ω iN j
    rw [← hsum]
    exact h

theorem FCH_paired_fitting_witness_excludes_partner
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FCH_paired_fitting_witness_excludes_partner.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hcM H F C hH hF hC p q u hp hq hu N V₀ hN hNM hV₀N hcN
    HN FN DN hHN hFN hDN v hv hwit
  subst hH hF hC hHN hFN hDN hp hq hu hv
  have hA : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hnoW : ¬ ∃ φ : ↥(fittingIn N) → ℂ, φ ∈ Irr ↥(fittingIn N) ∧ φ 1 = 1 ∧
      indBetween (fittingIn N) N φ ∈ Irr ↥N ∧
      ¬ (∀ x : ↥N, (x : G) ∈ hallCoreIn N →
        indBetween (fittingIn N) N φ x = indBetween (fittingIn N) N φ 1) :=
    noPartnerWitness_aux h₁ h₂ h₃ h₄ h₅ h₆ G hG hM hcM hN hNM hV₀N hcN hwit
  have hno : ¬ ∃ ψ ∈ Irr ↥(fittingRaw ↥N), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥N) ψ ∈ Irr ↥N ∧
      ¬ ∀ x : ↥N, (x : G) ∈ hallCoreIn N →
        indClassFun (fittingRaw ↥N) ψ x = indClassFun (fittingRaw ↥N) ψ 1 :=
    fun hcon => hnoW ((exists_fittingWitness_iff N).2 hcon)
  obtain ⟨hqp, hpp, -, -, -, hDN, hFN, hcardV, hcount, hmin, E, hEfield, hEfin, ι, hEcard,
      hιbij, hιadd, hact, hactsurj, -, -⟩ :=
    CFSG.FeitThompson.Proofs.FCH_type_p_no_fitting_induced_witness h₂ G hA N V₀ W₂ W₁
      ⟨hA, hN, hcN⟩ (Nat.card ↥W₁) (Nat.card ↥W₂)
      ((CFSG.FeitThompson.Prep03.cent V₀
        (hallCoreIn N : Set G)).relIndex V₀) rfl rfl rfl hno
  have hppos : 0 < Nat.card ↥W₂ := hpp.pos
  have hqpos : 0 < Nat.card ↥W₁ := hqp.pos
  have hsumpos : 0 < ∑ i ∈ Finset.range (Nat.card ↥W₂), Nat.card ↥W₁ ^ i :=
    Finset.sum_pos (fun i _ => pow_pos hqpos i) (Finset.nonempty_range_iff.2 hppos.ne')
  refine ⟨hnoW, hDN, hFN, hcardV, hcount, ?_, ⟨ULift.{u} E, inferInstance,
    multEquivULiftOfAdditive.{u} hιbij hιadd, ?_, ?_, ?_⟩⟩
  ·
    intro K hKHN hKinv
    exact hmin K hKHN
      (fun x hx y hy => mul_comm_of_additive hιbij.injective hιadd (hKHN hx) (hKHN hy))
      (fun x hx => pow_eq_one_of_additive_field hqp hppos.ne' hEcard hιbij.injective hιadd
        (hKHN hx))
      (conjSub_eq_self_of_forall hKinv)
  · rw [Nat.card_ulift]; exact hEcard
  ·
    intro x hx
    obtain ⟨a, ha, hrel⟩ := hact x hx
    refine ⟨ULift.up a, ?_, ULift.ext (by simpa using ha), fun h hh hc => ?_⟩
    · intro h0
      have ha0 : a = 0 := congrArg ULift.down h0
      rw [ha0, zero_pow hsumpos.ne'] at ha
      exact zero_ne_one ha
    · exact ULift.ext (hrel h hh hc)
  ·
    intro a _ha0 ha
    obtain ⟨x, hx, hrel⟩ := hactsurj a.down (by simpa using congrArg ULift.down ha)
    exact ⟨x, hx, fun h hh hc => ULift.ext (hrel h hh hc)⟩

end CFSG.FeitThompson.Proofs

end
