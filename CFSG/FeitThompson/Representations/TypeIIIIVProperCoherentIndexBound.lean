module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Representations.TypeIIIIVChiefLayerNoncoherence
import CFSG.FeitThompson.Local.TypeIIIIVChiefData
public import CFSG.FeitThompson.Representations.CentralSectionThresholdWeightedCoherence
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise NormalInducedFamily CentralSectionCoherence WeightedFeitExtension
open CFSG.FeitThompson.Prep05

universe u

variable {G : Type*} [Group G] [Finite G] {M U W₁ W₂ H₀ : Subgroup G}

omit [Finite G] in
theorem subgroupOf_lt_subgroupOf {A B : Subgroup G} (hAM : A ≤ M) (hBM : B ≤ M) (h : A < B) :
    A.subgroupOf M < B.subgroupOf M := by
  refine lt_of_le_of_ne (Subgroup.subgroupOf_mono M h.le) fun hcon => h.ne ?_
  have h2 := congrArg (Subgroup.map M.subtype) hcon
  rwa [Subgroup.map_subgroupOf_eq_of_le hAM, Subgroup.map_subgroupOf_eq_of_le hBM] at h2

theorem isMinimalSimpleOdd_of_isMinimalOddSimple {X : Type u} [Group X] [Finite X]
    (hX : CFSG.FeitThompson.Prep06.IsMinimalOddSimple X) : IsMinimalSimpleOdd X :=
  ⟨hX.odd, hX.simple, hX.nonabelian, hX.solvable⟩

omit [Finite G] in
open scoped Classical in
theorem indFamKer_eq_kerLayerIndFam [Fintype G] (M : Subgroup G) (K A : Subgroup ↥M) :
    CFSG.FeitThompson.Prep06.indFamKer M K A = kerLayerIndFam A K := by
  ext f
  rw [CFSG.FeitThompson.Prep06.indFamKer_eq, mem_indFam, mem_kerLayerIndFam]
  constructor
  · rintro ⟨θ, ⟨hnp, hker⟩, rfl⟩
    obtain ⟨hirr, hne⟩ := mem_nonprincipalIrr.1 hnp
    exact ⟨θ, mem_kerLayerIrr.2 ⟨hirr, hker, hne⟩, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    obtain ⟨hirr, hker, hne⟩ := mem_kerLayerIrr.1 hθ
    exact ⟨θ, ⟨mem_nonprincipalIrr.2 ⟨hirr, hne⟩, hker⟩, rfl⟩

theorem isCoherent_subTauHom_of_hasCoherentMap {X : Type u} [Group X] [Fintype X]
    {N V₁ V₂ : Subgroup X} [Fintype ↥N] {Sfin : Finset (↥N → ℂ)}
    {tau : (↥N → ℂ) → X → ℂ} {R : (↥N → ℂ) → Finset (X → ℂ)}
    (hc : IsSubcoherent Sfin tau R)
    (htau : ∀ f, tau f = CFSG.FeitThompson.Prep06.dadeTau N V₁ V₂ f)
    {S : Set (↥N → ℂ)} (hUS : S ⊆ ↑Sfin)
    (h : CFSG.FeitThompson.Prep06.HasCoherentMap N V₁ V₂ S) :
    IsCoherent S (subTauHom hc hUS) := by
  obtain ⟨ν, hiso, heq⟩ := h
  refine isCoherent_iff.2 ⟨ν, ⟨fun f g => (hiso f g).trans (cfInner_inst _ _ _ _), fun f => ?_⟩⟩
  refine Subtype.ext ?_
  rw [subTauHom_apply, htau]
  exact heq _ (mem_charSpanZero.1 f.2).2

theorem exists_isCoherentAt_of_isCoherent_subTauHom {X : Type u} [Group X] [Finite X] [Fintype X]
    {N V₁ V₂ : Subgroup X} [Fintype ↥N] {Sfin : Finset (↥N → ℂ)}
    {tau : (↥N → ℂ) → X → ℂ} {R : (↥N → ℂ) → Finset (X → ℂ)}
    (hc : IsSubcoherent Sfin tau R)
    (htau : ∀ f, tau f = CFSG.FeitThompson.Prep06.dadeTau N V₁ V₂ f)
    {S S₀ : Set (↥N → ℂ)} (hUS : S ⊆ ↑Sfin) (hS : S = S₀)
    (h : IsCoherent S (subTauHom hc hUS)) :
    ∃ ν : Submodule.span ℤ S₀ →+ (X → ℂ), IsCoherentAt N S₀ (tauDerived N V₁ V₂) ν := by
  subst hS
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 h
  refine ⟨AddMonoidHom.mk' (fun f => (ν f : X → ℂ)) (fun a b => by simp), ?_, ?_, ?_⟩
  · intro f; exact (ν f).2
  · intro f g
    rw [cfIP_eq_cfInner_of_finite, cfIP_eq_cfInner_of_finite]
    exact (hν.inner_eq f g).trans (cfInner_inst _ _ _ _)
  · intro f hf1
    have hfz : (f : ↥N → ℂ) ∈ charSpanZero S := mem_charSpanZero.2 ⟨f.2, hf1⟩
    have h2 := hν.eq_on_zero ⟨(f : ↥N → ℂ), hfz⟩
    rw [show Submodule.inclusion (charSpanZero_le S) ⟨(f : ↥N → ℂ), hfz⟩ = f from rfl] at h2
    change (ν f : X → ℂ) = _
    rw [h2, subTauHom_apply, htau, tauDerived_eq_dadeTau]

theorem commutator_fittingOf_le_sup
    (hdir : IsInternalDirectProduct (fittingOf M) (hallCoreOf M) (centralizerIn U (hallCoreOf M)))
    (hHH : ⁅hallCoreOf M, hallCoreOf M⁆ ≤ H₀) :
    ⁅(fittingOf M : Subgroup G), (fittingOf M : Subgroup G)⁆
      ≤ H₀ ⊔ centralizerIn U (hallCoreOf M) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hx' : x ∈ (hallCoreOf M : Set G) * (centralizerIn U (hallCoreOf M) : Set G) := by
    rw [← hdir.coe_eq_mul]; exact hx
  have hy' : y ∈ (hallCoreOf M : Set G) * (centralizerIn U (hallCoreOf M) : Set G) := by
    rw [← hdir.coe_eq_mul]; exact hy
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx'
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy'
  rw [commutatorElement_mul_mul_of_forall_commute (fun _ ha _ hb => hdir.commute ha hb)
    ha₁ ha₂ hb₁ hb₂]
  refine Subgroup.mul_mem _
    (Subgroup.mem_sup_left (hHH (Subgroup.commutator_mem_commutator ha₁ ha₂)))
    (Subgroup.mem_sup_right ?_)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hb₁ hb₂) (inv_mem hb₁)) (inv_mem hb₂)

theorem index_fittingRaw_eq_mul
    (hsemi₁ : FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) (U ⊔ W₁))
    (hsemi₂ : FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁)
    (hdir : IsInternalDirectProduct (fittingOf M) (hallCoreOf M)
      (centralizerIn U (hallCoreOf M))) :
    (fittingRaw ↥M).index = Nat.card ↥W₁ * (centralizerIn U (hallCoreOf M)).relIndex U := by
  have hcardF : Nat.card ↥(fittingRaw ↥M) = Nat.card ↥(fittingOf M) := by
    rw [fittingOf_eq]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ M.subtype_injective).toEquiv
  have hcardC : Nat.card ↥(centralizerIn U (hallCoreOf M)) *
      (centralizerIn U (hallCoreOf M)).relIndex U = Nat.card ↥U := by
    have h := Subgroup.card_mul_index ((centralizerIn U (hallCoreOf M)).subgroupOf U)
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (centralizerIn_le U (hallCoreOf M))).toEquiv] at h
    exact h
  have hMcard : Nat.card ↥M = Nat.card ↥(hallCoreOf M) * (Nat.card ↥U * Nat.card ↥W₁) := by
    rw [hsemi₁.natCard_eq_mul, hsemi₂.natCard_eq_mul]
  have hidx := Subgroup.index_mul_card (fittingRaw ↥M)
  rw [hcardF, hdir.card_eq_mul, hMcard] at hidx
  have hkey : (fittingRaw ↥M).index *
      (Nat.card ↥(hallCoreOf M) * Nat.card ↥(centralizerIn U (hallCoreOf M)))
      = (Nat.card ↥W₁ * (centralizerIn U (hallCoreOf M)).relIndex U) *
        (Nat.card ↥(hallCoreOf M) * Nat.card ↥(centralizerIn U (hallCoreOf M))) := by
    rw [hidx, ← hcardC]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos) hkey

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05
open CFSG.FeitThompson.NormalInducedFamily
open CFSG.FeitThompson.CentralSectionCoherence
open CFSG.FeitThompson.WeightedFeitExtension

universe u

open scoped Classical in
theorem FPF_type_iii_iv_proper_coherent_index_bound
    (h₁ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₂ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₃ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_proper_coherent_index_bound.{u} := by
  classical
  intro G _ _ hG M U W₁ W₂ hM htype hc H₀ hH₀norm hH₀ hH₀lt hH₀max N hNnorm hNlt hNcoh
  have hG5 : IsMinimalSimpleOdd G := isMinimalSimpleOdd_of_isMinimalOddSimple hG
  have hsolvM : Group.IsSolvable ↥M := hG5.isSolvable_of_ne_top M hM.1
  have hlayer : IsChiefLayer M H₀ (hallCoreOf M) := by
    refine ⟨hH₀norm, hH₀lt, fun N' hN' hle hle' => ?_⟩
    by_cases h1 : N' = H₀
    · exact Or.inl h1
    by_cases h2 : N' = hallCoreOf M
    · exact Or.inr h2
    exact absurd ⟨lt_of_le_of_ne hle (Ne.symm h1), lt_of_le_of_ne hle' h2⟩ (hH₀max N' hN')
  obtain ⟨-, hq, -, -, -, hUne, hsemi₁, hsemi₂, -, -, -, -, hdir, -, -, hlayers⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data h₃ G hG5 M U W₁ W₂ hM htype hc _ _ rfl rfl
  obtain ⟨⟨-, hHH, -, -⟩, -, hnormB, -, -, -, -⟩ := hlayers H₀ hH₀ hlayer
  obtain ⟨hchar, hstar, hstarne, horth, htauC, ⟨R, hR, hRR⟩, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_weighted_normal_family h₁ h₂ G hG M U W₁ W₂ hM htype hc
      _ rfl
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
  have hSeq : kerLayerIndFam ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M)
      (CFSG.FeitThompson.Prep06.derivedOf M)
      = derivedIndFamKer M (H₀ ⊔ centralizerIn U (hallCoreOf M)) := by
    rw [derivedIndFamKer_eq_kerLayerIndFam M (H₀ ⊔ centralizerIn U (hallCoreOf M)),
      subgroupOf_commutator_self]
    exact kerLayerIndFam_inst _ _ _ _
  set K : Subgroup ↥M := CFSG.FeitThompson.Prep06.derivedOf M with hK
  set A : Subgroup ↥M := N.subgroupOf M with hA
  set B : Subgroup ↥M := (H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M with hB
  set F : Subgroup ↥M := fittingRaw ↥M with hF
  have hKnormal : K.Normal := by rw [hK, CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  have hKsolv : Group.IsSolvable ↥K := by
    rw [hK, CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  have hAnormal : A.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNnorm
  have hBnormal : B.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnormB
  have hNM : N ≤ M := hNlt.le.trans (Subgroup.commutator_le_self M)
  have hAK : A < K := by
    rw [hA, hK, ← subgroupOf_commutator_self M]
    exact subgroupOf_lt_subgroupOf hNM (Subgroup.commutator_le_self M) hNlt
  have hBD : B ≤ F := by
    rw [hB, hF, ← subgroupOf_fittingOf M]
    exact Subgroup.subgroupOf_mono M (sup_le_fittingOf hc hsolvM hq hUne hlayer)
  have hCK : F ≤ K := hF ▸ fittingRaw_le_derivedOf hc
  have hcomm : ⁅F, F⁆ ≤ B := by
    rw [hF, hB, ← subgroupOf_fittingOf M]
    exact commutator_subgroupOf_le (commutator_fittingOf_le_sup hdir hHH)
  have hAS : kerLayerIndFam A K ⊆ (hfin.toFinset : Set (↥M → ℂ)) := by
    rw [hStar]; exact kerLayerIndFam_subset_bot _ _
  have hBS : kerLayerIndFam B K ⊆ (hfin.toFinset : Set (↥M → ℂ)) := by
    rw [hStar]; exact kerLayerIndFam_subset_bot _ _
  have hUS : kerLayerIndFam A K ∪ kerLayerIndFam B K ⊆ (hfin.toFinset : Set (↥M → ℂ)) :=
    Set.union_subset hAS hBS
  have hcohA : IsCoherent (kerLayerIndFam A K) (subTauHom hsub hAS) := by
    refine isCoherent_subTauHom_of_hasCoherentMap hsub (fun _ => rfl) hAS ?_
    rw [← indFamKer_eq_kerLayerIndFam M K A]
    exact hNcoh
  have hnB : ¬ IsCoherent (kerLayerIndFam B K) (subTauHom hsub hBS) := by
    intro hcoh
    obtain ⟨ν, hν⟩ := exists_isCoherentAt_of_isCoherent_subTauHom hsub (fun _ => rfl) hBS hSeq hcoh
    exact CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_layer_noncoherence h₁ h₂ h₃ G hG5 M U W₁ W₂
      hM htype hc H₀ hH₀ hlayer ⟨ν, hν⟩
  have hbound := le_two_mul_index_mul_sqrt_of_not_isCoherent (D := F) (C := F)
    hsub hAK hBD le_rfl hCK hcomm hAS hBS hUS hcohA hnB
  rw [Subgroup.relIndex_self, Nat.cast_one, Real.sqrt_one, mul_one] at hbound
  rw [hF, index_fittingRaw_eq_mul hsemi₁ hsemi₂ hdir] at hbound
  have hAeq : A.relIndex K = N.relIndex (⁅M, M⁆ : Subgroup G) := by
    rw [hA, hK, ← subgroupOf_commutator_self M,
      Subgroup.relIndex_subgroupOf (Subgroup.commutator_le_self M)]
  rw [hAeq] at hbound
  push_cast at hbound
  have hcast : ((N.relIndex (⁅M, M⁆ : Subgroup G) : ℝ))
      ≤ ((2 * Nat.card ↥W₁ * (centralizerIn U (hallCoreOf M)).relIndex U + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact Nat.cast_le.1 hcast

end CFSG.FeitThompson.Proofs
