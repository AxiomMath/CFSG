module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.TypePFieldInnerComplementOrder
import CFSG.FeitThompson.Local.TypePReducibleInnerActionOrder
import CFSG.FeitThompson.Representations.ActualTypeICrossedControl
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.OddOrder.SmallSideNormBoundException

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem relIndex_hallCoreIn_eq_hallCoreIndex [Finite G] (X : Subgroup G) :
    (_root_.CFSG.FeitThompson.hallCoreIn X).relIndex X = CFSG.FeitThompson.hallCoreIndex X := by
  rw [CFSG.FeitThompson.hallCoreIndex_eq]

theorem indClassFun_principal_eq_indBetween [Finite G] (X : Subgroup G) (inst : Fintype ↥X) :
    @indClassFun ↥X _ (hallCore ↥X) inst (principalClassFun ↥(hallCore ↥X))
      = CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn X) X 1 := by
  refine Eq.symm ((_root_.CFSG.FeitThompson.Proofs.CrossedTypeI.indBetween_hallCoreIn_eq_indClassFun X
    (1 : ↥(_root_.CFSG.FeitThompson.hallCoreIn X) → ℂ)).trans ?_)
  rw [coe_principalClassFun]
  rfl

variable [Fintype G]

theorem coreTau_eq_tauDade (X : Subgroup G) (f : ↥X → ℂ) :
    _root_.CFSG.FeitThompson.coreTau X f = CFSG.FeitThompson.tauDade X f := by
  rw [_root_.CFSG.FeitThompson.coreTau_eq, hallCoreSharp_eq]
  rfl

theorem indFamNonprincipal_eq_calLFam (X : Subgroup G) :
    _root_.CFSG.FeitThompson.indFamNonprincipal X = CFSG.FeitThompson.calLFam X := by
  classical
  rw [_root_.CFSG.FeitThompson.Proofs.CrossedTypeI.calLFam_eq_indFam X,
    _root_.CFSG.FeitThompson.indFamNonprincipal, coe_principalClassFun]

namespace CoreCharData

variable {X : Subgroup G} {ν : (↥X → ℂ) → (G → ℂ)} {φ : ↥X → ℂ} {β : G → ℂ}

theorem isCoherentDade (h : _root_.CFSG.FeitThompson.IsCoreCharData X ν φ β) :
    CFSG.FeitThompson.IsCoherentDade X ν := by
  have hset := indFamNonprincipal_eq_calLFam X
  refine ⟨fun f hf g hg => h.map_add f g (by rwa [hset]) (by rwa [hset]),
    fun f hf => h.mem_virtualChars f (by rwa [hset]), fun f hf g hg => ?_,
    fun f hf hf1 => by rw [h.eq_coreTau f (by rwa [hset]) hf1, coreTau_eq_tauDade]⟩
  have key := h.inner_eq f g (by rwa [hset]) (by rwa [hset])
  have _ : Fintype ↥X := Fintype.ofFinite _
  rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner, CFSG.FeitThompson.cfInnerFin_eq_cfInner]
  refine key.trans ?_
  congr 1
  exact Subsingleton.elim _ _

theorem mem_calLFam (h : _root_.CFSG.FeitThompson.IsCoreCharData X ν φ β) :
    φ ∈ CFSG.FeitThompson.calLFam X := by
  rw [← indFamNonprincipal_eq_calLFam X]; exact h.mem_φ

theorem apply_one (h : _root_.CFSG.FeitThompson.IsCoreCharData X ν φ β) :
    φ 1 = ((CFSG.FeitThompson.hallCoreIndex X : ℕ) : ℂ) := by
  rw [h.φ_apply_one, CFSG.FeitThompson.hallCoreIndex_eq,
    _root_.CFSG.FeitThompson.Proofs.CrossedTypeI.index_hallCore_eq_relIndex]

theorem beta_eq (h : _root_.CFSG.FeitThompson.IsCoreCharData X ν φ β) :
    β = CFSG.FeitThompson.tauDade X (CFSG.FeitThompson.indBetween (CFSG.FeitThompson.hallCoreIn X) X 1 - φ) := by
  rw [h.β_eq, coreTau_eq_tauDade, indClassFun_principal_eq_indBetween X]

end CoreCharData

theorem sub_one_le_mul_of_div_le {v k : ℕ} (hk : 0 < k) (h1 : 1 ≤ v)
    (h : ((v : ℚ) - 1) / (k : ℚ) ≤ (k : ℚ) - 1) : v - 1 ≤ k * (k - 1) := by
  have hk0 : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have h' : ((v : ℚ) - 1) ≤ ((k : ℚ) - 1) * (k : ℚ) := (div_le_iff₀ hk0).1 h
  have hcast : ((v - 1 : ℕ) : ℚ) ≤ ((k * (k - 1) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub h1, Nat.cast_sub hk]
    linarith
  exact_mod_cast hcast

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem natCard_reciprocal_complement (h₂ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₄ : Statements.FNI_type_p_elementary_core_structure.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
    (T V W₁ W₂ : Subgroup G) (hT : IsCoatom T)
    (hcT : IsWitnessedPConfiguration T V W₂ W₁)
    (hqp : Nat.card ↥W₁ < Nat.card ↥W₂) :
    Nat.card ↥V = (Nat.card ↥W₁ ^ Nat.card ↥W₂ - 1) / (Nat.card ↥W₁ - 1) := by
  set q := Nat.card ↥W₁ with hq
  set p := Nat.card ↥W₂ with hp
  obtain ⟨-, hqq, hpp, hoq, hop, hqpne, -, -, -, -, -, -, hmod, hcard, -⟩ :=
    h₄ G hG T V W₂ W₁ hT hcT q p rfl rfl
  have hq3 : 3 ≤ q := hqq.odd_iff.mp hoq
  obtain ⟨Vt, hVadd, hVmod, hdim, ⟨e⟩⟩ := hmod
  have hTnorm : T ≤ normalizer ((hallCoreOf T : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore T
  have hρ := isConjModule_conjLinear q hTnorm e
  have hirr : IsIrreducibleLinear ((V.subgroupOf T).map (conjLinear q hTnorm e)) := by
    by_contra hcon
    rw [IsIrreducibleLinear] at hcon
    push Not at hcon
    obtain ⟨W, hWinv, hWne⟩ := hcon
    obtain ⟨hp3, -⟩ := FNI_type_p_reducible_inner_action_order.{u, u} h₂ h₄ G hG T V W₂ W₁ hT hcT
      q p rfl rfl Vt e (conjLinear q hTnorm e) hρ ⟨W, hWne.1, hWne.2, hWinv⟩
    omega
  obtain ⟨-, -, hfull⟩ := FNI_type_p_field_inner_complement_order.{u, u} h₂ h₄ G hG T V W₂ W₁ hT hcT
    q p ((q ^ p - 1) / (q - 1)) rfl rfl rfl Vt e (conjLinear q hTnorm e) hρ hirr
  exact hfull (fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))

theorem FNI_paired_supporting_crossed_alternatives
    (h₁ : Statements.FCH_actual_type_I_crossed_control.{u})
    (h₂ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₃ : Statements.FNI_paired_supporting_maxima_nonconjugate.{u})
    (h₄ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FNI_paired_supporting_crossed_alternatives.{u} := by
  intro G _ _ hG S T L U V W₁ W₂ y hsetup hIL heL M hM hIM hHM heM νL φL βL hLdata νM φM βM hMdata
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG5 : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  set p := Nat.card ↥W₂ with hp
  set q := Nat.card ↥W₁ with hq
  obtain ⟨-, hpp, hqq, hop, hoq, hpq, -⟩ :=
    h₄ G hG5 S U W₁ W₂ hsetup.isCoatom_S hsetup.config_S p q rfl rfl
  have hqp : q < p := hsetup.natCard_lt
  have hnc : ∀ g : G, L ≠ CFSG.FeitThompson.conjSubgroup M g := by
    intro g
    exact h₃ G hG S T L U V W₁ W₂ y hsetup M hM hHM g
  have heL' : CFSG.FeitThompson.hallCoreIndex L = p * q := by
    rw [← relIndex_hallCoreIn_eq_hallCoreIndex]; exact heL
  have heM' : CFSG.FeitThompson.hallCoreIndex M = p * q := by
    rw [← relIndex_hallCoreIn_eq_hallCoreIndex]; exact heM
  obtain ⟨-, -, hor, hbd₁₂, hbd₂₁⟩ :=
    h₁ G hG2 M L hM hsetup.isCoatom_L hnc hIM hIL
      (Nat.card ↥(CFSG.FeitThompson.hallCoreIn M))
      (Nat.card ↥(CFSG.FeitThompson.hallCoreIn L))
      (CFSG.FeitThompson.hallCoreIndex M)
      (CFSG.FeitThompson.hallCoreIndex L) rfl rfl rfl rfl
      νM (CoreCharData.isCoherentDade hMdata) νL (CoreCharData.isCoherentDade hLdata)
      φM (CoreCharData.mem_calLFam hMdata) (CoreCharData.apply_one hMdata)
      φL (CoreCharData.mem_calLFam hLdata) (CoreCharData.apply_one hLdata)
      βM βL (CoreCharData.beta_eq hMdata) (CoreCharData.beta_eq hLdata)
      _ _ rfl rfl
  rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner,
    CFSG.FeitThompson.cfInnerFin_eq_cfInner] at hor
  rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner] at hbd₁₂
  rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner] at hbd₂₁
  rcases hor with hc | hc
  ·
    refine Or.inl ⟨hc, ?_⟩
    have hbd := hbd₁₂ hc
    rw [heL', heM'] at hbd
    push_cast at hbd
    exact hbd
  ·
    refine Or.inr ⟨hc, ?_⟩
    have hbd := hbd₂₁ hc
    rw [heL', heM'] at hbd
    have hHMV : CFSG.FeitThompson.hallCoreIn M = V := hHM
    rw [hHMV] at hbd
    have hv := natCard_reciprocal_complement h₂ h₄ hG5 T V W₁ W₂ hsetup.isCoatom_T
      hsetup.config_T hqp
    have hk : 0 < p * q := Nat.mul_pos hpp.pos hqq.pos
    have h1 : 1 ≤ Nat.card ↥V := Nat.card_pos
    have hnat := sub_one_le_mul_of_div_le hk h1 hbd
    rw [hv] at hnat
    exact eq_three_and_eq_five_of_sub_one_le_mul hpp hqq hop hoq hqp hnat

end

end CFSG.FeitThompson.Proofs
