module

public import CFSG.GH74.GLS.C3.Layer1.Th2BalGlobal
public import CFSG.GH74.GLS.C3.Layer1.Th2BalRows
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.GLS.Prop27.LocBalFinal

public section

namespace CFSG.GH74.GLS.Th2.Bal

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.Assembly.Dichotomy
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance
open scoped commutatorElement

theorem isLocallyKBalanced_of_locBal2 {K : Type} [Group K] [Finite K] (hc : center K = ⊥)
    (hLB : Prop27.LocBal2 (fun S _ => Nonempty (S ≃* K))) {k : ℕ} (hk : 1 ≤ k) :
    IsLocallyKBalanced k K := by
  classical
  intro H hInn F hFk hF2
  have : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  obtain ⟨Inn, hInnDef⟩ : ∃ Inn : Subgroup (MulAut K), Inn = (MulAut.conj : K →* MulAut K).range :=
    ⟨_, rfl⟩
  have hInnH : Inn ≤ H := hInnDef ▸ hInn
  have hInnN : Inn.Normal := by
    rw [hInnDef]
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨s, rfl⟩ := hn
    exact ⟨g s, (Prop27.mul_conj_mul_inv g s).symm ▸ rfl⟩
  have hNn : (Inn.subgroupOf H).Normal := Subgroup.normal_subgroupOf
  have hiso : Nonempty (↥(Inn.subgroupOf H) ≃* K) := by
    refine ⟨(Subgroup.subgroupOfEquivOfLe hInnH).trans ?_⟩
    rw [hInnDef]
    exact (MonoidHom.ofInjective (Prop27.conj_injective_of_center_bot hc)).symm
  have hcent : centralizer ((Inn.subgroupOf H : Subgroup ↥H) : Set ↥H) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    refine MulEquiv.ext fun s => ?_
    have hconj : ∀ s : K, MulAut.conj s ∈ Inn := fun s => by
      rw [hInnDef]; exact ⟨s, rfl⟩
    have hmem : ∀ s : K, (⟨MulAut.conj s, hInnH (hconj s)⟩ : ↥H) ∈ Inn.subgroupOf H :=
      fun s => hconj s
    have h1 := Subgroup.mem_centralizer_iff.mp hφ _ (hmem s)
    have h2 : (MulAut.conj s) * (φ : MulAut K) = (φ : MulAut K) * MulAut.conj s :=
      congrArg Subtype.val h1
    have h3 : MulAut.conj ((φ : MulAut K) s) = MulAut.conj s := by
      rw [← Prop27.mul_conj_mul_inv, ← h2, mul_assoc, mul_inv_cancel, mul_one]
    have h4 := Prop27.conj_injective_of_center_bot hc h3
    simpa using h4
  obtain ⟨f, hfF, hf1⟩ := exists_ne_one_of_two_pow_le hk hFk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : orderOf f = 2 := orderOf_eq_prime (by rw [sq]; exact hF2 f hfF) hf1
  have hbot := hLB ↥H (Inn.subgroupOf H) hNn hiso hcent f hf2
  have hbot' : involutionOddCore f = ⊥ := (Prop27.involutionOddCore_eq_bot_iff' f).mpr hbot
  exact le_bot_iff.mp ((deltaCore_le_involutionOddCore hfF hf1).trans hbot'.le)

section Component

variable {G : Type} [Group G] [Finite G]

theorem exists_pCompIn_over {a : G} {L : Subgroup (CentralizerBar a)} (hL : IsComponent L) :
    ∃ J : Subgroup G, IsPCompIn 2 (centralizer ({a} : Set G)) J ∧
      (J.subgroupOf (centralizer ({a} : Set G))).map (piBar a) = L := by
  obtain ⟨J₀, hJ₀, hJ₀map⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hL
  have hJsub : (J₀.map (centralizer ({a} : Set G)).subtype).subgroupOf (centralizer ({a} : Set G))
      = J₀ := Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) J₀
  refine ⟨J₀.map (centralizer ({a} : Set G)).subtype,
    ⟨Subgroup.map_subtype_le J₀, by rw [hJsub]; exact hJ₀⟩, by rw [hJsub]; exact hJ₀map⟩

theorem kBar_equiv_of_over {a : G} {J : Subgroup G} {L : Subgroup (CentralizerBar a)}
    (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hLJ : (J.subgroupOf (centralizer ({a} : Set G))).map (piBar a) = L) :
    Nonempty (kBar J ≃* ↥L) := by
  obtain ⟨e⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hJ
  exact ⟨e.trans (MulEquiv.subgroupCongr hLJ)⟩

end Component

end CFSG.GH74.GLS.Th2.Bal

namespace CFSG.GH74.GLS

open CFSG.GH74.GLS.Th2.Bal

@[expose] def B_ivk_10_5 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
    (HasL2Model L Odd ∨ Nonempty (L ≃* alternatingGroup (Fin 7))) →
      IsLocallyKBalanced 3 (L ⧸ Subgroup.center L) ∧
      (¬ IsLocallyKBalanced 2 (L ⧸ Subgroup.center L) →
        Nonempty (L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model L (fun q => Odd q ∧ ¬ IsFM9 q))

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.Bal

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.Prop27
  CFSG.Assembly.Dichotomy
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance
open scoped commutatorElement

theorem component_local
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (h105 : B_ivk_10_5)
    (hL34 : B_gen4_noL34_elem) {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {a : G}
    (ha : orderOf a = 2) {L : Subgroup (CentralizerBar a)} (hL : IsComponent L) :
    IsLocallyKBalanced 3 (↥L ⧸ Subgroup.center ↥L) ∧
      (¬ IsLocallyKBalanced 2 (↥L ⧸ Subgroup.center ↥L) →
        Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model ↥L (fun q => Odd q ∧ ¬ IsFM9 q)) := by
  have hq : CFSG.IsQuasisimple ↥L := hL.1
  have hCU := hG.lt2o.2 a ha L hL
  by_cases hU : InU2 ↥L
  · obtain ⟨J, hJ, hJL⟩ := exists_pCompIn_over hL
    obtain ⟨e⟩ := kBar_equiv_of_over hJ hJL
    have hU' := inU2_of_mulEquiv e.symm hU
    rcases hU'.2 with h | h | ⟨h34, hab, hcard⟩
    · exact h105 ↥L hq (Or.inl (TwoThin.hasL2Model_of_mulEquiv e h))
    · exact h105 ↥L hq (Or.inr (CFSG.GH74.nonempty_alternating_of_mulEquiv e h))
    · exact absurd ⟨h34, hab, hcard⟩ (hL34 G hG.gen4 a J ha hJ)
  · have hC2 : InC2 ↥L := hCU.resolve_right hU
    have hno : ¬ HasL2Model ↥L IsFM9 := by
      rintro ⟨p, f, hp, hf, hfm, hL'⟩
      exact hU ⟨hC2.1, Or.inl ⟨p, f, hp, hf, isFM9_odd hfm, hL'⟩⟩
    have hS : Shapes7 ↥L :=
      shapes7_of_component hGKF hE2 (compData7_of_component hG.gen4 ha hC2 hno) hC2.2.2.1
    have hLB := locBal2_of_shapes7 prop27LocalBalance hS
    have hc : center (↥L ⧸ center ↥L) = ⊥ := center_quotient_eq_bot hq
    exact ⟨isLocallyKBalanced_of_locBal2 hc hLB (by norm_num),
      fun hnot => absurd (isLocallyKBalanced_of_locBal2 hc hLB (by norm_num)) hnot⟩

end CFSG.GH74.GLS.Th2.Bal

namespace CFSG.GH74.GLS

theorem b_prop61a_of
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (hL34 : B_gen4_noL34_elem)
    (h105 : B_ivk_10_5) : B_prop61a := by
  intro G _ _ hG B hB
  exact Th2.Bal.isKBal_of_local (k := 3) (by norm_num)
    (fun a ha L hL => (Th2.Bal.component_local hGKF hE2 h105 hL34 hG ha hL).1) hB.2.1

theorem b_prop61b_unb_of
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (hL34 : B_gen4_noL34_elem)
    (h105 : B_ivk_10_5) : B_prop61b_unb := by
  intro G _ _ hG B hB hnot
  obtain ⟨a, d, J, haB, hdB, ha1, hd1, hunb, L, hL, hLJ, hnb⟩ :=
    Th2.Bal.exists_unbalancing_of_not_weak hB.2.1 hnot
  have ha2 : orderOf a = 2 := hunb.1.1
  obtain ⟨-, h2⟩ := Th2.Bal.component_local hGKF hE2 h105 hL34 hG ha2 hL
  obtain ⟨e⟩ := Th2.Bal.kBar_equiv_of_over hunb.1.2 hLJ.symm
  refine ⟨a, d, J, haB, hdB, hunb, ?_⟩
  rcases h2 hnb with ⟨⟨e'⟩⟩ | h
  · exact Or.inl ⟨e.trans e'⟩
  · exact Or.inr (TwoThin.hasL2Model_of_mulEquiv e.symm h)

end CFSG.GH74.GLS
