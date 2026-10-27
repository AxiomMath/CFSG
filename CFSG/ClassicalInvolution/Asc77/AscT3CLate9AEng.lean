module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate8AEng
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20G.late_W_le_N_K (d : Std20G K K' J S R R' W V z t) :
    W ≤ Subgroup.normalizer (K : Set G) := by
  conv_lhs => rw [d.late_hW]
  have h := d.late_JW_le_N_K d.late_JW
  exact sup_le (inf_le_right.trans Subgroup.le_normalizer) (fun x hx => h ⟨hx.2, hx.1⟩)

theorem Std20G.late_W_le_N_K' (d : Std20G K K' J S R R' W V z t) :
    W ≤ Subgroup.normalizer (K' : Set G) := by
  conv_lhs => rw [d.late_hW]
  have h := d.late_JW_le_N_K' d.late_JW
  refine sup_le ?_ (fun x hx => h ⟨hx.2, hx.1⟩)
  exact inf_le_right.trans (Sec6Gen.le_normalizer_of_twin d.late_hΩ d.late_mem_K d.late_mem_K'
    d.ne.symm d.viol.hzK d.late_hzK')

theorem Std20G.late_V_le_N_RR' (d : Std20G K K' J S R R' W V z t) :
    V ≤ Subgroup.normalizer ((R ⊔ R' : Subgroup G) : Set G) := by
  intro v hv
  have h1 : v ∈ Subgroup.normalizer (R : Set G) := by
    rw [d.late_R_eq]
    exact late_mem_normalizer_infE ((d.hVW.trans d.late_W_le_N_K) hv)
      (Subgroup.le_normalizer (d.hVS hv))
  have h2 : v ∈ Subgroup.normalizer (R' : Set G) := by
    rw [d.late_R'_eq]
    exact late_mem_normalizer_infE ((d.hVW.trans d.late_W_le_N_K') hv)
      (Subgroup.le_normalizer (d.hVS hv))
  exact late_mem_normalizer_supE h1 h2

theorem Std20G.late_P_inv' (d : Std20G K K' J S R R' W V z t)
    (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J)) {x : G} (hxS : x ∈ (S : Subgroup G)) :
    conjSub x (R ⊔ R' ⊔ (J ⊓ W)) = R ⊔ R' ⊔ (J ⊓ W) := by
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) := d.hSz hxS
  have hxS' : conjSub x (S : Subgroup G) = S := conjSub_eq_self_of_mem hxS
  have hxW : conjSub x W = W := mem_normalizer_iff_conjSub_eq.mp (d.hWN hxS)
  have hRle : conjSub x R ≤ R ⊔ R' := by
    rw [d.late_R_eq, late_conjSub_infE, hxS']
    rcases d.late_conj_K hxz with h | h
    · rw [h, ← d.late_R_eq]
      exact le_sup_left
    · rw [h, ← d.late_R'_eq]
      exact le_sup_right
  have hR'le : conjSub x R' ≤ R ⊔ R' := by
    rw [d.late_R'_eq, late_conjSub_infE, hxS']
    rcases d.late_conj_K' hxz with h | h
    · rw [h, ← d.late_R_eq]
      exact le_sup_left
    · rw [h, ← d.late_R'_eq]
      exact le_sup_right
  have hWP : W ≤ R ⊔ R' ⊔ (J ⊓ W) := by
    conv_lhs => rw [hWeq]
    refine sup_le ?_ ?_
    · have : W ⊓ K ≤ R := by
        rw [d.late_R_eq]
        exact le_inf inf_le_right (inf_le_left.trans d.hWS)
      exact this.trans (le_sup_left.trans le_sup_left)
    · rw [inf_comm]
      exact le_sup_right
  have hle : conjSub x (R ⊔ R' ⊔ (J ⊓ W)) ≤ R ⊔ R' ⊔ (J ⊓ W) := by
    rw [late_conjSub_supE, late_conjSub_supE]
    refine sup_le (sup_le (hRle.trans le_sup_left) (hR'le.trans le_sup_left)) ?_
    refine le_trans ?_ hWP
    calc conjSub x (J ⊓ W) ≤ conjSub x W := conjSub_mono inf_le_right
      _ = W := hxW
  exact late_conjSub_eq_of_leE hle le_rfl

theorem Std20G.late_98_iff (d : Std20G K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J))
    {X : Subgroup G} (hX2 : IsPGroup 2 X) (hXS : X ≤ (S : Subgroup G))
    (hXt : ∀ x ∈ X, x * t = t * x) :
    (∀ x ∈ X, conjSub x K = K) ↔ (∀ x ∈ X, conjSub x J = J) := by
  have hXc : X ≤ Subgroup.centralizer ({z, t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | hh
    · have := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz (hXS hx))
      exact this.symm
    · rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hXt x hx).symm
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) := by
    obtain ⟨-, h4⟩ := d.late_JW_data hJW
    have := Subgroup.card_le_of_le (inf_le_inf_left J d.hWS : J ⊓ W ≤ J ⊓ (S : Subgroup G))
    omega
  exact (Sec7.l9_8GenS G (CoreAssembly.conjClass K) d.late_hΩ K d.late_mem_K J d.late_mem_J
    d.late_inA z t d.viol.hzK d.viol.hzJ K' d.late_mem_K' d.ne d.twins X hX2 hXc
    (R ⊔ R' ⊔ (J ⊓ W)) (d.late_isSylow2In_P hJW)
    (fun x hx => d.late_P_inv' hWeq (hXS hx)) S
    (sup_le d.late_P_le_S hXS) hJS W d.hW d.hWS).1

theorem Std20G.late_SX (d : Std20G K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z) :
    (S : Subgroup G) ⊓ sec20X (CoreAssembly.conjClass K) z K K' = R ⊔ R' ⊔ V := by
  have hVK : V ≤ Subgroup.normalizer (K : Set G) := d.hVW.trans d.late_W_le_N_K
  have hVK' : V ≤ Subgroup.normalizer (K' : Set G) := d.hVW.trans d.late_W_le_N_K'
  have hCN : V ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
    fun v hv => late_mem_normalizer_supE (hVK hv) (hVK' hv)
  have hV2 : IsPGroup 2 ↥V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have hVsyl : IsSylow2In V V := ⟨le_rfl, hV2, fun V' hV' _ hle => le_antisymm hV' hle⟩
  have hVN : V ⊓ (K ⊔ K') ≤ R ⊔ R' := by
    rw [← d.late_S_inf_sup]
    exact le_inf (inf_le_left.trans d.hVS) inf_le_right
  have hP₁ : IsSylow2In (R ⊔ R' ⊔ V) ((K ⊔ K') ⊔ V) :=
    Sec7.isSylow2In_sup_of_sylow hCN d.late_isSylow2In_RR' hVsyl d.late_V_le_N_RR' hVN
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  have hXeq : X = oddCoreOf X ⊔ ((K ⊔ K') ⊔ V) := by
    rw [sup_comm (K ⊔ K') V]
    exact c3
  have hCX : (K ⊔ K') ⊔ V ≤ X := by
    conv_rhs => rw [hXeq]
    exact le_sup_right
  have hOd : Odd (Nat.card ↥(oddCoreOf X)) := oddCoreOf_odd_natCard X
  have hbot : IsSylow2In (⊥ : Subgroup G) (oddCoreOf X) := by
    refine ⟨bot_le, IsPGroup.of_bot, fun V' hV' hV'2 _ => ?_⟩
    refine le_antisymm (fun x hx => ?_) bot_le
    have h1 : x = 1 := eq_one_of_isPGroup_of_mem_odd hOd (hV' hx) (hV'2.to_le
      (Subgroup.zpowers_le.mpr hx))
    rw [h1]
    exact Subgroup.one_mem _
  have hCN₂ : (K ⊔ K') ⊔ V ≤ Subgroup.normalizer (oddCoreOf X : Set G) :=
    hCX.trans fun g hg => Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer
      (Subgroup.le_normalizer hg)
  have hVN₂ : (R ⊔ R' ⊔ V) ⊓ oddCoreOf X ≤ ⊥ := by
    intro x hx
    rw [Subgroup.mem_bot]
    exact eq_one_of_isPGroup_of_mem_odd hOd hx.2 (hP₁.2.1.to_le (Subgroup.zpowers_le.mpr hx.1))
  have hP₂ : IsSylow2In (⊥ ⊔ (R ⊔ R' ⊔ V)) (oddCoreOf X ⊔ ((K ⊔ K') ⊔ V)) :=
    Sec7.isSylow2In_sup_of_sylow hCN₂ hbot hP₁
      (fun g _ => mem_normalizer_iff_conjSub_eq.mpr (by unfold conjSub; exact Subgroup.map_bot _))
      hVN₂
  rw [bot_sup_eq, ← hXeq] at hP₂
  have hle : R ⊔ R' ⊔ V ≤ (S : Subgroup G) ⊓ X :=
    le_inf (sup_le (sup_le d.hRS d.hR'S) d.hVS) hP₂.1
  exact hP₂.2.2 _ inf_le_right (S.isPGroup'.to_le inf_le_left) hle

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
