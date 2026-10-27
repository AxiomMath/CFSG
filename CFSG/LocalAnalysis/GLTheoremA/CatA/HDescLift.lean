module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bLoc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLiftGood
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_StructAct
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section KLevel

variable {Y : Type} [Group Y] [Finite Y]

theorem le_normalizer_of_normal {K B : Subgroup Y} (hK : K.Normal) :
    B ≤ Subgroup.normalizer (K : Set Y) := fun g _ => by
  rw [Subgroup.normalizer_eq_top_iff.2 hK]
  exact Subgroup.mem_top g

theorem isKGroup_of_le (hY : CFSG.Open.IsKGroup Y) (H : Subgroup Y) : CFSG.Open.IsKGroup ↥H :=
  CFSG.KCore.KGroupNonab.subgroup CFSG.Assembly.inCatalog_isoInvariant hY H

theorem exists_stable_two_subgroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup Y}
    (h : KHyp p K B) (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S) :
    ∃ T' : Subgroup S, IsPGroup 2 T' ∧ T' ≠ ⊥ ∧
      ∀ α ∈ (kd264Rho hBN e).range, T'.map α.toMonoidHom = T' := by
  obtain ⟨T, hTK, hT2, hTne, hBT⟩ := h.twogrp
  let πK : ↥K →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hπ : ∀ (b : ↥B) (k : ↥K),
      (kd264Rho hBN e b) (πK k) = πK (CFSG.normalizerConjAutOfMem K B hBN b k) := by
    intro b k
    have h1 := CFSG.normalizerConjAutOfMem_comp_mk K B hBN b k
    show (MulAut.congr e (CFSG.normalizerToCenterQuotientAut K B hBN b))
        (e (QuotientGroup.mk' (Subgroup.center ↥K) k)) =
      e (QuotientGroup.mk' (Subgroup.center ↥K) (CFSG.normalizerConjAutOfMem K B hBN b k))
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [← h1]
  have hconj : ∀ (b : ↥B) (k : ↥K), ((CFSG.normalizerConjAutOfMem K B hBN b k : ↥K) : Y) =
      (b : Y) * (k : Y) * (b : Y)⁻¹ := by
    intro b k
    simp [CFSG.normalizerConjAutOfMem]
  set T' : Subgroup S := (T.subgroupOf K).map πK with hT'
  have hstab : ∀ b : ↥B, T'.map (kd264Rho hBN e b).toMonoidHom ≤ T' := by
    intro b
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    show (kd264Rho hBN e b) (πK k) ∈ T'
    rw [hπ]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
    rw [hconj]
    have hkT : (k : Y) ∈ T := Subgroup.mem_subgroupOf.1 hk
    exact (Subgroup.mem_normalizer_iff.1 (hBT b.2) (k : Y)).1 hkT
  refine ⟨T', (hT2.comap_subtype).map πK, ?_, ?_⟩
  · obtain ⟨t, htT, ht2⟩ := exists_orderOf_two_of_isPGroup hT2 hTne
    have hk2 : orderOf (⟨t, hTK htT⟩ : ↥K) = 2 := by
      rw [← ht2, ← Subgroup.orderOf_coe]
    have hkc := not_mem_center_of_orderOf_two hp hp2 h hk2
    intro hbot
    have hmem : πK ⟨t, hTK htT⟩ ∈ T' :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 htT)
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hkc
    have h1 : e (QuotientGroup.mk ⟨t, hTK htT⟩) = 1 := hmem
    rw [← map_one e] at h1
    exact (QuotientGroup.eq_one_iff _).1 (e.injective h1)
  · rintro _ ⟨b, rfl⟩
    refine le_antisymm (hstab b) ?_
    intro x hx
    have hx' : (kd264Rho hBN e b⁻¹) x ∈ T' := hstab b⁻¹ ⟨x, hx, rfl⟩
    refine ⟨(kd264Rho hBN e b⁻¹) x, hx', ?_⟩
    show (kd264Rho hBN e b) ((kd264Rho hBN e b⁻¹) x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem isElemAbelian_range {p : ℕ} {K B : Subgroup Y} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S) : IsElemAbelian p (kd264Rho hBN e).range := by
  have hT : IsElemAbelian p (⊤ : Subgroup ↥B) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.isElemAbelian_top_of hB
  have hmap := CFSG.SectionRank.isElemAbelian_map hT (kd264Rho hBN e)
  rwa [← MonoidHom.range_eq_map] at hmap

theorem card_range_ge {p : ℕ} (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3) :
    p ^ 2 ≤ Nat.card (kd264Rho hBN e).range ∧
      ∃ c : ℕ, c ≤ 2 ∧ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = p ^ c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr h.qs.1
  have hmul := card_range_kd264Rho_mul hperf hBN e
  obtain ⟨c, hcc⟩ := exists_card_eq_pow_of_isElemAbelian hp
    (isElemAbelian_mono h.elem (inf_le_left : B ⊓ Subgroup.centralizer (K : Set Y) ≤ B))
  have hc2 : c ≤ 2 := by
    by_contra hc3
    push Not at hc3
    have : p ^ 3 ≤ p ^ c := Nat.pow_le_pow_right hp.pos hc3
    omega
  refine ⟨?_, c, hc2, hcc⟩
  have h4 := h.card
  rw [← hmul, hcc] at h4
  have : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card (kd264Rho hBN e).range :=
    calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
      _ ≤ Nat.card (kd264Rho hBN e).range * p ^ c := h4
      _ ≤ Nat.card (kd264Rho hBN e).range * p ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.pos hc2)
      _ = p ^ 2 * Nat.card (kd264Rho hBN e).range := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left this (pow_pos hp.pos 2)

theorem iInf_fixSubgroup_zpowers {S : Type} [Group S] (α : MulAut S) :
    (⨅ f ∈ Subgroup.zpowers α, fixSubgroup f) = fixSubgroup α := by
  refine le_antisymm (iInf₂_le α (Subgroup.mem_zpowers α)) (le_iInf₂ fun f hf x hx => ?_)
  have hx' : α ∈ MulAction.stabilizer (MulAut S) x := hx
  have : Subgroup.zpowers α ≤ MulAction.stabilizer (MulAut S) x := Subgroup.zpowers_le.2 hx'
  exact this hf

theorem kConcl_of_good_element_of_cTwo {p : ℕ} (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S] [Finite S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S)
    (hCcard : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = p ^ 2) {α : MulAut S}
    (hαA : α ∈ (kd264Rho hBN e).range) (hαp : orderOf α = p)
    (hgood : GLAPLayer p (fixSubgroup α) ≠ ⊥) : KConcl p K B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr h.qs.1
  set F : Subgroup (MulAut S) := Subgroup.zpowers α with hF
  have hFA : F ≤ (kd264Rho hBN e).range := Subgroup.zpowers_le.2 hαA
  have hFcard : Nat.card F = p := by rw [hF, Nat.card_zpowers, hαp]
  have hFgood : IsGood p F := by
    unfold IsGood
    rw [hF, iInf_fixSubgroup_zpowers]
    exact hgood
  set Ft : Subgroup Y := (F.comap (kd264Rho hBN e)).map B.subtype with hFt
  have hker : Nat.card (kd264Rho hBN e).ker =
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
    rw [ker_kd264Rho hperf hBN]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := B ⊓ Subgroup.centralizer (K : Set Y))
        (K := B) inf_le_left).toEquiv
  have hcomp : Nat.card (F.comap (kd264Rho hBN e)) =
      Nat.card F * Nat.card (kd264Rho hBN e).ker := by
    have h' := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker
      (kd264Rho hBN e) (F.comap (kd264Rho hBN e))
    rw [Subgroup.map_comap_eq_self hFA,
      inf_eq_right.mpr (Subgroup.ker_le_comap (f := kd264Rho hBN e) F)] at h'
    exact h'
  have hFtcard : Nat.card Ft = p ^ 3 := by
    calc Nat.card Ft = Nat.card (F.comap (kd264Rho hBN e)) :=
        Subgroup.card_map_of_injective B.subtype_injective
      _ = Nat.card F * Nat.card (kd264Rho hBN e).ker := hcomp
      _ = p * p ^ 2 := by rw [hFcard, hker, hCcard]
      _ = p ^ 3 := by ring
  have hFtB : Ft ≤ B := Subgroup.map_subtype_le _
  exact ⟨Ft, hFtB, isElemAbelian_mono h.elem hFtB, hFtcard,
    kd264LiftGood_holds hp Y K B hBN S e F hFA hFgood⟩

theorem kConcl_of_good_element {p : ℕ} (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S] [Finite S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3) {α : MulAut S}
    (hαA : α ∈ (kd264Rho hBN e).range) (hαp : orderOf α = p)
    (hAcard : Nat.card (kd264Rho hBN e).range = p ^ 2)
    (hgood : GLAPLayer p (fixSubgroup α) ≠ ⊥) : KConcl p K B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, c, hc2, hcc⟩ := card_range_ge hp h hBN e hc
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr h.qs.1
  have hmul := card_range_kd264Rho_mul hperf hBN e
  have hCcard : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = p ^ 2 := by
    have h4 := h.card
    rw [← hmul, hAcard] at h4
    have h5 : p ^ 2 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
      have : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) :=
        calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
          _ ≤ p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := h4
      exact Nat.le_of_mul_le_mul_left this (pow_pos hp.pos 2)
    have h6 : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) ≤ p ^ 2 := by
      rw [hcc]
      exact Nat.pow_le_pow_right hp.pos hc2
    exact le_antisymm h6 h5
  exact kConcl_of_good_element_of_cTwo hp h hBN e hCcard hαA hαp hgood

end KLevel

end CFSG.LocalAnalysis.GLTheoremA.HDesc
