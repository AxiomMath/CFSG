module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2NormalSub
public import CFSG.Sporadic.Co2Schreier.Centralizers
public import CFSG.Sporadic.Co2Schreier.QMod
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtraspecialAb

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed
open scoped commutatorElement


abbrev locZsub : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.zpowers locZ

abbrev qcHom : locQ.subgroupOf locC →* Equiv.Perm (Fin 2300) :=
  locC.subtype.comp (locQ.subgroupOf locC).subtype

theorem qcHom_apply (x : locQ.subgroupOf locC) :
    qcHom x = ((x : locC) : Equiv.Perm (Fin 2300)) := rfl

theorem qcHom_zQc : qcHom zQc = locZ := rfl

theorem mem_locZsub_of_mem_center {x : locQ.subgroupOf locC}
    (hx : x ∈ Subgroup.center (locQ.subgroupOf locC)) :
    ((x : locC) : Equiv.Perm (Fin 2300)) ∈ locZsub := by
  rw [center_qc] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← qcHom_apply, map_zpow, qcHom_zQc]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers locZ) k

theorem locZsub_le_Q : locZsub ≤ locQ := by
  rw [Subgroup.zpowers_le]
  exact locZ_mem_Q

theorem locQ_le_centralizer_Z : ∀ q ∈ locQ, locZ * q = q * locZ := by
  intro q hq
  have hqC : q ∈ locC := locQ_le_C hq
  rw [locC_eq_centralizer] at hqC
  exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hqC).2).symm

theorem locZ_commutes_C : ∀ c ∈ locC, c * locZ * c⁻¹ = locZ := by
  intro c hc
  have hcC : c ∈ locC := hc
  rw [locC_eq_centralizer] at hcC
  have := (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hcC).2)
  rw [this]
  group

theorem span_image_eq {S : Set (locQ.subgroupOf locC)} (h1 : (1 : locQ.subgroupOf locC) ∈ S)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) {w : QV}
    (hw : w ∈ Submodule.span (ZMod 2) (qπ '' S)) : ∃ s ∈ S, w = qπ s := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, hs, rfl⟩ := hw
    exact ⟨s, hs, rfl⟩
  | zero => exact ⟨1, h1, qπ_one.symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨t, ht, rfl⟩ := hb
    exact ⟨s * t, hmul s hs t ht, (qπ_mul s t).symm⟩
  | smul c a _ ha =>
    obtain ⟨s, hs, rfl⟩ := ha
    have hc : c = 0 ∨ c = 1 := by
      revert c
      decide
    rcases hc with rfl | rfl
    · exact ⟨1, h1, by simp [qπ_one]⟩
    · exact ⟨s, hs, by simp⟩

theorem hirr_of_qmod (M : Subgroup (Equiv.Perm (Fin 2300))) (hZM : locZsub ≤ M) (hMQ : M ≤ locQ)
    (hMn : ∀ c ∈ locC, ∀ m ∈ M, c * m * c⁻¹ ∈ M) : M = locZsub ∨ M = locQ := by
  set L : Set (locQ.subgroupOf locC) := {x | ((x : locC) : Equiv.Perm (Fin 2300)) ∈ M} with hL
  have hL1 : (1 : locQ.subgroupOf locC) ∈ L := M.one_mem
  have hLmul : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L := fun x hx y hy => M.mul_mem hx hy
  set W : Submodule (ZMod 2) QV := Submodule.span (ZMod 2) (qπ '' L) with hW
  have hinv : ∀ g : locC, ((g : locC) : Equiv.Perm (Fin 2300)) ∈ locC → ∀ w ∈ W,
      conjEnd (Q := locQ.subgroupOf locC) g w ∈ W := by
    intro g _ w hw
    have hle : W ≤ W.comap (conjEnd (Q := locQ.subgroupOf locC) g) := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, conjEnd_qπ]
      refine Submodule.subset_span ⟨MulAut.conjNormal g x, ?_, rfl⟩
      show ((((MulAut.conjNormal g x : locQ.subgroupOf locC) : locC)) :
        Equiv.Perm (Fin 2300)) ∈ M
      rw [coe_conjNormal_qc]
      exact hMn _ g.2 _ hx
    exact hle hw
  have hcl := qmod_irreducible W (hinv (cGen 0) (cGen 0).2) (hinv (cGen 1) (cGen 1).2)
  rcases hcl with hbot | htop
  · left
    refine le_antisymm (fun m hm => ?_) hZM
    have hmL : toQc m (hMQ hm) ∈ L := hm
    have : qπ (toQc m (hMQ hm)) ∈ W := Submodule.subset_span ⟨_, hmL, rfl⟩
    rw [hbot, Submodule.mem_bot, qπ_eq_zero_iff] at this
    exact mem_locZsub_of_mem_center this
  · right
    refine le_antisymm hMQ (fun q hq => ?_)
    have hqW : qπ (toQc q hq) ∈ W := by rw [htop]; trivial
    obtain ⟨x, hx, hxq⟩ := span_image_eq hL1 hLmul hqW
    have h0 : qπ (toQc q hq * x⁻¹) = 0 := by rw [qπ_mul, qπ_inv, ← hxq]; simp
    have hc := mem_locZsub_of_mem_center ((qπ_eq_zero_iff _).1 h0)
    have hc' : q * (((x : locC) : Equiv.Perm (Fin 2300))⁻¹) ∈ M := hZM hc
    have hx' : ((x : locC) : Equiv.Perm (Fin 2300)) ∈ M := hx
    have := M.mul_mem hc' hx'
    simpa using this

theorem locQ_conj (c : Equiv.Perm (Fin 2300)) (hc : c ∈ locC) (q : Equiv.Perm (Fin 2300))
    (hq : q ∈ locQ) : c * q * c⁻¹ ∈ locQ := by
  have h := ((inferInstance : (locQ.subgroupOf locC).Normal).conj_mem (toQc q hq)
    (Subgroup.mem_subgroupOf.2 hq) ⟨c, hc⟩)
  exact Subgroup.mem_subgroupOf.1 h

theorem simple_quot_sub (K : Subgroup (Equiv.Perm (Fin 2300))) (hQK : locQ ≤ K) (hKC : K ≤ locC)
    (hKn : ∀ c ∈ locC, ∀ k ∈ K, c * k * c⁻¹ ∈ K) : K = locQ ∨ K = locC := by
  have hs := isSimpleGroup_quotCQ
  set Q' := locQ.subgroupOf locC with hQ'
  set K' := K.subgroupOf locC with hK'
  have hKn' : K'.Normal := ⟨fun k hk g => by
    have := hKn g.1 g.2 k.1 (Subgroup.mem_subgroupOf.1 hk)
    exact Subgroup.mem_subgroupOf.2 (by simpa using this)⟩
  have hmap : (K'.map (QuotientGroup.mk' Q')).Normal :=
    hKn'.map _ (QuotientGroup.mk'_surjective Q')
  rcases hs.eq_bot_or_eq_top_of_normal (K'.map (QuotientGroup.mk' Q')) with hbot | htop
  · left
    refine le_antisymm (fun k hk => ?_) hQK
    have hkC : k ∈ locC := hKC hk
    have hk' : (⟨k, hkC⟩ : locC) ∈ K' := hk
    have : QuotientGroup.mk' Q' ⟨k, hkC⟩ ∈ K'.map (QuotientGroup.mk' Q') := ⟨_, hk', rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact Subgroup.mem_subgroupOf.1 this
  · right
    refine le_antisymm hKC (fun x hx => ?_)
    have : QuotientGroup.mk' Q' ⟨x, hx⟩ ∈ K'.map (QuotientGroup.mk' Q') := by rw [htop]; trivial
    obtain ⟨k, hk, hkx⟩ := this
    have hq : k⁻¹ * ⟨x, hx⟩ ∈ Q' := QuotientGroup.eq.1 hkx
    have hq' : k⁻¹ * ⟨x, hx⟩ ∈ K' := by
      rw [hK', Subgroup.mem_subgroupOf]
      exact hQK (Subgroup.mem_subgroupOf.1 hq)
    have hxk : (⟨x, hx⟩ : locC) = k * (k⁻¹ * ⟨x, hx⟩) := by group
    have : (⟨x, hx⟩ : locC) ∈ K' := by rw [hxk]; exact K'.mul_mem hk hq'
    exact Subgroup.mem_subgroupOf.1 this

theorem eq_one_or_locZ {y : Equiv.Perm (Fin 2300)} (hy : y ∈ locZsub) : y = 1 ∨ y = locZ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : locZ ^ (2 : ℤ) = 1 := by
    have := locZ_sq
    simpa using this
  have hk : locZ ^ k = locZ ^ (k % 2) := by
    have hk' : k = 2 * (k / 2) + k % 2 := by omega
    calc locZ ^ k = locZ ^ (2 * (k / 2) + k % 2) := by rw [← hk']
      _ = locZ ^ (k % 2) := by rw [zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rw [hk]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem locZ_central_Q : ∀ z ∈ locZsub, ∀ q ∈ locQ, z * q = q * z := by
  intro z hz q hq
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact (Commute.zpow_left (show Commute locZ q from locQ_le_centralizer_Z q hq) k).eq

theorem locZ_normal_C : ∀ c ∈ locC, ∀ z ∈ locZsub, c * z * c⁻¹ ∈ locZsub := by
  intro c hc z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [← conj_zpow, locZ_commutes_C c hc]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers locZ) k

theorem locZsub_ne_bot : locZsub ≠ ⊥ := by
  intro h
  exact locZ_ne_one (Subgroup.zpowers_eq_bot.1 h)

theorem locQ_comm_mem : ∀ a ∈ locQ, ∀ b ∈ locQ, a * b * a⁻¹ * b⁻¹ ∈ locZsub := by
  intro a ha b hb
  have h := commutator_qc_le (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top (toQc a ha)) (Subgroup.mem_top (toQc b hb)))
  exact mem_locZsub_of_mem_center h

theorem locZ_mem_closure_comm : ∀ z ∈ locZsub, z ∈ Subgroup.closure (commSet locQ) := by
  intro z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  refine Subgroup.zpow_mem _ ?_ k
  have h1 : zQc ∈ commutator (locQ.subgroupOf locC) := by
    rw [commutator_qc]
    exact zQc_mem_center
  rw [commutator_eq_closure] at h1
  have h2 : qcHom zQc ∈ (Subgroup.closure (commutatorSet (locQ.subgroupOf locC))).map qcHom :=
    Subgroup.mem_map_of_mem _ h1
  rw [MonoidHom.map_closure, qcHom_zQc] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨x, y, rfl⟩, rfl⟩
  refine ⟨qcHom x, ?_, qcHom y, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.1 x.2
  · exact Subgroup.mem_subgroupOf.1 y.2
  · rw [map_commutatorElement]
    rfl

theorem locC_normal_le_or_eq {N : Subgroup (Equiv.Perm (Fin 2300))} (hNC : N ≤ locC)
    (hNn : ∀ c ∈ locC, ∀ n ∈ N, c * n * c⁻¹ ∈ N) : N ≤ locQ ∨ N = locC :=
  normal_le_or_eq locQ_le_C locQ_conj simple_quot_sub locZsub_le_Q locZ_central_Q locZ_normal_C
    locZsub_ne_bot locQ_comm_mem locZ_mem_closure_comm hirr_of_qmod hNC hNn

theorem card_locQ : Nat.card locQ = 512 := by
  rw [← card_qc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe locQ_le_C).toEquiv]

theorem locQ_center_mem {w : Equiv.Perm (Fin 2300)} (hw : w ∈ locQ)
    (h : ∀ q ∈ locQ, q * w = w * q) : w = 1 ∨ w = locZ := by
  refine eq_one_or_locZ (mem_locZsub_of_mem_center (x := toQc w hw) ?_)
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact h _ (Subgroup.mem_subgroupOf.1 x.2)

theorem locQ_abelian_le {A : Subgroup (Equiv.Perm (Fin 2300))} (hAQ : A ≤ locQ)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ 32 :=
  CFSG.Quasithin.D4Hex.card_abelian_le_32 (z := locZ) card_locQ
    (fun x hx y hy => eq_one_or_locZ (locQ_comm_mem x hx y hy)) (fun _ hw h => locQ_center_mem hw h)
    hAQ hA

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2
