module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCNSC
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqWDefs
import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open Subgroup

theorem uniqCheckW_of_parts {N : ℕ} {commB : ℕ → ℕ → Bool} {conjB : ℕ → ℕ → ℕ → Bool}
    {invB : ℕ → Bool} {W : UniqWit} (h₁ : (List.range W.J).all (clsPartW N commB conjB W) = true)
    (h₂ : ∀ j < W.J, ∀ i < N, dRowW commB W j i = true)
    (h₄ : ∀ j < W.J, ∀ t < 128, dPairW commB W j t = true)
    (h₃ : ((List.range N).filter fun i => invB i && decide (2 ≤ W.kind (W.cl i))).length < 63) :
    uniqCheckW N commB conjB invB W = true := by
  simp only [uniqCheckW, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨fun j hj => ?_, h₃⟩
  have hp := (List.all_eq_true.1 h₁) j (List.mem_range.2 hj)
  simp only [clsPartW, clsOKW, Bool.and_eq_true] at hp ⊢
  refine ⟨hp.1, ?_⟩
  by_cases h0 : W.kind j = 0
  · simpa only [ite_eq_left h0] using hp.2
  by_cases h1 : W.kind j = 1
  · simp only [ite_eq_right h0, ite_eq_left h1, Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
    obtain ⟨⟨⟨hN, hlen⟩, hsort⟩, hc0⟩ := hp.2
    refine ⟨⟨⟨⟨List.all_eq_true.2 fun i hi => ?_, hN⟩, List.all_eq_true.2 fun a ha => ?_⟩,
      hsort⟩, hc0⟩
    · have hr := h₂ j hj i (List.mem_range.1 hi)
      simpa [dRowW, h1] using hr
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
      have hr := h₄ j hj t (by omega)
      simp only [dPairW, h1, decide_true, Bool.not_true, Bool.false_or, ht] at hr
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] at hr
  · simp only [ite_eq_right h0, ite_eq_right h1] at hp ⊢

variable {G : Type*} [Group G] {S : Subgroup G} {N : ℕ} {e : ℕ → G}
  {commB : ℕ → ℕ → Bool} {conjB : ℕ → ℕ → ℕ → Bool} {invB : ℕ → Bool} {W : UniqWit}

theorem mem_iff_of_uniqCheckW (he : ∀ i < N, e i ∈ S) (hsurj : ∀ g ∈ S, ∃ i < N, e i = g)
    (hinj : ∀ i < N, ∀ k < N, e i = e k → i = k)
    (hcomm : ∀ i < N, ∀ k < N, commB i k = true ↔ e i * e k = e k * e i)
    (hconj : ∀ c < N, ∀ a < N, ∀ w < N, conjB c a w = true → e c * e a = e w * e c)
    (hinv : ∀ i < N, e i * e i = 1 → e i ≠ 1 → invB i = true)
    (hcls : ∀ i < N, invB i = true → W.cl i < W.J ∧ ∃ c < N, e c * e (W.y (W.cl i)) = e i * e c)
    (h : uniqCheckW N commB conjB invB W = true) {F : Subgroup G} (hF : IsNSC S F 64)
    (g : G) : g ∈ F ↔ ∃ i ∈ W.c0, e i = g := by
  classical
  simp only [uniqCheckW, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hcl, hcount⟩ := h
  obtain ⟨i, hi, hiF, hkind⟩ : ∃ i < N, e i ∈ F ∧ invB i = true ∧ W.kind (W.cl i) < 2 := by
    by_contra hno
    push Not at hno
    set L := (List.range N).filter fun i => invB i && decide (2 ≤ W.kind (W.cl i)) with hL
    have hsub : (F : Set G) ⊆ ↑(insert 1 ((L.map e).toFinset)) := by
      intro f hf
      by_cases h1 : f = 1
      · simp [h1]
      · obtain ⟨i, hi, rfl⟩ := hsurj f (hF.le hf)
        have hinvi := hinv i hi (hF.mul_self _ hf) h1
        have h2 := hno i hi hf hinvi
        simp only [Finset.coe_insert, List.coe_toFinset, Set.mem_insert_iff, Set.mem_ofPred_eq,
          List.mem_map, hL, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
        exact Or.inr ⟨i, ⟨hi, hinvi, h2⟩, rfl⟩
    have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at hle
    have h1 : Nat.card F = (F : Set G).ncard := Nat.card_coe_set_eq _
    have h2 := Finset.card_insert_le 1 (L.map e).toFinset
    have h3 := List.toFinset_card_le (L.map e)
    rw [List.length_map] at h3
    have h4 := hF.card_eq
    omega
  obtain ⟨hinvi, hk⟩ := hkind
  obtain ⟨hj, c, hc, hce⟩ := hcls i hi hinvi
  set j := W.cl i with hjdef
  have hyF : e (W.y j) ∈ F := by
    have e1 : e (W.y j) = (e c)⁻¹ * e i * (e c)⁻¹⁻¹ := by
      rw [inv_inv, mul_assoc, ← hce]
      group
    rw [e1]
    exact hF.normal _ (inv_mem (he c hc)) _ hiF
  have hc0 := hcl j hj
  simp only [clsOKW, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc0
  obtain ⟨⟨hyN, hconjs⟩, hk01⟩ := hc0
  have hwF : ∀ p ∈ W.conj j, e p.2 ∈ F := by
    intro p hp
    obtain ⟨⟨hp1, hp2⟩, hpc⟩ := hconjs p hp
    have e1 := hconj p.1 hp1 _ hyN p.2 hp2 hpc
    have e2 : e p.2 = e p.1 * e (W.y j) * (e p.1)⁻¹ := by
      rw [e1]
      group
    rw [e2]
    exact hF.normal _ (he _ hp1) _ hyF
  have hwN : ∀ p ∈ W.conj j, p.2 < N := fun p hp => (hconjs p hp).1.2
  by_cases h0 : W.kind j = 0
  · exfalso
    rw [ite_eq_left h0] at hk01
    obtain ⟨p, hp, hnc⟩ := List.any_eq_true.1 hk01
    have hc' := (hcomm _ hyN _ (hwN p hp)).2 (hF.comm _ hyF _ (hwF p hp))
    simp [hc'] at hnc
  have h1 : W.kind j = 1 := by omega
  rw [ite_eq_right h0, ite_eq_left h1] at hk01
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    bne_iff_ne, ne_eq, Bool.or_eq_true] at hk01
  obtain ⟨⟨⟨⟨hD, hdlN⟩, hdlc⟩, hsorted⟩, hlen⟩ := hk01
  have hFdl : ∀ f ∈ F, ∃ a ∈ W.dl j, e a = f := by
    intro f hf
    obtain ⟨a, ha, rfl⟩ := hsurj f (hF.le hf)
    refine ⟨a, ?_, rfl⟩
    rw [← List.contains_iff_mem, ← hD a ha, List.all_eq_true]
    intro p hp
    exact (hcomm _ ha _ (hwN p hp)).2 (hF.comm _ hf _ (hwF p hp))
  have hdlF : ∀ a ∈ W.dl j, e a ∈ F := by
    intro a ha
    refine hF.self_centralizing _ (he _ (hdlN a ha)) fun f hf => ?_
    obtain ⟨b, hb, rfl⟩ := hFdl f hf
    exact (hcomm _ (hdlN a ha) _ (hdlN b hb)).1 (hdlc a ha b hb)
  have hnd : (W.dl j).Nodup := hsorted.imp (fun h => Nat.ne_of_lt h)
  have hmapnd : ((W.dl j).map e).Nodup :=
    hnd.map_on fun a ha b hb hab => hinj a (hdlN a ha) b (hdlN b hb) hab
  have hset : (F : Set G) = ↑((W.dl j).map e).toFinset := by
    ext f
    simp only [SetLike.mem_coe, List.coe_toFinset, Set.mem_ofPred_eq, List.mem_map]
    exact ⟨hFdl f, fun ⟨a, ha, hf⟩ => hf ▸ hdlF a ha⟩
  have hl : (W.dl j).length = 64 := by
    have h1 : Nat.card F = (F : Set G).ncard := Nat.card_coe_set_eq _
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hmapnd, List.length_map,
      hF.card_eq] at h1
    exact h1.symm
  have hdc : W.dl j = W.c0 := hlen.resolve_left fun h => h hl
  rw [← hdc]
  exact ⟨fun hg => hFdl g hg, fun ⟨a, ha, hag⟩ => hag ▸ hdlF a ha⟩

theorem eq_of_uniqCheckW (he : ∀ i < N, e i ∈ S) (hsurj : ∀ g ∈ S, ∃ i < N, e i = g)
    (hinj : ∀ i < N, ∀ k < N, e i = e k → i = k)
    (hcomm : ∀ i < N, ∀ k < N, commB i k = true ↔ e i * e k = e k * e i)
    (hconj : ∀ c < N, ∀ a < N, ∀ w < N, conjB c a w = true → e c * e a = e w * e c)
    (hinv : ∀ i < N, e i * e i = 1 → e i ≠ 1 → invB i = true)
    (hcls : ∀ i < N, invB i = true → W.cl i < W.J ∧ ∃ c < N, e c * e (W.y (W.cl i)) = e i * e c)
    (h : uniqCheckW N commB conjB invB W = true) {F₁ F₂ : Subgroup G} (h₁ : IsNSC S F₁ 64)
    (h₂ : IsNSC S F₂ 64) : F₁ = F₂ :=
  Subgroup.ext fun g =>
    (mem_iff_of_uniqCheckW he hsurj hinj hcomm hconj hinv hcls h h₁ g).trans
      (mem_iff_of_uniqCheckW he hsurj hinj hcomm hconj hinv hcls h h₂ g).symm

end CFSG.EvenSmallLie.OmegaEight.SplitC
