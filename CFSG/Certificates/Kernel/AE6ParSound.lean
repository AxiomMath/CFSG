module

public import Certificates.Data.Kernel.AE6Par.Defs
public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLF

public section

namespace CFSG.KC.AE6Par

open Equiv Finset CFSG.ClassicalInvolution.Q3 Certificates.AE6Par Certificates.AE6Par.K

theorem ai (σ : Perm (Fin 8)) (x : Fin 8) : σ (σ⁻¹ x) = x := by
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

theorem ia (σ : Perm (Fin 8)) (x : Fin 8) : σ⁻¹ (σ x) = x := by
  rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]

theorem inS0_iff (σ : Perm (Fin 8)) :
    inS0 σ = true ↔ (∀ i, σ (pt i) = pt (σ i)) ∧ Perm.sign σ = 1 := by
  unfold inS0
  exact decide_eq_true_iff

def S0g : Subgroup (Perm (Fin 8)) where
  carrier := {σ | inS0 σ = true}
  mul_mem' {a b} ha hb := by
    rw [Set.mem_setOf_eq, inS0_iff] at *
    refine ⟨fun i => ?_, by rw [Perm.sign_mul, ha.2, hb.2, one_mul]⟩
    rw [Perm.mul_apply, Perm.mul_apply, hb.1, ha.1]
  one_mem' := by
    rw [Set.mem_setOf_eq, inS0_iff]
    exact ⟨fun _ => rfl, Perm.sign_one⟩
  inv_mem' {a} ha := by
    rw [Set.mem_setOf_eq, inS0_iff] at *
    refine ⟨fun i => ?_, by rw [Perm.sign_inv, ha.2]⟩
    apply a.injective
    rw [ha.1, ai, ai]

theorem codeOf_eq_iff (σ τ : Perm (Fin 8)) :
    codeOf σ = codeOf τ ↔ ∀ i, (τ⁻¹ * σ) (pt i) = pt ((τ⁻¹ * σ) i) := by
  unfold codeOf
  rw [List.map_inj_left]
  simp only [List.mem_finRange, true_implies, Perm.mul_apply]
  constructor
  · intro h i
    have h1 := h (σ i)
    rw [ia] at h1
    rw [h1, ia]
  · intro h x
    have h1 := h (σ⁻¹ x)
    rw [ai] at h1
    apply τ⁻¹.injective
    rw [h1, ia]

theorem inS0_of_code {σ τ : Perm (Fin 8)} (h : codeOf σ = codeOf τ) (hσ : Perm.sign σ = 1)
    (hτ : Perm.sign τ = 1) : inS0 (τ⁻¹ * σ) = true := by
  rw [inS0_iff]
  exact ⟨(codeOf_eq_iff σ τ).1 h, by rw [Perm.sign_mul, Perm.sign_inv, hσ, hτ, mul_one]⟩

theorem codeOf_mul_S0 (w : Perm (Fin 8)) {u : Perm (Fin 8)} (hu : inS0 u = true) :
    codeOf (w * u) = codeOf w := by
  rw [codeOf_eq_iff, inv_mul_cancel_left]
  exact ((inS0_iff u).1 hu).1

abbrev S0F : Finset (Perm (Fin 8)) := univ.filter fun σ => inS0 σ = true

theorem card_fibre (G : Finset (Perm (Fin 8)))
    (hS : ∀ σ ∈ G, ∀ u, inS0 u = true → σ * u ∈ G) (hE : ∀ σ ∈ G, Perm.sign σ = 1)
    {w : Perm (Fin 8)} (hw : w ∈ G) :
    (G.filter fun σ => codeOf σ = codeOf w).card = S0F.card := by
  have : (G.filter fun σ => codeOf σ = codeOf w) = S0F.image (w * ·) := by
    ext σ
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hσ, hc⟩
      exact ⟨w⁻¹ * σ, inS0_of_code hc (hE σ hσ) (hE w hw), mul_inv_cancel_left w σ⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hS w hw u hu, codeOf_mul_S0 w hu⟩
  rw [this, card_image_of_injective _ (mul_right_injective w)]

theorem card_eq_image_mul (G : Finset (Perm (Fin 8)))
    (hS : ∀ σ ∈ G, ∀ u, inS0 u = true → σ * u ∈ G) (hE : ∀ σ ∈ G, Perm.sign σ = 1) :
    G.card = (G.image codeOf).card * S0F.card := by
  rw [card_eq_sum_card_image codeOf G]
  apply sum_const_nat
  intro k hk
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hk
  exact card_fibre G hS hE hw

theorem card_A8 : (univ.filter fun σ : Perm (Fin 8) => Perm.sign σ = 1).card = 20160 := by
  have h := card_alternatingGroup (α := Fin 8)
  rw [Fintype.card_fin] at h
  have h2 : Fintype.card (alternatingGroup (Fin 8)) =
      (univ.filter fun σ : Perm (Fin 8) => Perm.sign σ = 1).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun σ => by simp [Perm.mem_alternatingGroup])
  rw [← h2, h]
  rfl

abbrev TreeP : Prop := treeElt 0 = 1 ∧ treeP.length = 191 ∧ ∀ i ∈ List.range 191,
    (treeP.getD i (0, 0)).2 ≤ i ∧ (treeP.getD i (0, 0)).1 < gens.length ∧
    treeElt (i + 1) = genElt (treeP.getD i (0, 0)).1 * treeElt (treeP.getD i (0, 0)).2

theorem tree_mem (ht : TreeP) (hl : gens.length = 18) (H : Subgroup (Perm (Fin 8)))
    (hg : ∀ g ∈ List.range 18, genElt g ∈ H) : ∀ i < 192, treeElt i ∈ H := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | k
    · rw [ht.1]
      exact H.one_mem
    · obtain ⟨hj, hgl, he⟩ := ht.2.2 k (List.mem_range.2 (by omega))
      rw [he]
      exact H.mul_mem (hg _ (List.mem_range.2 (hl ▸ hgl))) (ih _ (by omega) (by omega))

abbrev TreeF : Finset (Perm (Fin 8)) := ((List.range 192).map treeElt).toFinset

theorem card_treeF (hk : ((List.range 192).map fun i => permKey (treeElt i)).Nodup) :
    TreeF.card = 192 := by
  have h : ((List.range 192).map treeElt).Nodup := by
    rw [show (fun i => permKey (treeElt i)) = permKey ∘ treeElt from rfl, ← List.map_map] at hk
    exact hk.of_map _
  rw [List.toFinset_card_of_nodup h, List.length_map, List.length_range]

theorem treeF_sub (ht : TreeP) (hl : gens.length = 18)
    (hg : ∀ g ∈ List.range 18, inS0 (genElt g) = true) : TreeF ⊆ S0F := by
  intro σ hσ
  rw [List.mem_toFinset, List.mem_map] at hσ
  obtain ⟨i, hi, rfl⟩ := hσ
  simp only [S0F, mem_filter, mem_univ, true_and]
  exact tree_mem ht hl S0g hg i (List.mem_range.1 hi)

abbrev codesL : List (List (Fin 8)) := codeOf 1 :: dcTable.map Prod.fst

theorem tau_sign (hw : chkWords () = true) : ∀ j < 6, Perm.sign (tau j) = 1 := by
  simp only [chkWords, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact fun j hj => hw.1.1.2.2 j (List.mem_range.2 hj)

theorem row_witness (hr : ∀ e ∈ dcTable, RowOK e) {e} (he : e ∈ dcTable) :
    codeOf ((swapsPerm e.2.2)⁻¹ * tau e.2.1) = e.1 := (hr e he).2.2

theorem row_sign (hw : chkWords () = true) (hr : ∀ e ∈ dcTable, RowOK e) {e} (he : e ∈ dcTable) :
    Perm.sign ((swapsPerm e.2.2)⁻¹ * tau e.2.1) = 1 := by
  rw [Perm.sign_mul, Perm.sign_inv, ((inS0_iff _).1 (hr e he).2.1).2,
    tau_sign hw _ (hr e he).1, mul_one]

structure A8Facts : Prop where
  card_S0 : S0F.card = 192
  tree : S0F = TreeF
  codes : ∀ σ : Perm (Fin 8), Perm.sign σ = 1 → codeOf σ ∈ codesL

theorem sound_A8 (ht : TreeP) (hk : ((List.range 192).map fun i => permKey (treeElt i)).Nodup)
    (hg : gens.length = 18 ∧ ∀ g ∈ List.range 18, inS0 (genElt g) = true)
    (hr : ∀ e ∈ dcTable, RowOK e) (hc : codesL.Nodup ∧ dcTable.length = 104)
    (hw : chkWords () = true) : A8Facts := by
  set A := univ.filter fun σ : Perm (Fin 8) => Perm.sign σ = 1 with hA
  have hS : ∀ σ ∈ A, ∀ u, inS0 u = true → σ * u ∈ A := by
    intro σ hσ u hu
    simp only [hA, mem_filter, mem_univ, true_and] at hσ ⊢
    rw [Perm.sign_mul, hσ, ((inS0_iff u).1 hu).2, one_mul]
  have hE : ∀ σ ∈ A, Perm.sign σ = 1 := fun σ hσ => (mem_filter.1 hσ).2
  have hcard := card_eq_image_mul A hS hE
  rw [card_A8] at hcard
  have hsub : codesL.toFinset ⊆ A.image codeOf := by
    intro k hk
    rw [List.mem_toFinset, List.mem_cons] at hk
    rw [mem_image]
    rcases hk with rfl | hk
    · exact ⟨1, by simp [hA], rfl⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
      exact ⟨_, by simp [hA, row_sign hw hr he], row_witness hr he⟩
  have hL : codesL.toFinset.card = 105 := by
    rw [List.toFinset_card_of_nodup hc.1]
    simp [hc.2]
  have h105 : 105 ≤ (A.image codeOf).card := by
    have := card_le_card hsub
    rwa [hL] at this
  have h192 : 192 ≤ S0F.card := by
    have := card_le_card (treeF_sub ht hg.1 hg.2)
    rwa [card_treeF hk] at this
  have hxy : 105 * S0F.card ≤ 20160 := by
    rw [hcard]
    exact Nat.mul_le_mul_right _ h105
  have hyx : (A.image codeOf).card * 192 ≤ 20160 := by
    rw [hcard]
    exact Nat.mul_le_mul_left _ h192
  have hS0 : S0F.card = 192 := by omega
  have himg : (A.image codeOf).card = 105 := by omega
  refine ⟨hS0, ?_, ?_⟩
  · exact (eq_of_subset_of_card_le (treeF_sub ht hg.1 hg.2) (by rw [hS0, card_treeF hk])).symm
  · intro σ hσ
    have heq := eq_of_subset_of_card_le hsub (by rw [hL, himg])
    have : codeOf σ ∈ A.image codeOf := mem_image_of_mem _ (by simp [hA, hσ])
    rw [← heq, List.mem_toFinset] at this
    exact this

theorem row_of_even (F : A8Facts) (hr : ∀ e ∈ dcTable, RowOK e) (hw : chkWords () = true)
    {σ : Perm (Fin 8)} (hσ : Perm.sign σ = 1) (hn : inS0 σ = false) :
    ∃ e ∈ dcTable, e.1 = codeOf σ ∧
      inS0 ((tau e.2.1)⁻¹ * swapsPerm e.2.2 * σ) = true := by
  have hc := F.codes σ hσ
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · have := inS0_of_code hc hσ Perm.sign_one
    rw [inv_one, one_mul, hn] at this
    exact absurd this (by decide)
  · obtain ⟨e, he, hk⟩ := List.mem_map.1 hc
    refine ⟨e, he, hk, ?_⟩
    have h := inS0_of_code (hk.symm.trans (row_witness hr he).symm) hσ (row_sign hw hr he)
    rw [mul_inv_rev, inv_inv] at h
    exact h

theorem word_mem (H : Subgroup (Perm (Fin 8))) (hS : ∀ u, inS0 u = true → u ∈ H)
    {allowed : List ℕ} (hA : ∀ j ∈ allowed, tau j ∈ H) {g : Perm (Fin 8)}
    {w : List (ℕ × ℕ × List (Fin 8 × Fin 8))} (h : WordOK allowed g w) : g ∈ H := by
  obtain ⟨hl, hp⟩ := h
  rw [← hp]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  rcases hl a ha with ⟨h0, hs⟩ | ⟨h12, hj⟩
  · simp only [letterVal, h0, if_true]
    exact hS _ hs
  · rcases h12 with h1 | h2
    · simp only [letterVal, h1, one_ne_zero, if_false, if_true]
      exact hA _ hj
    · simp only [letterVal, h2, OfNat.ofNat_ne_zero, if_false, OfNat.ofNat_ne_one]
      exact H.inv_mem (hA _ hj)

theorem stabB_iff (F : List (Finset (Fin 8))) (σ : Perm (Fin 8)) :
    stabB F σ = true ↔ σ ∈ AE.stabFamily F := by
  unfold stabB
  rw [decide_eq_true_iff]
  exact Iff.rfl

theorem map_mul_perm (s : Finset (Fin 8)) (σ τ : Perm (Fin 8)) :
    (s.map τ.toEmbedding).map σ.toEmbedding = s.map (σ * τ).toEmbedding := by
  rw [Finset.map_map]
  rfl

theorem map_swap01_twice (s : Finset (Fin 8)) :
    (s.map (swap (0 : Fin 8) 1).toEmbedding).map (swap (0 : Fin 8) 1).toEmbedding = s := by
  rw [map_mul_perm, swap_mul_self]
  exact Finset.map_refl

theorem conj_mem_agl (hp : planes2 = AE.affinePlanes.map fun s => s.map (swap 0 1).toEmbedding)
    {σ : Perm (Fin 8)} (hσ : σ ∈ AE.stabFamily planes2) :
    swap 0 1 * σ * swap 0 1 ∈ AE.agl32 := by
  have key : ∀ τ ∈ AE.stabFamily planes2, ∀ s ∈ AE.affinePlanes,
      s.map (swap 0 1 * τ * swap 0 1).toEmbedding ∈ AE.affinePlanes := by
    intro τ hτ s hs
    have h1 : s.map (swap 0 1).toEmbedding ∈ planes2 := by
      rw [hp]
      exact List.mem_map_of_mem hs
    have h2 := (hτ _ h1).1
    rw [hp] at h2
    obtain ⟨t, ht, he⟩ := List.mem_map.1 h2
    rw [← map_mul_perm, ← map_mul_perm, ← he, map_swap01_twice]
    exact ht
  intro s hs
  refine ⟨key σ hσ s hs, ?_⟩
  have : (swap 0 1 * σ * swap 0 1)⁻¹ = swap 0 1 * σ⁻¹ * swap 0 1 := by
    rw [mul_inv_rev, mul_inv_rev, swap_inv, mul_assoc]
  rw [this]
  exact key _ ((AE.stabFamily planes2).inv_mem hσ) s hs

theorem planes2_sign (hp : planes2 = AE.affinePlanes.map fun s => s.map (swap 0 1).toEmbedding)
    {σ : Perm (Fin 8)} (hσ : σ ∈ AE.stabFamily planes2) : Perm.sign σ = 1 := by
  have h := TL4.agl32_sign _ (conj_mem_agl hp hσ)
  rw [Perm.sign_mul, Perm.sign_mul, mul_comm, ← mul_assoc, Int.units_mul_self, one_mul] at h
  exact h

structure AglFacts (H : Subgroup (Perm (Fin 8))) (T : List (List (Fin 8))) (k : ℕ) : Prop where
  sub : ∀ σ, inS0 σ = true → σ ∈ H
  codes : ∀ σ ∈ H, codeOf σ ∈ T
  mem : ∀ σ, Perm.sign σ = 1 → codeOf σ ∈ T → σ ∈ H
  card : ∀ p : Perm (Fin 8) → Bool, (∀ σ, p σ = true ↔ σ ∈ H) →
    (univ.filter fun σ => p σ = true).card = 1344
  row : ∀ σ ∈ H, inS0 σ = false → ∃ e ∈ dcTable, e.1 = codeOf σ ∧ e.2.1 = k ∧
    inS0 ((tau e.2.1)⁻¹ * swapsPerm e.2.2 * σ) = true

theorem sound_agl (F : A8Facts) (hr : ∀ e ∈ dcTable, RowOK e) (hw : chkWords () = true)
    (hc : codesL.Nodup) (ht : TreeP) (hl : gens.length = 18)
    (H : Subgroup (Perm (Fin 8))) (T : List (List (Fin 8))) (k : ℕ)
    (hT : codeOf 1 :: (dcTable.filter fun e => e.2.1 = k).map Prod.fst = T) (hT7 : T.length = 7)
    (hgH : ∀ g ∈ List.range 18, genElt g ∈ H) (hE : ∀ σ ∈ H, Perm.sign σ = 1)
    (htk : tau k ∈ H)
    (hbad : (∀ u, inS0 u = true → u ∈ H) → ∀ j < 6, j ≠ k → tau j ∈ H → False) :
    AglFacts H T k := by
  have hsub : ∀ σ, inS0 σ = true → σ ∈ H := by
    intro σ hσ
    have : σ ∈ TreeF := by
      rw [← F.tree]
      simpa using hσ
    rw [List.mem_toFinset, List.mem_map] at this
    obtain ⟨i, hi, rfl⟩ := this
    exact tree_mem ht hl H hgH i (List.mem_range.1 hi)
  have hrow : ∀ σ ∈ H, inS0 σ = false → ∃ e ∈ dcTable, e.1 = codeOf σ ∧ e.2.1 = k ∧
      inS0 ((tau e.2.1)⁻¹ * swapsPerm e.2.2 * σ) = true := by
    intro σ hσ hn
    obtain ⟨e, he, hk, hu⟩ := row_of_even F hr hw (hE σ hσ) hn
    refine ⟨e, he, hk, ?_, hu⟩
    by_contra hne
    apply hbad hsub _ (hr e he).1 hne
    have h1 : tau e.2.1 = swapsPerm e.2.2 * σ * ((tau e.2.1)⁻¹ * swapsPerm e.2.2 * σ)⁻¹ := by
      group
    rw [h1]
    exact H.mul_mem (H.mul_mem (hsub _ (hr e he).2.1) hσ) (H.inv_mem (hsub _ hu))
  have hcodes : ∀ σ ∈ H, codeOf σ ∈ T := by
    intro σ hσ
    rw [← hT, List.mem_cons]
    cases hn : inS0 σ
    · obtain ⟨e, he, hk, hj, -⟩ := hrow σ hσ hn
      right
      rw [← hk]
      exact List.mem_map_of_mem (List.mem_filter.2 ⟨he, by simpa using hj⟩)
    · left
      rw [codeOf_eq_iff, inv_one, one_mul]
      exact ((inS0_iff σ).1 hn).1
  have hwit : ∀ c ∈ T, ∃ w ∈ H, codeOf w = c := by
    intro c hcT
    rw [← hT, List.mem_cons] at hcT
    rcases hcT with rfl | hcT
    · exact ⟨1, H.one_mem, rfl⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hcT
      obtain ⟨he, hj⟩ := List.mem_filter.1 he
      have hj : e.2.1 = k := by simpa using hj
      refine ⟨_, H.mul_mem (H.inv_mem (hsub _ (hr e he).2.1)) (hj ▸ htk), row_witness hr he⟩
  have hmem : ∀ σ, Perm.sign σ = 1 → codeOf σ ∈ T → σ ∈ H := by
    intro σ hσ hcT
    obtain ⟨w, hwH, hw⟩ := hwit _ hcT
    have hu := inS0_of_code hw.symm hσ (hE w hwH)
    rw [show σ = w * (w⁻¹ * σ) by group]
    exact H.mul_mem hwH (hsub _ hu)
  refine ⟨hsub, hcodes, hmem, fun p hp => ?_, hrow⟩
  set G := univ.filter fun σ => p σ = true with hG
  have hcard := card_eq_image_mul G (fun σ hσ u hu => by
      simp only [hG, mem_filter, mem_univ, true_and, hp] at hσ ⊢
      exact H.mul_mem hσ (hsub u hu))
    (fun σ hσ => hE σ (by simpa [hG, hp] using hσ))
  have himg : G.image codeOf = T.toFinset := by
    ext c
    simp only [mem_image, List.mem_toFinset, hG, mem_filter, mem_univ, true_and, hp]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact hcodes σ hσ
    · intro hcT
      exact hwit c hcT
  have hTn : T.Nodup := by
    rw [← hT]
    exact hc.sublist (((List.filter_sublist).map _).cons₂ _)
  rw [hcard, himg, List.toFinset_card_of_nodup hTn, hT7, F.card_S0]

theorem dt_apply {p q r s : Fin 8} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) :
    (swap p q * swap r s) p = q ∧ (swap p q * swap r s) q = p ∧ (swap p q * swap r s) r = s ∧
      (swap p q * swap r s) s = r ∧
      ∀ x, x ≠ p → x ≠ q → x ≠ r → x ≠ s → (swap p q * swap r s) x = x := by
  simp only [Perm.mul_apply]
  refine ⟨?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 => ?_⟩
  · rw [swap_apply_of_ne_of_ne hpr hps, swap_apply_left]
  · rw [swap_apply_of_ne_of_ne hqr hqs, swap_apply_right]
  · rw [swap_apply_left, swap_apply_of_ne_of_ne hps.symm hqs.symm]
  · rw [swap_apply_right, swap_apply_of_ne_of_ne hpr.symm hqr.symm]
  · rw [swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]

theorem vk_dt {p q r s : Fin 8} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) : vkPred {p, q, r, s} (swap p q * swap r s) = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := dt_apply hpq hpr hps hqr hqs hrs
  generalize swap p q * swap r s = τ at h1 h2 h3 h4 h5 ⊢
  unfold vkPred
  rw [decide_eq_true_iff]
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, Or.inr fun x hx => ?_⟩
  · simp only [mem_insert, mem_singleton, not_or] at hx
    exact h5 x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  · simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [h1]; simp
    · rw [h2]; simp
    · rw [h3]; simp
    · rw [h4]; simp
  · ext x
    rw [Perm.mul_apply, Perm.one_apply]
    by_cases hxp : x = p
    · rw [hxp, h1, h2]
    by_cases hxq : x = q
    · rw [hxq, h2, h1]
    by_cases hxr : x = r
    · rw [hxr, h3, h4]
    by_cases hxs : x = s
    · rw [hxs, h4, h3]
    rw [h5 x hxp hxq hxr hxs, h5 x hxp hxq hxr hxs]
  · simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [h1]; exact hpq.symm
    · rw [h2]; exact hpq
    · rw [h3]; exact hrs.symm
    · rw [h4]; exact hrs

theorem perm_eq_of {σ τ : Perm (Fin 8)} {a b c d : Fin 8} (ha : σ a = τ a) (hb : σ b = τ b)
    (hc : σ c = τ c) (hd : σ d = τ d) (hσ : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → σ x = x)
    (hτ : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → τ x = x) : σ = τ := by
  ext x
  by_cases hxa : x = a
  · rw [hxa, ha]
  by_cases hxb : x = b
  · rw [hxb, hb]
  by_cases hxc : x = c
  · rw [hxc, hc]
  by_cases hxd : x = d
  · rw [hxd, hd]
  rw [hσ x hxa hxb hxc hxd, hτ x hxa hxb hxc hxd]

theorem vk_cases {a b c d : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) {σ : Perm (Fin 8)} (h : vkPred {a, b, c, d} σ = true) :
    σ = 1 ∨ σ ∈ dtl a b c d := by
  unfold vkPred at h
  rw [decide_eq_true_iff] at h
  obtain ⟨hfix, hin, hinv, h1 | hfp⟩ := h
  · exact Or.inl h1
  right
  have hσσ : ∀ x, σ (σ x) = x := fun x => by rw [← Perm.mul_apply, hinv, Perm.one_apply]
  have hoff : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → σ x = x := fun x h1 h2 h3 h4 =>
    hfix x (by simp [h1, h2, h3, h4])
  have mem : ∀ x ∈ ({a, b, c, d} : Finset (Fin 8)), σ x = a ∨ σ x = b ∨ σ x = c ∨ σ x = d :=
    fun x hx => by simpa using hin x hx
  have ma : a ∈ ({a, b, c, d} : Finset (Fin 8)) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset (Fin 8)) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset (Fin 8)) := by simp
  have md : d ∈ ({a, b, c, d} : Finset (Fin 8)) := by simp
  have fa := hfp a ma
  have fb := hfp b mb
  have fc := hfp c mc
  simp only [dtl, List.mem_cons, List.not_mem_nil, or_false]
  rcases mem a ma with h | h | h | h
  · exact absurd h fa
  · have hb : σ b = a := by rw [← h, hσσ]
    have hc : σ c = d := by
      rcases mem c mc with h' | h' | h' | h'
      · exact absurd (σ.injective (h'.trans hb.symm)) hbc.symm
      · exact absurd (σ.injective (h'.trans h.symm)) hac.symm
      · exact absurd h' fc
      · exact h'
    have hd : σ d = c := by rw [← hc, hσσ]
    obtain ⟨t1, t2, t3, t4, t5⟩ := dt_apply hab hac had hbc hbd hcd
    exact Or.inl (perm_eq_of (h.trans t1.symm) (hb.trans t2.symm) (hc.trans t3.symm)
      (hd.trans t4.symm) hoff t5)
  · have hc : σ c = a := by rw [← h, hσσ]
    have hb : σ b = d := by
      rcases mem b mb with h' | h' | h' | h'
      · exact absurd (σ.injective (h'.trans hc.symm)) hbc
      · exact absurd h' fb
      · exact absurd (σ.injective (h'.trans h.symm)) hab.symm
      · exact h'
    have hd : σ d = b := by rw [← hb, hσσ]
    obtain ⟨t1, t2, t3, t4, t5⟩ := dt_apply hac hab had hbc.symm hcd hbd
    exact Or.inr (Or.inl (perm_eq_of (h.trans t1.symm) (hb.trans t3.symm) (hc.trans t2.symm)
      (hd.trans t4.symm) hoff fun x h1 h2 h3 h4 => t5 x h1 h3 h2 h4))
  · have hd : σ d = a := by rw [← h, hσσ]
    have hb : σ b = c := by
      rcases mem b mb with h' | h' | h' | h'
      · exact absurd (σ.injective (h'.trans hd.symm)) hbd
      · exact absurd h' fb
      · exact h'
      · exact absurd (σ.injective (h'.trans h.symm)) hab.symm
    have hc : σ c = b := by rw [← hb, hσσ]
    obtain ⟨t1, t2, t3, t4, t5⟩ := dt_apply had hab hac hbd.symm hcd.symm hbc
    exact Or.inr (Or.inr (perm_eq_of (h.trans t1.symm) (hb.trans t3.symm) (hc.trans t4.symm)
      (hd.trans t2.symm) hoff fun x h1 h2 h3 h4 => t5 x h1 h4 h2 h3))

theorem four_sort {δ : Finset (Fin 8)} (h : δ.card = 4) : ∃ a b c d : Fin 8, a < b ∧ b < c ∧
    c < d ∧ δ.sort (· ≤ ·) = [a, b, c, d] ∧ δ = {a, b, c, d} := by
  have hlen : (δ.sort (· ≤ ·)).length = 4 := by rw [Finset.length_sort, h]
  have hs : (δ.sort (· ≤ ·)).Pairwise (· < ·) := (Finset.sortedLT_sort δ).pairwise
  have htf : (δ.sort (· ≤ ·)).toFinset = δ := Finset.sort_toFinset _ _
  generalize δ.sort (· ≤ ·) = l at hlen hs htf ⊢
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩
  · simp only [List.length_nil] at hlen; omega
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  · refine ⟨a, b, c, d, List.rel_of_pairwise_cons hs (by simp),
      List.rel_of_pairwise_cons hs.of_cons (by simp),
      List.rel_of_pairwise_cons hs.of_cons.of_cons (by simp), rfl, ?_⟩
    rw [← htf]
    ext x
    simp
  · simp only [List.length_cons] at hlen; omega

theorem dts_eq {δ : Finset (Fin 8)} {a b c d : Fin 8} (h : δ.sort (· ≤ ·) = [a, b, c, d]) :
    dts δ = dtl a b c d := by
  simp only [dts, h, dtl]

theorem mem_fours {δ : Finset (Fin 8)} (h : δ ∈ fours ()) : δ.card = 4 := by
  unfold fours at h
  exact (mem_powersetCard.1 h).2

theorem maskF_inj {s t : Finset (Fin 8)} (h : maskF s = maskF t) : s = t := by
  have key : ∀ u : Finset (Fin 8), maskF u = equivBitIndices.symm (u.map Fin.valEmbedding) := by
    intro u
    rw [equivBitIndices_symm_apply, sum_map]
    rfl
  rw [key, key] at h
  exact map_injective Fin.valEmbedding (equivBitIndices.symm.injective h)

theorem m4_eq {a b c d : Fin 8} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    maskF {a, b, c, d} = m4 a b c d := by
  have h1 : a ≠ b := hab.ne
  have h2 : a ≠ c := (hab.trans hbc).ne
  have h3 : a ≠ d := (hab.trans (hbc.trans hcd)).ne
  have h4 : b ≠ c := hbc.ne
  have h5 : b ≠ d := (hbc.trans hcd).ne
  have h6 : c ≠ d := hcd.ne
  unfold maskF m4
  rw [sum_insert (by simp [h1, h2, h3]), sum_insert (by simp [h4, h5]), sum_insert (by simp [h6]),
    sum_singleton]
  rfl

theorem mem_of_mask {F : List (Finset (Fin 8))} {M : List ℕ} (hM : F.map maskF = M)
    {δ : Finset (Fin 8)} (h : maskF δ ∈ M) : δ ∈ F := by
  rw [← hM] at h
  obtain ⟨P, hP, he⟩ := List.mem_map.1 h
  rwa [← maskF_inj he]

theorem quad_ne {a b c d : Fin 8} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d :=
  ⟨hab.ne, (hab.trans hbc).ne, (hab.trans (hbc.trans hcd)).ne, hbc.ne, (hbc.trans hcd).ne, hcd.ne⟩

theorem vk_dtl {a b c d : Fin 8} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∀ σ ∈ dtl a b c d, vkPred {a, b, c, d} σ = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := quad_ne hab hbc hcd
  intro σ hσ
  simp only [dtl, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl
  · exact vk_dt h1 h2 h3 h4 h5 h6
  · have : ({a, b, c, d} : Finset (Fin 8)) = {a, c, b, d} := by
      ext x; simp only [mem_insert, mem_singleton]; tauto
    rw [this]
    exact vk_dt h2 h1 h3 h4.symm h6 h5
  · have : ({a, b, c, d} : Finset (Fin 8)) = {a, d, b, c} := by
      ext x; simp only [mem_insert, mem_singleton]; tauto
    rw [this]
    exact vk_dt h3 h1 h2 h5.symm h6.symm h4

theorem card_inter_of_symmDiff {α β : Finset (Fin 8)} (ha : α.card = 4) (hb : β.card = 4)
    (h : (symmDiff α β).card = 4) : (α ∩ β).card = 2 := by
  rw [symmDiff_def, sup_eq_union, card_union_of_disjoint disjoint_sdiff_sdiff] at h
  have h1 := card_sdiff_add_card_inter α β
  have h2 := card_sdiff_add_card_inter β α
  rw [inter_comm] at h2
  omega

theorem inC_iff {c : List (Fin 8)} {T : List (List (Fin 8))} : inC c T = true ↔ c ∈ T := by
  unfold inC
  simp [List.any_eq_true]

theorem inN_iff {m : ℕ} {M : List ℕ} : inN m M = true ↔ m ∈ M := by
  unfold inN
  simp [List.any_eq_true, Nat.beq_eq]

theorem allIn_of {T : List (List (Fin 8))} {a b c d : Fin 8}
    (h : ∀ σ ∈ dtl a b c d, codeOf σ ∈ T) : Certificates.AE6Par.K.allIn T a b c d = true := by
  simp only [dtl, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  unfold Certificates.AE6Par.K.allIn
  simp only [Bool.and_eq_true, inC_iff]
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem quadB_spec {a b c d : Fin 8} (h : quadB a b c d = true) :
    m4 a b c d ∈ tab1M ∧ (meets2 a b c d = true → m4 a b c d ∈ tab2M) ∧
      (Certificates.AE6Par.K.allIn t0L a b c d = true → m4 a b c d ∈ affM) ∧
      (Certificates.AE6Par.K.allIn t1L a b c d = true → m4 a b c d ∈ p2M) := by
  unfold quadB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨inN_iff.1 h1, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · rcases h2 with h2 | h2
    · simp [hm] at h2
    · exact inN_iff.1 h2
  · rcases h3 with h3 | h3
    · simp [hm] at h3
    · exact inN_iff.1 h3
  · rcases h4 with h4 | h4
    · simp [hm] at h4
    · exact inN_iff.1 h4

theorem sixB_spec {a b c d : Fin 8} (h : sixB a b c d = true) :
    a < b ∧ b < c ∧ c < d ∧ ∀ σ ∈ dtl a b c d, inS0 σ = true := by
  unfold sixB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, fun σ hσ => ?_⟩
  simp only [dtl, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl
  · exact h4
  · exact h5
  · exact h6

theorem ptabB_spec {T : List (List (Fin 8))} {e : Finset (Fin 8) × List (Fin 8 × Fin 8)}
    (h : ptabB T e = true) : Perm.sign (swapsPerm e.2) = 1 ∧ codeOf (swapsPerm e.2) ∈ T ∧
      d0.map (swapsPerm e.2).toEmbedding = e.1 := by
  unfold ptabB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, inC_iff.1 h.1.2, h.2⟩

theorem chk_all (ht : TreeP)
    (hk0 : (List.range 192).map (fun i => permKey (treeElt i)) = treeKeys)
    (hk1 : treeKeys.Nodup)
    (hg : gens.length = 18 ∧ ∀ g ∈ List.range 18, inS0 (genElt g) = true)
    (hr : ∀ e ∈ dcTable, RowOK e)
    (hc : (codeOf 1 :: dcTable.map Prod.fst).Nodup ∧ dcTable.length = 104)
    (ht01 : codeOf 1 :: (dcTable.filter fun e => e.2.1 = 0).map Prod.fst = t0L ∧
      codeOf 1 :: (dcTable.filter fun e => e.2.1 = 1).map Prod.fst = t1L)
    (hw : chkWords () = true)
    (hn : stabB AE.affinePlanes (tau 1) = false ∧ stabB planes2 (tau 0) = false)
    (hgs : ∀ g ∈ List.range 18,
      stabB AE.affinePlanes (genElt g) = true ∧ stabB planes2 (genElt g) = true)
    (hp : planes2 = AE.affinePlanes.map fun s => s.map (swap 0 1).toEmbedding)
    (hvk : (∀ g ∈ gens, g.1 ∈ six ∧ vkPred g.1 (swapsPerm g.2) = true) ∧
      ∀ x y : Fin 8, x ≠ y → ∃ δ ∈ six, x ∈ δ ∧ y ∈ δ)
    (hsix : six = sixL.map q4 ∧ ∀ q ∈ sixL, sixB q.1 q.2.1 q.2.2.1 q.2.2.2 = true)
    (hmP : AE.affinePlanes.map maskF = affM ∧ planes2.map maskF = p2M)
    (hmT : tab1.map (fun e => maskF (d0.map (swapsPerm e).toEmbedding)) = tab1M ∧
      tab2.map (fun e => maskF (b0.map (swapsPerm e).toEmbedding)) = tab2M ∧
      ∀ e ∈ tab2, d0.map (swapsPerm e).toEmbedding = d0)
    (hq0 : ∀ a b : Fin 8, a < b → ∀ c : Fin 8, b < c → ∀ d : Fin 8, c < d →
      quadB a b c d = true)
    (hpf : ptab1.map Prod.fst = AE.affinePlanes ∧ ptab2.map Prod.fst = planes2)
    (hpt : (∀ e ∈ ptab1, ptabB t0L e = true) ∧ ∀ e ∈ ptab2, ptabB t1L e = true) :
    chkAgl () = true ∧ chkDc () = true ∧ chkWords () = true ∧ chkTree () = true ∧
      chkVK () = true ∧ chkPlanes () = true ∧ chkSym () = true := by
  have hm : AE.affinePlanes.map maskF = affM ∧ planes2.map maskF = p2M ∧
      tab1.map (fun e => maskF (d0.map (swapsPerm e).toEmbedding)) = tab1M ∧
      tab2.map (fun e => maskF (b0.map (swapsPerm e).toEmbedding)) = tab2M ∧
      ∀ e ∈ tab2, d0.map (swapsPerm e).toEmbedding = d0 := ⟨hmP.1, hmP.2, hmT⟩
  have hq := fun a b hab c hbc d hcd => quadB_spec (hq0 a b hab c hbc d hcd)
  have hk : ((List.range 192).map fun i => permKey (treeElt i)).Nodup := hk0 ▸ hk1
  have F := sound_A8 ht hk hg hr hc hw
  have hw' := hw
  simp only [chkWords, Bool.and_eq_true, decide_eq_true_eq] at hw'
  have hbad1 : (∀ u, inS0 u = true → u ∈ AE.stabFamily AE.affinePlanes) → ∀ j < 6, j ≠ 0 →
      tau j ∈ AE.stabFamily AE.affinePlanes → False := by
    intro hsub j hj h0 hτ
    have h1 : tau 1 ∈ AE.stabFamily AE.affinePlanes := by
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · obtain rfl : j = 1 := by omega
        exact hτ
      · obtain ⟨l, rfl⟩ : ∃ l, j = l + 2 := ⟨j - 2, by omega⟩
        refine word_mem _ hsub (allowed := [l + 2]) (fun j' hj' => ?_)
          (hw'.2 l (List.mem_range.2 (by omega))).2
        rw [List.mem_singleton.1 hj']
        exact hτ
    rw [← stabB_iff, hn.1] at h1
    exact absurd h1 (by decide)
  have hbad2 : (∀ u, inS0 u = true → u ∈ AE.stabFamily planes2) → ∀ j < 6, j ≠ 1 →
      tau j ∈ AE.stabFamily planes2 → False := by
    intro hsub j hj h0 hτ
    have h1 : tau 0 ∈ AE.stabFamily planes2 := by
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · obtain rfl : j = 0 := by omega
        exact hτ
      · obtain ⟨l, rfl⟩ : ∃ l, j = l + 2 := ⟨j - 2, by omega⟩
        refine word_mem _ hsub (allowed := [l + 2]) (fun j' hj' => ?_)
          (hw'.2 l (List.mem_range.2 (by omega))).1
        rw [List.mem_singleton.1 hj']
        exact hτ
    rw [← stabB_iff, hn.2] at h1
    exact absurd h1 (by decide)
  have A1 := sound_agl F hr hw hc.1 ht hg.1 (AE.stabFamily AE.affinePlanes) t0L 0 ht01.1 rfl
    (fun g hg' => (stabB_iff _ _).1 (hgs g hg').1) (fun σ hσ => TL4.agl32_sign σ hσ)
    ((stabB_iff _ _).1 hw'.1.1.1) hbad1
  have A2 := sound_agl F hr hw hc.1 ht hg.1 (AE.stabFamily planes2) t1L 1 ht01.2 rfl
    (fun g hg' => (stabB_iff _ _).1 (hgs g hg').2) (fun σ hσ => planes2_sign hp hσ)
    ((stabB_iff _ _).1 hw'.1.1.2.1) hbad2
  refine ⟨?_, ?_, hw, ?_, ?_, ?_, ?_⟩
  ·
    simp only [chkAgl, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨F.card_S0, ?_⟩, ?_⟩, fun σ h => ⟨(stabB_iff _ _).2 (A1.sub σ h),
      (stabB_iff _ _).2 (A2.sub σ h)⟩⟩
    · exact A1.card _ (stabB_iff _)
    · exact A2.card _ (stabB_iff _)
  ·
    simp only [chkDc, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, fun σ hσ => ?_⟩
    · cases hn' : inS0 σ
      · right
        obtain ⟨e, he, hk', hu⟩ := row_of_even F hr hw hσ hn'
        simp only [dcWit, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        exact ⟨e, he, ⟨⟨hk', (hr e he).1⟩, (hr e he).2.1⟩, hu⟩
      · exact Or.inl rfl
    · rw [stabB_iff] at hσ
      cases hn' : inS0 σ
      · right
        obtain ⟨e, he, hk', hj, hu⟩ := A1.row σ hσ hn'
        simp only [dcWitJ, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
        exact ⟨e, he, ⟨⟨hk', hj⟩, (hr e he).2.1⟩, hu⟩
      · exact Or.inl rfl
    · rw [stabB_iff] at hσ
      cases hn' : inS0 σ
      · right
        obtain ⟨e, he, hk', hj, hu⟩ := A2.row σ hσ hn'
        simp only [dcWitJ, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
        exact ⟨e, he, ⟨⟨hk', hj⟩, (hr e he).2.1⟩, hu⟩
      · exact Or.inl rfl
  ·
    simp only [chkTree, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨ht, fun σ hσ => ?_⟩
    have h1 : σ ∈ TreeF := by
      rw [← F.tree]
      simpa using hσ
    rw [List.mem_toFinset, List.mem_map] at h1
    exact h1
  ·
    simp only [chkVK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hvk.1, fun δ hδ σ hv => ?_⟩, hvk.2⟩
    rw [hsix.1] at hδ
    obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hδ
    have h6 := sixB_spec (hsix.2 q hq')
    unfold q4 at hv
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := quad_ne h6.1 h6.2.1 h6.2.2.1
    rcases vk_cases n1 n2 n3 n4 n5 n6 hv with rfl | hm'
    · exact S0g.one_mem
    · exact h6.2.2.2 σ hm'
  ·
    simp only [chkPlanes, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨fun δ hδ => ?_, fun δ hδ h => ?_⟩, fun δ hδ h => ?_⟩, fun δ hδ => ?_⟩,
      fun δ hδ => ?_⟩
    · obtain ⟨a, b, c, d, hab, hbc, hcd, hs, rfl⟩ := four_sort (mem_fours hδ)
      rw [dts_eq hs]
      exact ⟨rfl, vk_dtl hab hbc hcd⟩
    · obtain ⟨a, b, c, d, hab, hbc, hcd, hs, rfl⟩ := four_sort (mem_fours hδ)
      rw [dts_eq hs] at h
      have hq' := hq a b hab c hbc d hcd
      apply mem_of_mask hm.1
      rw [m4_eq hab hbc hcd]
      apply hq'.2.2.1
      apply allIn_of
      intro σ hσ
      exact A1.codes σ ((stabB_iff _ _).1 (h σ hσ))
    · obtain ⟨a, b, c, d, hab, hbc, hcd, hs, rfl⟩ := four_sort (mem_fours hδ)
      rw [dts_eq hs] at h
      have hq' := hq a b hab c hbc d hcd
      apply mem_of_mask hm.2.1
      rw [m4_eq hab hbc hcd]
      apply hq'.2.2.2
      apply allIn_of
      intro σ hσ
      exact A2.codes σ ((stabB_iff _ _).1 (h σ hσ))
    · rw [← hpf.1] at hδ
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hδ
      have h1 := ptabB_spec (hpt.1 e he)
      exact ⟨e, he, rfl, (stabB_iff _ _).2 (A1.mem _ h1.1 h1.2.1), h1.2.2⟩
    · rw [← hpf.2] at hδ
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hδ
      have h1 := ptabB_spec (hpt.2 e he)
      exact ⟨e, he, rfl, (stabB_iff _ _).2 (A2.mem _ h1.1 h1.2.1), h1.2.2⟩
  ·
    simp only [chkSym, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨fun α hα => ?_, fun β hβ h2 => ?_⟩, fun α hα β hβ h4 =>
      card_inter_of_symmDiff (mem_fours hα) (mem_fours hβ) h4⟩
    · obtain ⟨a, b, c, d, hab, hbc, hcd, -, rfl⟩ := four_sort (mem_fours hα)
      have h1 := (hq a b hab c hbc d hcd).1
      rw [← m4_eq hab hbc hcd, ← hm.2.2.1] at h1
      obtain ⟨e, he, hme⟩ := List.mem_map.1 h1
      exact ⟨e, he, maskF_inj hme⟩
    · obtain ⟨a, b, c, d, hab, hbc, hcd, -, rfl⟩ := four_sort (mem_fours hβ)
      have h1 := (hq a b hab c hbc d hcd).2.1 (decide_eq_true h2)
      rw [← m4_eq hab hbc hcd, ← hm.2.2.2.1] at h1
      obtain ⟨e, he, hme⟩ := List.mem_map.1 h1
      exact ⟨e, he, hm.2.2.2.2 e he, maskF_inj hme⟩

end CFSG.KC.AE6Par
