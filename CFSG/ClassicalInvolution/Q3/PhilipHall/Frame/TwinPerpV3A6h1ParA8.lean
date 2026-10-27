module

public import Certificates.Certificate517601
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1

open Equiv CFSG.ClassicalInvolution.Q3 Certificates.AE6Par

theorem inS0_iff {σ : Perm (Fin 8)} :
    inS0 σ = true ↔ (∀ i, σ (pt i) = pt (σ i)) ∧ Perm.sign σ = 1 :=
  decide_eq_true_iff

@[expose] def parS0 : Subgroup (Perm (Fin 8)) where
  carrier := {σ | inS0 σ = true}
  mul_mem' {σ τ} hσ hτ := by
    obtain ⟨hσ1, hσ2⟩ := inS0_iff.mp hσ
    obtain ⟨hτ1, hτ2⟩ := inS0_iff.mp hτ
    refine inS0_iff.mpr ⟨fun i => ?_, by rw [Perm.sign_mul, hσ2, hτ2, mul_one]⟩
    rw [Perm.mul_apply, Perm.mul_apply, hτ1, hσ1]
  one_mem' := inS0_iff.mpr ⟨fun _ => rfl, Perm.sign_one⟩
  inv_mem' {σ} hσ := by
    obtain ⟨hσ1, hσ2⟩ := inS0_iff.mp hσ
    refine inS0_iff.mpr ⟨fun i => ?_, by rw [Perm.sign_inv, hσ2]⟩
    apply σ.injective
    rw [hσ1 (σ⁻¹ i), Perm.inv_def, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem parS0_le_alternating : parS0 ≤ alternatingGroup (Fin 8) := fun _ hσ =>
  Perm.mem_alternatingGroup.mpr (inS0_iff.mp hσ).2

theorem mem_stabFamily_iff {F : List (Finset (Fin 8))} {σ : Perm (Fin 8)} :
    σ ∈ AE.stabFamily F ↔ stabB F σ = true := by
  rw [stabB, decide_eq_true_iff]
  exact Iff.rfl

@[expose] def parAgl2 : Subgroup (Perm (Fin 8)) := AE.stabFamily planes2

theorem card_d0 : d0.card = 4 := by decide

theorem card_b0 : b0.card = 4 := by decide

theorem mem_fours {δ : Finset (Fin 8)} (h : δ.card = 4) : δ ∈ fours () :=
  Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h⟩

theorem map_perm_mul (σ τ : Perm (Fin 8)) (s : Finset (Fin 8)) :
    s.map (σ * τ).toEmbedding = (s.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  rfl

theorem wordOK_mem {A : Subgroup (Perm (Fin 8))} (hS : parS0 ≤ A) {allowed : List ℕ}
    (ht : ∀ j ∈ allowed, tau j ∈ A) {g : Perm (Fin 8)}
    {w : List (ℕ × ℕ × List (Fin 8 × Fin 8))} (hw : WordOK allowed g w) : g ∈ A := by
  obtain ⟨hl, rfl⟩ := hw
  induction w with
  | nil => exact A.one_mem
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons]
    refine A.mul_mem ?_ (ih fun b hb => hl b (List.mem_cons_of_mem a hb))
    have ha := hl a List.mem_cons_self
    unfold letterOK at ha
    unfold letterVal
    rcases ha with ⟨h0, hs⟩ | ⟨h12, hj⟩
    · rw [if_pos h0]
      exact hS hs
    · have h0 : a.1 ≠ 0 := by omega
      rw [if_neg h0]
      split_ifs
      · exact ht _ hj
      · exact A.inv_mem (ht _ hj)

theorem dcWit_spec {σ : Perm (Fin 8)} (h : dcWit σ = true) :
    ∃ j < 6, ∃ s u : Perm (Fin 8), inS0 s = true ∧ inS0 u = true ∧ σ = s⁻¹ * tau j * u := by
  simp only [dcWit, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨e, -, ⟨⟨-, hj⟩, hs⟩, hu⟩ := h
  exact ⟨e.2.1, hj, swapsPerm e.2.2, _, hs, hu, by group⟩

theorem dcWitJ_spec {j : ℕ} {σ : Perm (Fin 8)} (h : dcWitJ j σ = true) :
    ∃ s u : Perm (Fin 8), inS0 s = true ∧ inS0 u = true ∧ σ = s⁻¹ * tau j * u := by
  simp only [dcWitJ, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨e, -, ⟨⟨-, rfl⟩, hs⟩, hu⟩ := h
  exact ⟨swapsPerm e.2.2, _, hs, hu, by group⟩

theorem tau_mem_of_dc {A : Subgroup (Perm (Fin 8))} (hS : parS0 ≤ A) {σ s u : Perm (Fin 8)}
    {j : ℕ} (hs : inS0 s = true) (hu : inS0 u = true) (he : σ = s⁻¹ * tau j * u) (hσ : σ ∈ A) :
    tau j ∈ A := by
  have : tau j = s * σ * u⁻¹ := by rw [he]; group
  rw [this]
  exact A.mul_mem (A.mul_mem (hS hs) hσ) (A.inv_mem (hS hu))

theorem mem_of_dc {A : Subgroup (Perm (Fin 8))} (hS : parS0 ≤ A) {σ s u : Perm (Fin 8)}
    {j : ℕ} (hs : inS0 s = true) (hu : inS0 u = true) (he : σ = s⁻¹ * tau j * u)
    (ht : tau j ∈ A) : σ ∈ A := by
  rw [he]
  exact A.mul_mem (A.mul_mem (A.inv_mem (hS hs)) ht) (hS hu)

section Checks

theorem par_agl :
    (((Finset.univ.filter fun σ : Perm (Fin 8) => inS0 σ = true).card = 192 ∧
      (Finset.univ.filter fun σ : Perm (Fin 8) => stabB AE.affinePlanes σ = true).card = 1344) ∧
      (Finset.univ.filter fun σ : Perm (Fin 8) => stabB planes2 σ = true).card = 1344) ∧
    ∀ σ : Perm (Fin 8), inS0 σ = true →
      stabB AE.affinePlanes σ = true ∧ stabB planes2 σ = true := by
  have h : chkAgl () = true := Certificates.certificate517601.1
  simpa only [chkAgl, Bool.and_eq_true, decide_eq_true_eq] using h

theorem par_dc :
    ((∀ σ : Perm (Fin 8), Perm.sign σ = 1 → inS0 σ = true ∨ dcWit σ = true) ∧
      ∀ σ : Perm (Fin 8), stabB AE.affinePlanes σ = true → inS0 σ = true ∨ dcWitJ 0 σ = true) ∧
    ∀ σ : Perm (Fin 8), stabB planes2 σ = true → inS0 σ = true ∨ dcWitJ 1 σ = true := by
  have h : chkDc () = true := Certificates.certificate517601.2.1
  simpa only [chkDc, Bool.and_eq_true, decide_eq_true_eq] using h

theorem par_words :
    ((stabB AE.affinePlanes (tau 0) = true ∧ stabB planes2 (tau 1) = true ∧
        ∀ j ∈ List.range 6, Perm.sign (tau j) = 1) ∧
      ∀ l ∈ List.range 4, WordOK [0, 1] (tau (l + 2)) (w12.getD l [])) ∧
    ∀ l ∈ List.range 4, WordOK [l + 2] (tau 0) ((wj.getD l []).getD 0 []) ∧
      WordOK [l + 2] (tau 1) ((wj.getD l []).getD 1 []) := by
  have h : chkWords () = true := Certificates.certificate517601.2.2.1
  simpa only [chkWords, Bool.and_eq_true, decide_eq_true_eq] using h

theorem par_tree :
    (treeElt 0 = 1 ∧ treeP.length = 191 ∧ ∀ i ∈ List.range 191,
      (treeP.getD i (0, 0)).2 ≤ i ∧ (treeP.getD i (0, 0)).1 < gens.length ∧
        treeElt (i + 1) = genElt (treeP.getD i (0, 0)).1 * treeElt (treeP.getD i (0, 0)).2) ∧
    ∀ σ : Perm (Fin 8), inS0 σ = true → ∃ i ∈ List.range 192, treeElt i = σ := by
  have h : chkTree () = true := Certificates.certificate517601.2.2.2.1
  simpa only [chkTree, Bool.and_eq_true, decide_eq_true_eq] using h

theorem par_vk :
    ((∀ g ∈ gens, g.1 ∈ six ∧ vkPred g.1 (swapsPerm g.2) = true) ∧
      ∀ δ ∈ six, ∀ σ : Perm (Fin 8), vkPred δ σ = true → inS0 σ = true) ∧
    ∀ x y : Fin 8, x ≠ y → ∃ δ ∈ six, x ∈ δ ∧ y ∈ δ := by
  have h : chkVK () = true := Certificates.certificate517601.2.2.2.2.1
  simpa only [chkVK, Bool.and_eq_true, decide_eq_true_eq] using h

theorem par_planes :
    ((((∀ δ ∈ fours (), (dts δ).length = 3 ∧ ∀ σ ∈ dts δ, vkPred δ σ = true) ∧
      ∀ δ ∈ fours (), (∀ σ ∈ dts δ, stabB AE.affinePlanes σ = true) → δ ∈ AE.affinePlanes) ∧
      ∀ δ ∈ fours (), (∀ σ ∈ dts δ, stabB planes2 σ = true) → δ ∈ planes2) ∧
      ∀ δ ∈ AE.affinePlanes, ∃ e ∈ ptab1, e.1 = δ ∧
        stabB AE.affinePlanes (swapsPerm e.2) = true ∧ d0.map (swapsPerm e.2).toEmbedding = δ) ∧
    ∀ δ ∈ planes2, ∃ e ∈ ptab2, e.1 = δ ∧
      stabB planes2 (swapsPerm e.2) = true ∧ d0.map (swapsPerm e.2).toEmbedding = δ := by
  have h : chkPlanes () = true := Certificates.certificate517601.2.2.2.2.2.1
  simpa only [chkPlanes, Bool.and_eq_true, decide_eq_true_eq] using h

theorem par_sym :
    ((∀ α ∈ fours (), ∃ e ∈ tab1, d0.map (swapsPerm e).toEmbedding = α) ∧
      ∀ β ∈ fours (), (d0 ∩ β).card = 2 → ∃ e ∈ tab2,
        d0.map (swapsPerm e).toEmbedding = d0 ∧ b0.map (swapsPerm e).toEmbedding = β) ∧
    ∀ α ∈ fours (), ∀ β ∈ fours (), (symmDiff α β).card = 4 → (α ∩ β).card = 2 := by
  have h : chkSym () = true := Certificates.certificate517601.2.2.2.2.2.2
  simpa only [chkSym, Bool.and_eq_true, decide_eq_true_eq] using h

theorem card_parS0 : Nat.card parS0 = 192 := by
  show Nat.card {σ : Perm (Fin 8) // inS0 σ = true} = 192
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact par_agl.1.1.1

theorem card_stabFamily (F : List (Finset (Fin 8))) :
    Nat.card (AE.stabFamily F) =
      (Finset.univ.filter fun σ : Perm (Fin 8) => stabB F σ = true).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_stabFamily_iff)

theorem card_agl32 : Nat.card AE.agl32 = 1344 :=
  (card_stabFamily _).trans par_agl.1.1.2

theorem card_parAgl2 : Nat.card parAgl2 = 1344 :=
  (card_stabFamily _).trans par_agl.1.2

theorem tau_mem_of_01 {A : Subgroup (Perm (Fin 8))} (hS : parS0 ≤ A) (h0 : tau 0 ∈ A)
    (h1 : tau 1 ∈ A) {j : ℕ} (hj : j < 6) : tau j ∈ A := by
  have ht : ∀ i ∈ [0, 1], tau i ∈ A := by
    intro i hi
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact h0
    · exact h1
  rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h2
  · exact h0
  · exact h1
  · have hw := par_words.1.2 (j - 2) (List.mem_range.mpr (by omega))
    rw [show j - 2 + 2 = j by omega] at hw
    exact wordOK_mem hS ht hw

theorem tau01_of_tau {A : Subgroup (Perm (Fin 8))} (hS : parS0 ≤ A) {j : ℕ} (hj : j < 6)
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) (htj : tau j ∈ A) : tau 0 ∈ A ∧ tau 1 ∈ A := by
  have ht : ∀ i ∈ [j - 2 + 2], tau i ∈ A := by
    intro i hi
    rw [List.mem_singleton.mp hi, show j - 2 + 2 = j by omega]
    exact htj
  obtain ⟨w0, w1⟩ := par_words.2 (j - 2) (List.mem_range.mpr (by omega))
  exact ⟨wordOK_mem hS ht w0, wordOK_mem hS ht w1⟩

theorem parS0_overgroups {A : Subgroup (Perm (Fin 8))} (hS : parS0 ≤ A)
    (hA : A ≤ alternatingGroup (Fin 8)) :
    A = parS0 ∨ A = AE.agl32 ∨ A = parAgl2 ∨ A = alternatingGroup (Fin 8) := by
  obtain ⟨⟨hdc, hdc0⟩, hdc1⟩ := par_dc
  obtain ⟨⟨ht0, ht1, -⟩, -⟩ := par_words.1
  have hagl := par_agl.2
  have key : ∀ σ ∈ A, inS0 σ = false → ∃ j < 6, tau j ∈ A ∧
      ∃ s u : Perm (Fin 8), inS0 s = true ∧ inS0 u = true ∧ σ = s⁻¹ * tau j * u := by
    intro σ hσ hσ0
    rcases hdc σ (Perm.mem_alternatingGroup.mp (hA hσ)) with h | h
    · rw [hσ0] at h
      exact absurd h (by decide)
    · obtain ⟨j, hj, s, u, hs, hu, he⟩ := dcWit_spec h
      exact ⟨j, hj, tau_mem_of_dc hS hs hu he hσ, s, u, hs, hu, he⟩
  have hS1 : parS0 ≤ AE.agl32 := fun σ hσ => mem_stabFamily_iff.mpr (hagl σ hσ).1
  have hS2 : parS0 ≤ parAgl2 := fun σ hσ => mem_stabFamily_iff.mpr (hagl σ hσ).2
  by_cases h0 : tau 0 ∈ A <;> by_cases h1 : tau 1 ∈ A
  ·
    right; right; right
    refine le_antisymm hA fun σ hσ => ?_
    rcases hdc σ (Perm.mem_alternatingGroup.mp hσ) with h | h
    · exact hS h
    · obtain ⟨j, hj, s, u, hs, hu, he⟩ := dcWit_spec h
      exact mem_of_dc hS hs hu he (tau_mem_of_01 hS h0 h1 hj)
  ·
    right; left
    refine le_antisymm (fun σ hσ => ?_) (fun σ hσ => ?_)
    · cases hσ0 : inS0 σ
      · obtain ⟨j, hj, htj, s, u, hs, hu, he⟩ := key σ hσ hσ0
        have hj0 : j = 0 := by
          by_contra hj0
          by_cases hj1 : j = 1
          · exact h1 (hj1 ▸ htj)
          · exact h1 (tau01_of_tau hS hj hj0 hj1 htj).2
        subst hj0
        exact mem_of_dc hS1 hs hu he (mem_stabFamily_iff.mpr ht0)
      · exact hS1 hσ0
    · rcases hdc0 σ (mem_stabFamily_iff.mp hσ) with h | h
      · exact hS h
      · obtain ⟨s, u, hs, hu, he⟩ := dcWitJ_spec h
        exact mem_of_dc hS hs hu he h0
  ·
    right; right; left
    refine le_antisymm (fun σ hσ => ?_) (fun σ hσ => ?_)
    · cases hσ0 : inS0 σ
      · obtain ⟨j, hj, htj, s, u, hs, hu, he⟩ := key σ hσ hσ0
        have hj1 : j = 1 := by
          by_contra hj1
          by_cases hj0 : j = 0
          · exact h0 (hj0 ▸ htj)
          · exact h0 (tau01_of_tau hS hj hj0 hj1 htj).1
        subst hj1
        exact mem_of_dc hS2 hs hu he (mem_stabFamily_iff.mpr ht1)
      · exact hS2 hσ0
    · rcases hdc1 σ (mem_stabFamily_iff.mp hσ) with h | h
      · exact hS h
      · obtain ⟨s, u, hs, hu, he⟩ := dcWitJ_spec h
        exact mem_of_dc hS hs hu he h1
  ·
    left
    refine le_antisymm (fun σ hσ => ?_) hS
    cases hσ0 : inS0 σ
    · obtain ⟨j, hj, htj, -⟩ := key σ hσ hσ0
      exfalso
      by_cases hj0 : j = 0
      · exact h0 (hj0 ▸ htj)
      by_cases hj1 : j = 1
      · exact h1 (hj1 ▸ htj)
      exact h0 (tau01_of_tau hS hj hj0 hj1 htj).1
    · exact hσ0

theorem exists_perm_of_tree {G : Type*} [Group G] (p : G →* Perm (Fin 8)) {H : Subgroup G}
    (hgen : ∀ g ∈ gens, ∃ a ∈ H, p a = swapsPerm g.2) :
    ∀ σ : Perm (Fin 8), inS0 σ = true → ∃ a ∈ H, p a = σ := by
  obtain ⟨⟨h0, -, hstep⟩, hall⟩ := par_tree
  have hi : ∀ i, i ≤ 191 → ∃ a ∈ H, p a = treeElt i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases i with _ | k
      · exact ⟨1, H.one_mem, by rw [map_one, h0]⟩
      · obtain ⟨hp, hg, he⟩ := hstep k (List.mem_range.mpr (by omega))
        obtain ⟨b, hb, hbp⟩ := ih (treeP.getD k (0, 0)).2 (by omega) (by omega)
        have hmem : gens.getD (treeP.getD k (0, 0)).1 (∅, []) ∈ gens := by
          rw [← List.getElem_eq_getD (h := hg)]
          exact List.getElem_mem hg
        obtain ⟨c, hc, hcp⟩ := hgen _ hmem
        refine ⟨c * b, H.mul_mem hc hb, ?_⟩
        rw [map_mul, hcp, hbp, he]
        rfl
  intro σ hσ
  obtain ⟨i, hi', rfl⟩ := hall σ hσ
  exact hi i (by have := List.mem_range.mp hi'; omega)

theorem vkPred_dts {δ : Finset (Fin 8)} (h : δ.card = 4) : ∀ σ ∈ dts δ, vkPred δ σ = true :=
  (par_planes.1.1.1.1 δ (mem_fours h)).2

theorem mem_affinePlanes_of_dts {δ : Finset (Fin 8)} (h : δ.card = 4)
    (hd : ∀ σ ∈ dts δ, σ ∈ AE.agl32) : δ ∈ AE.affinePlanes :=
  par_planes.1.1.1.2 δ (mem_fours h) fun σ hσ => mem_stabFamily_iff.mp (hd σ hσ)

theorem mem_planes2_of_dts {δ : Finset (Fin 8)} (h : δ.card = 4)
    (hd : ∀ σ ∈ dts δ, σ ∈ parAgl2) : δ ∈ planes2 :=
  par_planes.1.1.2 δ (mem_fours h) fun σ hσ => mem_stabFamily_iff.mp (hd σ hσ)

theorem exists_plane_perm1 {δ : Finset (Fin 8)} (hδ : δ ∈ AE.affinePlanes) :
    ∃ ρ ∈ AE.agl32, d0.map ρ.toEmbedding = δ := by
  obtain ⟨e, -, -, he1, he2⟩ := par_planes.1.2 δ hδ
  exact ⟨swapsPerm e.2, mem_stabFamily_iff.mpr he1, he2⟩

theorem exists_plane_perm2 {δ : Finset (Fin 8)} (hδ : δ ∈ planes2) :
    ∃ ρ ∈ parAgl2, d0.map ρ.toEmbedding = δ := by
  obtain ⟨e, -, -, he1, he2⟩ := par_planes.2 δ hδ
  exact ⟨swapsPerm e.2, mem_stabFamily_iff.mpr he1, he2⟩

theorem card_inter_of_symmDiff {α β : Finset (Fin 8)} (hα : α.card = 4) (hβ : β.card = 4)
    (h : (symmDiff α β).card = 4) : (α ∩ β).card = 2 :=
  par_sym.2 α (mem_fours hα) β (mem_fours hβ) h

theorem exists_perm_d0_b0 {α β : Finset (Fin 8)} (hα : α.card = 4) (hβ : β.card = 4)
    (hαβ : (α ∩ β).card = 2) :
    ∃ σ : Perm (Fin 8), d0.map σ.toEmbedding = α ∧ b0.map σ.toEmbedding = β := by
  obtain ⟨⟨h1, h2⟩, -⟩ := par_sym
  obtain ⟨e1, -, he1⟩ := h1 α (mem_fours hα)
  set σ₁ := swapsPerm e1
  set β' := β.map σ₁.symm.toEmbedding with hβ'def
  have hβ'β : β'.map σ₁.toEmbedding = β := by
    ext x
    simp [hβ'def, Finset.mem_map_equiv]
  have hβ' : β'.card = 4 := (Finset.card_map _).trans hβ
  have hcard : (d0 ∩ β').card = 2 := by
    rw [← Finset.card_map σ₁.toEmbedding, Finset.map_inter, he1, hβ'β, hαβ]
  obtain ⟨e2, -, he2a, he2b⟩ := h2 β' (mem_fours hβ') hcard
  refine ⟨σ₁ * swapsPerm e2, ?_, ?_⟩
  · rw [map_perm_mul, he2a, he1]
  · rw [map_perm_mul, he2b, hβ'β]

end Checks

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
