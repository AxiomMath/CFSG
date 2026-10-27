module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

@[expose] noncomputable def ae6LetterSub (A : Set (Fin 8)) : Subgroup AE6Om :=
  Subgroup.closure (A6.curtisGen '' A)

@[expose] def ae6ULetters : Finset (Fin 8) := {0, 2, 4, 6}

@[expose] noncomputable def ae6ModelU : Subgroup AE6Om := ae6LetterSub ↑ae6ULetters

@[expose] def ae6VertexLetters (k : Fin 3) : Finset (Fin 8) := Finset.univ.filter fun i => i ≠ ae6Omit k

@[expose] def ae6EdgeLetters (k l : Fin 3) : Finset (Fin 8) :=
  Finset.univ.filter fun i => i ≠ ae6Omit k ∧ i ≠ ae6Omit l

@[expose] def ae6VertexSwap : Fin 3 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 2, 3, 4, 5, 0, 1], ![4, 5, 2, 3, 0, 1, 6, 7]]

@[expose] def ae6EdgeSwap : Fin 3 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 6, 7, 4, 5], ![4, 5, 2, 3, 0, 1, 6, 7], ![6, 7, 2, 3, 4, 5, 0, 1]]

@[expose] def ae6CosetWordsV0 : List (List (Fin 8)) :=
  [[], [3], [5], [7], [3, 2], [3, 5], [3, 7], [5, 3], [5, 4], [5, 7], [7, 3], [7, 6], [3, 2, 5], [3, 2, 7],
    [3, 5, 3], [3, 5, 4], [3, 5, 7], [3, 7, 3], [3, 7, 6], [5, 3, 2], [5, 3, 4], [5, 3, 5], [5, 3, 7], [5, 4, 7],
    [5, 7, 3], [5, 7, 6], [7, 3, 2], [7, 3, 5], [7, 3, 6], [7, 3, 7], [3, 2, 5, 3], [3, 2, 5, 4], [3, 2, 5, 7],
    [3, 2, 7, 3], [3, 2, 7, 6], [3, 5, 3, 2], [3, 5, 3, 4], [3, 5, 3, 7], [3, 5, 4, 7], [3, 5, 7, 3], [3, 5, 7, 6],
    [3, 7, 3, 2], [3, 7, 3, 5], [3, 7, 3, 6], [5, 3, 2, 7], [5, 3, 4, 2], [5, 3, 4, 7], [5, 3, 5, 7], [5, 3, 7, 3],
    [5, 3, 7, 6], [5, 4, 7, 3], [5, 4, 7, 6], [5, 7, 3, 2], [5, 7, 3, 5], [5, 7, 3, 6], [5, 7, 3, 7], [7, 3, 2, 5],
    [7, 3, 5, 3], [7, 3, 5, 4], [7, 3, 5, 6], [7, 3, 5, 7], [7, 3, 6, 2], [3, 2, 5, 3, 4], [3, 2, 5, 3, 7],
    [3, 2, 5, 4, 7], [3, 2, 5, 7, 3], [3, 2, 5, 7, 6], [3, 2, 7, 3, 5], [3, 2, 7, 3, 6], [3, 5, 3, 2, 7],
    [3, 5, 3, 4, 2], [3, 5, 3, 4, 7], [3, 5, 3, 7, 3], [3, 5, 3, 7, 6], [3, 5, 4, 7, 3], [3, 5, 4, 7, 6],
    [3, 5, 7, 3, 2], [3, 5, 7, 3, 5], [3, 5, 7, 3, 6], [3, 5, 7, 3, 7], [3, 7, 3, 2, 5], [3, 7, 3, 5, 3],
    [3, 7, 3, 5, 4], [3, 7, 3, 5, 6], [3, 7, 3, 6, 2], [5, 3, 2, 7, 3], [5, 3, 2, 7, 6], [5, 3, 4, 2, 7],
    [5, 3, 4, 7, 3], [5, 3, 4, 7, 6], [5, 3, 5, 7, 3], [5, 3, 5, 7, 6], [5, 3, 7, 3, 2], [5, 3, 7, 3, 5],
    [5, 3, 7, 3, 6], [5, 4, 7, 3, 2], [5, 4, 7, 3, 5], [5, 4, 7, 3, 6], [5, 4, 7, 3, 7], [5, 7, 3, 2, 5],
    [5, 7, 3, 5, 3], [5, 7, 3, 5, 6], [5, 7, 3, 5, 7], [5, 7, 3, 6, 2], [7, 3, 2, 5, 4], [7, 3, 5, 3, 6],
    [7, 3, 5, 3, 7], [7, 3, 5, 4, 6], [7, 3, 5, 4, 7], [7, 3, 5, 6, 2], [7, 3, 5, 7, 3], [3, 2, 5, 3, 4, 2],
    [3, 2, 5, 3, 4, 7], [3, 2, 5, 3, 7, 3], [3, 2, 5, 3, 7, 6], [3, 2, 5, 4, 7, 3], [3, 2, 5, 4, 7, 6],
    [3, 2, 5, 7, 3, 2], [3, 2, 5, 7, 3, 5], [3, 2, 5, 7, 3, 6], [3, 2, 5, 7, 3, 7], [3, 2, 7, 3, 5, 3],
    [3, 2, 7, 3, 5, 4], [3, 2, 7, 3, 5, 6], [3, 2, 7, 3, 6, 2], [3, 5, 3, 2, 7, 3], [3, 5, 3, 2, 7, 6],
    [3, 5, 3, 4, 2, 7], [3, 5, 3, 4, 7, 3], [3, 5, 3, 4, 7, 6], [3, 5, 3, 7, 3, 2], [3, 5, 3, 7, 3, 5],
    [3, 5, 3, 7, 3, 6], [3, 5, 3, 7, 3, 7], [3, 5, 4, 7, 3, 2], [3, 5, 4, 7, 3, 5], [3, 5, 4, 7, 3, 6],
    [3, 5, 4, 7, 3, 7], [3, 5, 7, 3, 5, 3], [3, 5, 7, 3, 5, 6], [3, 5, 7, 3, 5, 7], [3, 5, 7, 3, 6, 2],
    [3, 7, 3, 2, 5, 3], [3, 7, 3, 2, 5, 4], [3, 7, 3, 5, 3, 2], [3, 7, 3, 5, 3, 6], [3, 7, 3, 5, 3, 7],
    [3, 7, 3, 5, 4, 6], [3, 7, 3, 5, 6, 2], [5, 3, 2, 7, 3, 5], [5, 3, 2, 7, 3, 6], [5, 3, 4, 2, 7, 3],
    [5, 3, 4, 2, 7, 6], [5, 3, 4, 7, 3, 2], [5, 3, 4, 7, 3, 5], [5, 3, 4, 7, 3, 6], [5, 3, 5, 7, 3, 5],
    [5, 3, 5, 7, 3, 6], [5, 3, 7, 3, 2, 5], [5, 3, 7, 3, 5, 3], [5, 3, 7, 3, 5, 4], [5, 3, 7, 3, 5, 6],
    [5, 3, 7, 3, 6, 2], [5, 4, 7, 3, 2, 5], [5, 4, 7, 3, 5, 6], [5, 4, 7, 3, 5, 7], [5, 4, 7, 3, 6, 2],
    [5, 7, 3, 2, 5, 4], [5, 7, 3, 5, 3, 6], [5, 7, 3, 5, 3, 7], [5, 7, 3, 5, 6, 2], [7, 3, 5, 3, 6, 7],
    [7, 3, 5, 3, 7, 3], [7, 3, 5, 3, 7, 6], [7, 3, 5, 4, 7, 3], [7, 3, 5, 6, 2, 4], [3, 2, 5, 3, 4, 2, 7],
    [3, 2, 5, 3, 4, 7, 3], [3, 2, 5, 3, 4, 7, 6], [3, 2, 5, 3, 7, 3, 5], [3, 2, 5, 3, 7, 3, 6],
    [3, 2, 5, 4, 7, 3, 2], [3, 2, 5, 4, 7, 3, 5], [3, 2, 5, 4, 7, 3, 6], [3, 2, 5, 4, 7, 3, 7],
    [3, 2, 5, 7, 3, 5, 6], [3, 2, 5, 7, 3, 5, 7], [3, 2, 5, 7, 3, 6, 2], [3, 2, 7, 3, 5, 3, 6],
    [3, 2, 7, 3, 5, 3, 7], [3, 2, 7, 3, 5, 4, 6], [3, 2, 7, 3, 5, 6, 2], [3, 5, 3, 2, 7, 3, 5],
    [3, 5, 3, 2, 7, 3, 6], [3, 5, 3, 4, 2, 7, 3], [3, 5, 3, 4, 2, 7, 6], [3, 5, 3, 4, 7, 3, 2],
    [3, 5, 3, 4, 7, 3, 5], [3, 5, 3, 4, 7, 3, 6], [3, 5, 3, 7, 3, 2, 4], [3, 5, 3, 7, 3, 2, 5],
    [3, 5, 3, 7, 3, 5, 6], [3, 5, 3, 7, 3, 5, 7], [3, 5, 3, 7, 3, 6, 2], [3, 5, 4, 7, 3, 2, 5],
    [3, 5, 4, 7, 3, 5, 6], [3, 5, 4, 7, 3, 5, 7], [3, 5, 4, 7, 3, 6, 2], [3, 5, 7, 3, 5, 3, 6],
    [3, 5, 7, 3, 5, 3, 7], [3, 5, 7, 3, 5, 6, 2], [3, 7, 3, 2, 5, 3, 4], [3, 7, 3, 5, 3, 2, 6],
    [3, 7, 3, 5, 3, 2, 7], [3, 7, 3, 5, 3, 6, 7], [3, 7, 3, 5, 6, 2, 4], [5, 3, 2, 7, 3, 5, 3],
    [5, 3, 2, 7, 3, 5, 4], [5, 3, 2, 7, 3, 5, 6], [5, 3, 2, 7, 3, 6, 2], [5, 3, 4, 2, 7, 3, 5],
    [5, 3, 4, 2, 7, 3, 6], [5, 3, 4, 7, 3, 2, 5], [5, 3, 4, 7, 3, 5, 3], [5, 3, 4, 7, 3, 5, 4],
    [5, 3, 4, 7, 3, 5, 6], [5, 3, 4, 7, 3, 6, 2], [5, 3, 5, 7, 3, 5, 3], [5, 3, 5, 7, 3, 5, 4],
    [5, 3, 5, 7, 3, 5, 6], [5, 3, 5, 7, 3, 6, 2], [5, 3, 7, 3, 2, 5, 4], [5, 3, 7, 3, 5, 3, 2],
    [5, 3, 7, 3, 5, 3, 6], [5, 3, 7, 3, 5, 3, 7], [5, 3, 7, 3, 5, 4, 6], [5, 3, 7, 3, 5, 6, 2],
    [5, 4, 7, 3, 2, 5, 4], [5, 4, 7, 3, 5, 6, 2], [5, 4, 7, 3, 5, 7, 3], [5, 7, 3, 5, 6, 2, 4],
    [7, 3, 5, 3, 6, 7, 3], [7, 3, 5, 3, 7, 3, 2], [7, 3, 5, 4, 7, 3, 2], [3, 2, 5, 3, 4, 2, 7, 3],
    [3, 2, 5, 3, 4, 2, 7, 6], [3, 2, 5, 3, 4, 7, 3, 5], [3, 2, 5, 3, 4, 7, 3, 6], [3, 2, 5, 3, 7, 3, 5, 6],
    [3, 2, 5, 3, 7, 3, 6, 2], [3, 2, 5, 4, 7, 3, 2, 5], [3, 2, 5, 4, 7, 3, 5, 6], [3, 2, 5, 4, 7, 3, 5, 7],
    [3, 2, 5, 4, 7, 3, 6, 2], [3, 2, 5, 7, 3, 5, 6, 2], [3, 2, 7, 3, 5, 3, 6, 7], [3, 2, 7, 3, 5, 6, 2, 4],
    [3, 5, 3, 2, 7, 3, 6, 2], [3, 5, 3, 4, 2, 7, 3, 5], [3, 5, 3, 4, 2, 7, 3, 6], [3, 5, 3, 4, 7, 3, 5, 6],
    [3, 5, 3, 4, 7, 3, 6, 2], [3, 5, 3, 7, 3, 2, 4, 5], [3, 5, 3, 7, 3, 2, 5, 4], [3, 5, 3, 7, 3, 5, 6, 2],
    [3, 5, 4, 7, 3, 2, 5, 4], [3, 5, 4, 7, 3, 5, 6, 2], [3, 5, 7, 3, 5, 6, 2, 4], [3, 7, 3, 5, 3, 2, 6, 7],
    [5, 3, 2, 7, 3, 5, 4, 2], [5, 3, 2, 7, 3, 5, 4, 6], [5, 3, 2, 7, 3, 5, 6, 2], [5, 3, 4, 2, 7, 3, 5, 3],
    [5, 3, 4, 2, 7, 3, 5, 6], [5, 3, 4, 2, 7, 3, 6, 2], [5, 3, 4, 7, 3, 5, 3, 2], [5, 3, 4, 7, 3, 5, 3, 6],
    [5, 3, 4, 7, 3, 5, 6, 2], [5, 3, 5, 7, 3, 5, 4, 6], [5, 3, 5, 7, 3, 5, 6, 2], [5, 3, 7, 3, 5, 6, 2, 4],
    [5, 4, 7, 3, 5, 6, 2, 4], [7, 3, 5, 3, 6, 7, 3, 2], [3, 2, 5, 3, 4, 2, 7, 3, 5], [3, 2, 5, 3, 4, 2, 7, 3, 6],
    [3, 2, 5, 3, 4, 7, 3, 5, 6], [3, 2, 5, 3, 4, 7, 3, 6, 2], [3, 2, 5, 3, 7, 3, 5, 6, 2],
    [3, 2, 5, 4, 7, 3, 5, 6, 2], [3, 2, 5, 7, 3, 5, 6, 2, 4], [3, 5, 3, 4, 2, 7, 3, 5, 6],
    [3, 5, 3, 4, 2, 7, 3, 6, 2], [3, 5, 3, 4, 7, 3, 5, 6, 2], [3, 5, 3, 7, 3, 5, 6, 2, 4],
    [3, 5, 4, 7, 3, 5, 6, 2, 4], [5, 3, 2, 7, 3, 5, 4, 2, 6], [5, 3, 2, 7, 3, 5, 6, 2, 4],
    [5, 3, 4, 2, 7, 3, 5, 3, 6], [5, 3, 4, 2, 7, 3, 5, 6, 2], [5, 3, 4, 7, 3, 5, 3, 2, 6],
    [5, 3, 4, 7, 3, 5, 6, 2, 4], [5, 3, 5, 7, 3, 5, 6, 2, 4], [7, 3, 5, 3, 6, 7, 3, 2, 4],
    [3, 2, 5, 3, 4, 2, 7, 3, 5, 6], [3, 2, 5, 3, 4, 2, 7, 3, 6, 2], [3, 2, 5, 3, 4, 7, 3, 5, 6, 2],
    [3, 2, 5, 3, 7, 3, 5, 6, 2, 4], [3, 2, 5, 4, 7, 3, 5, 6, 2, 4], [3, 5, 3, 4, 2, 7, 3, 5, 6, 2],
    [3, 5, 3, 4, 7, 3, 5, 6, 2, 4], [5, 3, 4, 2, 7, 3, 5, 6, 2, 4], [3, 2, 5, 3, 4, 2, 7, 3, 5, 6, 2],
    [3, 2, 5, 3, 4, 7, 3, 5, 6, 2, 4], [3, 5, 3, 4, 2, 7, 3, 5, 6, 2, 4], [3, 2, 5, 3, 4, 2, 7, 3, 5, 6, 2, 4]]

@[expose] def ae6CosetWord (k : Fin 3) (j : Fin 315) : List (Fin 8) :=
  (ae6CosetWordsV0.getD j []).map (ae6VertexSwap k)

@[expose] noncomputable def ae6CosetY (k : Fin 3) (j : Fin 315) : AE6Om := ae6Word (ae6CosetWord k j)

@[expose] def AE6EdgePairsFin : Prop :=
  Nat.card ae6ModelU = 4096 ∧ (∀ k, Nat.card (ae6ModelV k) = 1290240) ∧
    (∀ k (A : Finset (Fin 8)), ae6ULetters ⊆ A → ae6Omit k ∉ A → Nat.card (ae6LetterSub ↑A) = 86016 →
      ∃ l, l ≠ k ∧ A = ae6EdgeLetters k l) ∧
    (∀ k (j : Fin 315) (x : Fin 8), x ≠ ae6Omit k →
      ∃ j' : Fin 315, ae6CosetY k j * A6.curtisGen x * (ae6CosetY k j')⁻¹ ∈ ae6ModelU) ∧
    (∀ k (j : Fin 315), ∀ i ∈ ae6CosetWord k j,
      A6.curtisGen i ∈ ae6ModelU ⊔ Subgroup.zpowers (ae6CosetY k j)) ∧
    ∀ k, ∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6EdgeSwap k i)) r = 1

theorem gen_mem_letterSub {A : Set (Fin 8)} {i : Fin 8} (h : i ∈ A) : A6.curtisGen i ∈ ae6LetterSub A :=
  Subgroup.subset_closure ⟨i, h, rfl⟩

theorem ae6LetterSub_mono {A B : Set (Fin 8)} (h : A ⊆ B) : ae6LetterSub A ≤ ae6LetterSub B :=
  Subgroup.closure_mono (Set.image_mono h)

theorem ae6Word_mem {A : Set (Fin 8)} {w : List (Fin 8)} (h : ∀ i ∈ w, i ∈ A) : ae6Word w ∈ ae6LetterSub A := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact gen_mem_letterSub (h i hi)

theorem ae6ModelV_eq (k : Fin 3) : ae6ModelV k = ae6LetterSub ↑(ae6VertexLetters k) := by
  simp only [ae6ModelV, ae6LetterSub, ae6VertexLetters, Finset.coe_filter, Finset.mem_univ, true_and]

theorem ae6ULetters_subset (k : Fin 3) : ae6ULetters ⊆ ae6VertexLetters k := by
  revert k; decide

theorem ae6ModelU_le (k : Fin 3) : ae6ModelU ≤ ae6ModelV k := by
  rw [ae6ModelV_eq]; exact ae6LetterSub_mono (Finset.coe_subset.mpr (ae6ULetters_subset k))

theorem mem_letterSub_aut {e : MulAut AE6Om} {π : Fin 8 → Fin 8}
    (he : ∀ i, e (A6.curtisGen i) = A6.curtisGen (π i)) (A : Set (Fin 8)) (x : AE6Om) :
    x ∈ ae6LetterSub A ↔ e x ∈ ae6LetterSub (π '' A) := by
  have hmap : (ae6LetterSub A).map e.toMonoidHom = ae6LetterSub (π '' A) := by
    rw [ae6LetterSub, MonoidHom.map_closure, Set.image_image, ae6LetterSub, Set.image_image]
    congr 1
    exact Set.image_congr fun i _ => he i
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm

theorem gen_omit_not_mem {k : Fin 3} (hV : Nat.card (ae6ModelV k) = 1290240) :
    A6.curtisGen (ae6Omit k) ∉ ae6ModelV k := by
  intro hmem
  have htop : ae6ModelV k = ⊤ := by
    rw [eq_top_iff, ← A6.closure_curtisGen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = ae6Omit k
    · rw [hi]; exact hmem
    · exact gen_mem_letterSub hi
  rw [htop, Subgroup.card_top] at hV
  have h2 : Nat.card AE6Om = 174182400 := CFSG.EvenSmallLie.OmegaEight.card_omegaT
  exact absurd (hV.symm.trans h2) (by norm_num)

theorem ae6_cover (h : AE6EdgePairsFin) (k : Fin 3) {g : AE6Om} (hg : g ∈ ae6ModelV k) :
    ∃ j, g * (ae6CosetY k j)⁻¹ ∈ ae6ModelU := by
  have hstep : ∀ x y : AE6Om, y ∈ A6.curtisGen '' {i | i ≠ ae6Omit k} →
      (∃ j, x * (ae6CosetY k j)⁻¹ ∈ ae6ModelU) → ∃ j, x * y * (ae6CosetY k j)⁻¹ ∈ ae6ModelU := by
    rintro x _ ⟨i, hi, rfl⟩ ⟨j, hj⟩
    obtain ⟨j', hj'⟩ := h.2.2.2.1 k j i hi
    refine ⟨j', ?_⟩
    convert mul_mem hj hj' using 1
    group
  have hpow : ∀ x y : AE6Om, y ∈ A6.curtisGen '' {i | i ≠ ae6Omit k} → ∀ n : ℕ,
      (∃ j, x * (ae6CosetY k j)⁻¹ ∈ ae6ModelU) → ∃ j, x * y ^ n * (ae6CosetY k j)⁻¹ ∈ ae6ModelU := by
    intro x y hy n hx
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ, ← mul_assoc]; exact hstep _ _ hy ih
  induction hg using Subgroup.closure_induction_right with
  | one =>
    refine ⟨0, ?_⟩
    have hw : ae6CosetWord k 0 = [] := rfl
    have h0 : ae6CosetY k 0 = 1 := by
      simp only [ae6CosetY, hw, ae6Word, List.map_nil, List.prod_nil]
    rw [h0, inv_one, mul_one]
    exact one_mem _
  | mul_right x _ y hy ih => exact hstep x y hy ih
  | mul_inv_cancel x _ y hy ih =>
    have hy1 : y⁻¹ = y ^ (orderOf y - 1) :=
      (eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul (orderOf_pos y).ne', pow_orderOf_eq_one])).symm
    rw [hy1]
    exact hpow x y hy _ ih

theorem ae6_overgroup (h : AE6EdgePairsFin) (k : Fin 3) {H : Subgroup AE6Om} (hU : ae6ModelU ≤ H)
    (hV : H ≤ ae6ModelV k) :
    ∃ A : Finset (Fin 8), ae6ULetters ⊆ A ∧ (∀ i ∈ A, A6.curtisGen i ∈ H) ∧ H = ae6LetterSub ↑A := by
  classical
  set T := Finset.univ.filter fun j : Fin 315 => ae6CosetY k j ∈ H with hT
  set A : Finset (Fin 8) := ae6ULetters ∪ T.biUnion fun j => (ae6CosetWord k j).toFinset with hA
  have hAH : ∀ i ∈ A, A6.curtisGen i ∈ H := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hU (gen_mem_letterSub (Finset.mem_coe.mpr hi))
    · obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
      have hjH : ae6CosetY k j ∈ H := (Finset.mem_filter.mp hj).2
      exact sup_le hU (Subgroup.zpowers_le.mpr hjH) (h.2.2.2.2.1 k j i (List.mem_toFinset.mp hij))
  refine ⟨A, Finset.subset_union_left, hAH, le_antisymm (fun x hx => ?_) ?_⟩
  · obtain ⟨j, hj⟩ := ae6_cover h k (hV hx)
    have hjH : ae6CosetY k j ∈ H := by
      convert mul_mem (inv_mem (hU hj)) hx using 1
      group
    have hy : ae6CosetY k j ∈ ae6LetterSub ↑A := ae6Word_mem fun i hi =>
      Finset.mem_coe.mpr (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjH⟩, List.mem_toFinset.mpr hi⟩))
    have hu : x * (ae6CosetY k j)⁻¹ ∈ ae6LetterSub ↑A :=
      ae6LetterSub_mono (Finset.coe_subset.mpr Finset.subset_union_left) hj
    convert mul_mem hu hy using 1
    group
  · exact (Subgroup.closure_le _).mpr (by rintro _ ⟨i, hi, rfl⟩; exact hAH i hi)

theorem ae6ModelE_eq (h : AE6EdgePairsFin) (k l : Fin 3) :
    ae6ModelE k l = ae6LetterSub ↑(ae6EdgeLetters k l) := by
  have hle : ∀ k l : Fin 3, ae6EdgeLetters k l ⊆ ae6VertexLetters k := by decide
  have hle' : ∀ k l : Fin 3, ae6EdgeLetters k l ⊆ ae6VertexLetters l := by decide
  obtain ⟨A, -, hA, hEq⟩ :=
    ae6_overgroup h k (le_inf (ae6ModelU_le k) (ae6ModelU_le l)) (inf_le_left : ae6ModelE k l ≤ _)
  have hsub : A ⊆ ae6EdgeLetters k l := by
    intro i hi
    have hi' := hA i hi
    simp only [ae6EdgeLetters, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun e => ?_, fun e => ?_⟩
    · subst e; exact gen_omit_not_mem (h.2.1 k) (Subgroup.mem_inf.mp hi').1
    · subst e; exact gen_omit_not_mem (h.2.1 l) (Subgroup.mem_inf.mp hi').2
  refine le_antisymm (hEq.trans_le (ae6LetterSub_mono (Finset.coe_subset.mpr hsub))) (le_inf ?_ ?_)
  · rw [ae6ModelV_eq]; exact ae6LetterSub_mono (Finset.coe_subset.mpr (hle k l))
  · rw [ae6ModelV_eq]; exact ae6LetterSub_mono (Finset.coe_subset.mpr (hle' k l))

theorem factorization_1290240 : (1290240 : ℕ).factorization 2 = 12 := by
  rw [show (1290240 : ℕ) = 2 ^ 12 * 315 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem ae6_exists_conj_U (h : AE6EdgePairsFin) (k : Fin 3) {D : Subgroup AE6Om} (hD : D ≤ ae6ModelV k)
    (hc : Nat.card D = 12288) : ∃ g ∈ ae6ModelV k, ∀ u ∈ ae6ModelU, ∃ t ∈ D, g * t * g⁻¹ = u := by
  classical
  have hVc : Nat.card (ae6ModelV k) = 1290240 := h.2.1 k
  have hUV := ae6ModelU_le k
  have hD' : Nat.card (D.subgroupOf (ae6ModelV k)) = 12288 := by
    rw [← hc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(D.subgroupOf (ae6ModelV k))) 2 (n := 12)
    (by rw [hD']; norm_num)
  set T : Subgroup ↥(ae6ModelV k) := K.map (D.subgroupOf (ae6ModelV k)).subtype with hTdef
  have hT : Nat.card T = 2 ^ (Nat.card ↥(ae6ModelV k)).factorization 2 := by
    rw [hTdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK, hVc, factorization_1290240]
  have hU' : Nat.card (ae6ModelU.subgroupOf (ae6ModelV k)) = 2 ^ (Nat.card ↥(ae6ModelV k)).factorization 2 := by
    rw [hVc, factorization_1290240, show (2 : ℕ) ^ 12 = 4096 by norm_num, ← h.1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(ae6ModelV k)) (Sylow.ofCard T hT) (Sylow.ofCard _ hU')
  refine ⟨g, g.2, fun u hu => ?_⟩
  have hmem : (⟨u, hUV hu⟩ : ↥(ae6ModelV k)) ∈ ((g • Sylow.ofCard T hT : Sylow 2 _) : Subgroup _) := by
    rw [hg, Sylow.coe_ofCard]
    exact Subgroup.mem_subgroupOf.mpr hu
  rw [Sylow.coe_subgroup_smul, Sylow.coe_ofCard, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨t, ht, hte⟩ := hmem
  obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp ht
  refine ⟨((s : ↥(ae6ModelV k)) : AE6Om), Subgroup.mem_subgroupOf.mp s.2, ?_⟩
  have := congrArg (fun x : ↥(ae6ModelV k) => (x : AE6Om)) hte
  simpa [MulAut.smul_def, MulAut.conj_apply] using this

theorem ae6_aut_of_perm (π : Fin 8 → Fin 8) (hπ : Function.Surjective π)
    (hrel : ∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen (π i)) r = 1) :
    ∃ e : MulAut AE6Om, ∀ i, e (A6.curtisGen i) = A6.curtisGen (π i) := by
  let ψ := MulEquiv.ofBijective _ A6.curtisToGroup_gen_bijective
  let φ := (A6.curtisToGroup hrel).comp ψ.symm.toMonoidHom
  have hgen : Subgroup.closure (Set.range fun i => A6.curtisGen (π i)) = ⊤ := by
    rw [show (Set.range fun i => A6.curtisGen (π i)) = Set.range A6.curtisGen from hπ.range_comp A6.curtisGen]
    exact A6.closure_curtisGen
  have hs : Function.Surjective φ := (A6.curtisToGroup_surjective hrel hgen).comp ψ.symm.surjective
  refine ⟨MulEquiv.ofBijective φ ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, fun i => ?_⟩
  change A6.curtisToGroup hrel (ψ.symm (A6.curtisGen i)) = _
  have : ψ.symm (A6.curtisGen i) = PresentedGroup.of i := by
    rw [MulEquiv.symm_apply_eq]
    exact (A6.curtisToGroup_of A6.curtisGen_rels i).symm
  rw [this, A6.curtisToGroup_of]

theorem ae6_restrict {k : Fin 3} (φ : MulAut AE6Om) (hφ : ∀ x, x ∈ ae6ModelV k ↔ φ x ∈ ae6ModelV k) :
    ∃ β : MulAut ↥(ae6ModelV k), ∀ x : ↥(ae6ModelV k), (β x : AE6Om) = φ x :=
  ⟨{ toFun := fun x => ⟨φ (x : AE6Om), (hφ x).1 x.2⟩
     invFun := fun x => ⟨φ.symm (x : AE6Om), (hφ _).2 (by rw [MulEquiv.apply_symm_apply]; exact x.2)⟩
     left_inv := fun x => Subtype.ext (φ.symm_apply_apply (x : AE6Om))
     right_inv := fun x => Subtype.ext (φ.apply_symm_apply (x : AE6Om))
     map_mul' := fun x y => Subtype.ext (map_mul φ (x : AE6Om) y) }, fun _ => rfl⟩

theorem ae6_restrict_map {k : Fin 3} {φ : MulAut AE6Om} {β : MulAut ↥(ae6ModelV k)}
    (hβ : ∀ x : ↥(ae6ModelV k), (β x : AE6Om) = φ x) {H H' : Subgroup AE6Om} (hH : ∀ x, x ∈ H ↔ φ x ∈ H') :
    (H.subgroupOf (ae6ModelV k)).map β.toMonoidHom = H'.subgroupOf (ae6ModelV k) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (β y : AE6Om) ∈ H'
    rw [hβ]
    exact (hH _).1 hy
  · intro hx
    refine ⟨β.symm x, ?_, β.apply_symm_apply x⟩
    rw [hH, ← hβ, MulEquiv.apply_symm_apply]
    exact hx

theorem fin3_pair_cases : ∀ k l m a b : Fin 3, k ≠ l → k ≠ m → l ≠ m → a ≠ k → b ≠ k → a ≠ b →
    (a = l ∧ b = m) ∨ (a = m ∧ b = l) := by
  decide

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
