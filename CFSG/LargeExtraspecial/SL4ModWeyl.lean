module

public import CFSG.LargeExtraspecial.SL4ModCodes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Native

theorem cosetCheck : ((List.range 3).all fun i => (List.range 64).all fun e =>
    (isUCode (mul4 (mul4 (genCode (i + 3)) (uCode e)) (genCode (i + 3))) &&
        isUCode (mul4 (mul4 (mul4 (mul4 (genCode (i + 3)) (genCode i)) (uCode e)) (genCode i))
          (genCode (i + 3)))) ||
      (isUCode (mul4 (mul4 (mul4 (genCode (i + 3)) (genCode i)) (uCode e)) (genCode (i + 3))) &&
        isUCode (mul4 (mul4 (mul4 (genCode (i + 3)) (uCode e)) (genCode i))
          (genCode (i + 3))))) = true := by
  decide +kernel

theorem coset_cases (i : Fin 3) {u : SL4} (hu : u ∈ U) :
    (nn i * u * nn i ∈ U ∧ nn i * xx i * u * xx i * nn i ∈ U) ∨
      (nn i * xx i * u * nn i ∈ U ∧ nn i * u * xx i * nn i ∈ U) := by
  obtain ⟨e, he, rfl⟩ := exists_uSL hu
  have h := cosetCheck
  rw [List.all_eq_true] at h
  have h' := h i.val (List.mem_range.mpr i.isLt)
  rw [List.all_eq_true] at h'
  have h'' := h' e (List.mem_range.mpr he)
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h''
  have hn : HasCode (nn i) (genCode (i.val + 3)) := hasCode_genN _
  have hx : HasCode (xx i) (genCode i.val) := hasCode_genN _
  have hu' := hasCode_uSL e
  rcases h'' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨((hn.mul hu').mul hn).mem_U h1,
      ((((hn.mul hx).mul hu').mul hx).mul hn).mem_U h2⟩
  · exact Or.inr ⟨(((hn.mul hx).mul hu').mul hn).mem_U h1,
      (((hn.mul hu').mul hx).mul hn).mem_U h2⟩

@[expose] def gList : List ℕ → List SL4
  | [] => [1]
  | i :: ws =>
    (gList ws).map (fun g => genN (i + 3) * g) ++
      (gList ws).map (fun g => genN i * genN (i + 3) * g)

theorem gList_val (ws : List ℕ) :
    (gList ws).map toMat = (gCodeList ws).map (rowsMatrix 4) := by
  induction ws with
  | nil =>
    change [toMat 1] = [rowsMatrix 4 id4]
    rw [show toMat 1 = 1 from rfl, id4, rowsMatrix_idRows]
  | cons i ws ih =>
    simp only [gList, gCodeList, List.map_append, List.map_map]
    have e1 : (toMat ∘ fun g : SL4 => genN (i + 3) * g) =
        (fun A => rowsMatrix 4 (genCode (i + 3)) * A) ∘ toMat := rfl
    have e2 : (toMat ∘ fun g : SL4 => genN i * genN (i + 3) * g) =
        (fun A => rowsMatrix 4 (genCode i) * rowsMatrix 4 (genCode (i + 3)) * A) ∘ toMat := rfl
    have e3 : (rowsMatrix 4 ∘ fun g => mul4 (genCode (i + 3)) g) =
        (fun A => rowsMatrix 4 (genCode (i + 3)) * A) ∘ rowsMatrix 4 := by
      funext g
      simp only [Function.comp_apply, mul4, rowsMatrix_mulRows]
    have e4 : (rowsMatrix 4 ∘ fun g => mul4 (mul4 (genCode i) (genCode (i + 3))) g) =
        (fun A => rowsMatrix 4 (genCode i) * rowsMatrix 4 (genCode (i + 3)) * A) ∘
          rowsMatrix 4 := by
      funext g
      simp only [Function.comp_apply, mul4, rowsMatrix_mulRows]
    rw [e1, e2, e3, e4, ← List.map_map, ← List.map_map (g := fun A => _ * _ * A), ih,
      List.map_map, List.map_map]

theorem gList_length (ws : List ℕ) : (gList ws).length = 2 ^ ws.length := by
  induction ws with
  | nil => rfl
  | cons i ws ih =>
    simp only [gList, List.length_append, List.length_map, ih, List.length_cons, pow_succ]
    ring

@[expose] def w0 : List ℕ := [0, 1, 0, 2, 1, 0]

@[expose] def nw0C : Array ℕ := wordCode [3, 4, 3, 5, 4, 3]

@[expose] def nw0 : SL4 := wordProd [3, 4, 3, 5, 4, 3]

theorem hasCode_nw0 : HasCode nw0 nw0C := hasCode_wordProd _

theorem nw0_mul_self : nw0 * nw0 = 1 :=
  (hasCode_nw0.mul hasCode_nw0).eq hasCode_one (by decide +kernel)

theorem w0Check : (gCodeList w0).all (fun c => isUCode (mul4 c nw0C)) = true := by
  decide +kernel

theorem w0Nodup : ((gCodeList w0).map fun c => uDecC (mul4 c nw0C)).Nodup := by
  decide +kernel

theorem exists_code_of_mem_gList {ws : List ℕ} {g : SL4} (hg : g ∈ gList ws) :
    ∃ c ∈ gCodeList ws, HasCode g c := by
  have : toMat g ∈ (gCodeList ws).map (rowsMatrix 4) := by
    rw [← gList_val]
    exact List.mem_map_of_mem hg
  obtain ⟨c, hc, hcg⟩ := List.mem_map.mp this
  exact ⟨c, hc, hcg.symm⟩

theorem gList_w0_mem {g : SL4} (hg : g ∈ gList w0) : g * nw0 ∈ U := by
  obtain ⟨c, hc, hgc⟩ := exists_code_of_mem_gList hg
  exact (hgc.mul hasCode_nw0).mem_U (List.all_eq_true.mp w0Check c hc)

theorem gList_w0_nodup : ((gList w0).map fun g => g * nw0).Nodup := by
  refine List.Nodup.of_map (fun g : SL4 => uDecM (toMat g)) ?_
  have : ((gList w0).map fun g => g * nw0).map (fun g : SL4 => uDecM (toMat g)) =
      ((gList w0).map toMat).map fun A => uDecM (A * toMat nw0) := by
    rw [List.map_map, List.map_map]
    rfl
  rw [this, gList_val, List.map_map]
  have h2 : ((fun A => uDecM (A * toMat nw0)) ∘ rowsMatrix 4) =
      fun c => uDecC (mul4 c nw0C) := by
    funext c
    simp only [Function.comp_apply]
    rw [hasCode_nw0.toMat_eq, ← rowsMatrix_mulRows, ← mul4, uDecM_rowsMatrix]
  rw [h2]
  exact w0Nodup

theorem sum_U_eq [Fintype U] {M : Type*} [AddCommMonoid M] (F : SL4 → M) :
    ∑ u : U, F u = ((gList w0).map fun g => F (g * nw0)).sum := by
  classical
  set l := (gList w0).map fun g => g * nw0 with hl
  have hlen : l.length = 64 := by rw [hl, List.length_map, gList_length]; rfl
  have hsum : ((gList w0).map fun g => F (g * nw0)).sum = ∑ x ∈ l.toFinset, F x := by
    rw [List.sum_toFinset F gList_w0_nodup, List.map_map]
    rfl
  rw [hsum]
  have hsub : l.toFinset ⊆ Finset.univ.filter (· ∈ U) := by
    intro x hx
    rw [List.mem_toFinset, hl, List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, gList_w0_mem hg⟩
  have hcard : (Finset.univ.filter (· ∈ U)).card ≤ l.toFinset.card := by
    rw [List.toFinset_card_of_nodup gList_w0_nodup, hlen, ← Fintype.card_subtype,
      ← Nat.card_eq_fintype_card, natCard_U]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [heq, Finset.sum_subtype (Finset.univ.filter (· ∈ U)) (p := (· ∈ U))
    (fun x => by simp) F]

end CFSG.LargeExtraspecial.SL4Mod
