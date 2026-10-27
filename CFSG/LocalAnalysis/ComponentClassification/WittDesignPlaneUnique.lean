module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneFrame
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquares
public import CFSG.Monster.B.Classical.PlaneIncidence
public meta import CFSG.Monster.B.Classical.PlaneData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquares
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneUniqueInputs
public import Certificates.Certificate2038
public import Certificates.Certificate2037

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open Equiv CFSG.Monster.B.Classical.Plane

@[expose] def encOpt : Option (Fin 5 × Fin 4) → Fin 21
  | none => 0
  | some (j, x) => enc j x

theorem encOpt_bijective : Function.Bijective encOpt := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by decide⟩

theorem vlineImage_mem : ∀ j : Fin 5,
    insert 0 (Finset.univ.image (enc j)) ∈ Finset.univ.image projLine :=
  Certificates.certificate2038.1

theorem tlineImage_mem : ∀ x y : Fin 4,
    ({enc 0 x, enc 1 y, enc 2 (latinSq rA x y), enc 3 (latinSq rB x y),
      enc 4 (latinSq rC x y)} : Finset (Fin 21)) ∈ Finset.univ.image projLine :=
  Certificates.certificate2038.2

theorem card_image_projLine : (Finset.univ.image projLine).card = 21 := by
  rw [Finset.card_image_of_injective _ projLine_injective, Finset.card_univ, Fintype.card_fin]

variable {P : Type*} [Fintype P] [DecidableEq P] {𝓛 : Finset (Finset P)}

section Squares

variable (h : IsSteinerPlane 𝓛) (p₀ : P)

theorem mu_ne_mu {i j : Fin 5} (hij : i ≠ j) (x y : Fin 4) : mu h p₀ i x ≠ mu h p₀ j y :=
  fun e => hij (eq_of_mem_vpts h p₀ (mu_mem h p₀ i x) (e ▸ mu_mem h p₀ j y))

@[expose] def tline (x y : Fin 4) : Finset P := lineThrough 𝓛 (mu h p₀ 0 x) (mu h p₀ 1 y)

theorem tline_spec (x y : Fin 4) :
    tline h p₀ x y ∈ 𝓛 ∧ p₀ ∉ tline h p₀ x y ∧ mu h p₀ 0 x ∈ tline h p₀ x y ∧
      mu h p₀ 1 y ∈ tline h p₀ x y := by
  obtain ⟨h1, h2, h3⟩ := h.lineThrough_spec (mu_ne_mu h p₀ (i := 0) (j := 1) (by decide) x y)
  exact ⟨h1, p₀_not_mem_lineThrough h p₀ (by decide) (mu_mem h p₀ 0 x) (mu_mem h p₀ 1 y), h2, h3⟩

@[expose] def lsq (j : Fin 5) (x y : Fin 4) : Fin 4 :=
  (muEquiv h p₀ j).symm ⟨meetPoint (tline h p₀ x y) (vline h p₀ j) p₀,
    (meetPoint_mem_vpts h p₀ (tline_spec h p₀ x y).1 (tline_spec h p₀ x y).2.1 j).2⟩

theorem mu_lsq_mem (j : Fin 5) (x y : Fin 4) : mu h p₀ j (lsq h p₀ j x y) ∈ tline h p₀ x y := by
  rw [lsq, mu_muEquiv_symm]
  exact (meetPoint_mem_vpts h p₀ (tline_spec h p₀ x y).1 (tline_spec h p₀ x y).2.1 j).1

theorem eq_lsq {j : Fin 5} {x y z : Fin 4} (hz : mu h p₀ j z ∈ tline h p₀ x y) :
    z = lsq h p₀ j x y := by
  obtain ⟨hM, hp, -, -⟩ := tline_spec h p₀ x y
  have h1 := h.eq_meetPoint hM (vline_mem h p₀ j) (ne_vline_of_not_mem h p₀ hp j) p₀ hz
    (mem_vline_of_mem_vpts h p₀ (mu_mem h p₀ j z))
  apply mu_injective h p₀ j
  rw [h1, lsq, mu_muEquiv_symm]

theorem lsq_zero_left (x y : Fin 4) : lsq h p₀ 0 x y = x :=
  (eq_lsq h p₀ (tline_spec h p₀ x y).2.2.1).symm

theorem lsq_one_left (x y : Fin 4) : lsq h p₀ 1 x y = y :=
  (eq_lsq h p₀ (tline_spec h p₀ x y).2.2.2).symm

theorem tline_eq {x y x' y' : Fin 4} {i j : Fin 5} (hij : i ≠ j) {a b : Fin 4}
    (ha : mu h p₀ i a ∈ tline h p₀ x y) (ha' : mu h p₀ i a ∈ tline h p₀ x' y')
    (hb : mu h p₀ j b ∈ tline h p₀ x y) (hb' : mu h p₀ j b ∈ tline h p₀ x' y') :
    x = x' ∧ y = y' := by
  have heq := h.eq_of_mem_of_mem (tline_spec h p₀ x y).1 (tline_spec h p₀ x' y').1
    (mu_ne_mu h p₀ hij a b) ha hb ha' hb'
  refine ⟨?_, ?_⟩
  · rw [← lsq_zero_left h p₀ x y, ← lsq_zero_left h p₀ x' y']
    exact eq_lsq h p₀ (heq ▸ mu_lsq_mem h p₀ 0 x y)
  · rw [← lsq_one_left h p₀ x y, ← lsq_one_left h p₀ x' y']
    exact eq_lsq h p₀ (heq ▸ mu_lsq_mem h p₀ 1 x y)

theorem lsq_row_injective {j : Fin 5} (hj : j ≠ 0) (x : Fin 4) :
    Function.Injective (lsq h p₀ j x) := by
  intro y y' e
  have h1 := mu_lsq_mem h p₀ j x y
  have h2 := mu_lsq_mem h p₀ j x y'
  rw [← e] at h2
  exact (tline_eq h p₀ (Ne.symm hj) (tline_spec h p₀ x y).2.2.1 (tline_spec h p₀ x y').2.2.1
    h1 h2).2

theorem lsq_col_injective {j : Fin 5} (hj : j ≠ 1) (y : Fin 4) :
    Function.Injective fun x => lsq h p₀ j x y := by
  intro x x' e
  have h1 := mu_lsq_mem h p₀ j x y
  have h2 := mu_lsq_mem h p₀ j x' y
  simp only at e
  rw [← e] at h2
  exact (tline_eq h p₀ (Ne.symm hj) (tline_spec h p₀ x y).2.2.2 (tline_spec h p₀ x' y).2.2.2
    h1 h2).1

theorem lsq_orth {j k : Fin 5} (hjk : j ≠ k) : Orth (lsq h p₀ j) (lsq h p₀ k) := by
  intro x y x' y' e1 e2
  have h1 := mu_lsq_mem h p₀ j x y
  have h2 := mu_lsq_mem h p₀ j x' y'
  have h3 := mu_lsq_mem h p₀ k x y
  have h4 := mu_lsq_mem h p₀ k x' y'
  rw [← e1] at h2
  rw [← e2] at h4
  exact tline_eq h p₀ hjk h1 h2 h3 h4

theorem mu_zero_zero : mu h p₀ 0 0 = o₀ h p₀ := by
  obtain ⟨hM, hpM⟩ := lineThrough_o₀_spec h p₀ 0
  have hne : μ₁ h p₀ 0 ≠ muAux h p₀ 2 0 := fun e =>
    absurd (eq_of_mem_vpts h p₀ (μ₁_mem h p₀ 0) (e ▸ (muAux_spec h p₀ 2 0).2)) (by decide)
  have hneo : o₀ h p₀ ≠ μ₁ h p₀ 0 := fun e =>
    absurd (eq_of_mem_vpts h p₀ (o₀_mem h p₀) (e ▸ μ₁_mem h p₀ 0)) (by decide)
  have heq := h.eq_lineThrough hne hM (h.lineThrough_spec hneo).2.2 (muAux_spec h p₀ 2 0).1
  rw [mu_zero, ← heq]
  exact (h.eq_meetPoint hM (vline_mem h p₀ 0) (ne_vline_of_not_mem h p₀ hpM 0) p₀
    (h.lineThrough_spec hneo).2.1 (mem_vline_of_mem_vpts h p₀ (o₀_mem h p₀))).symm

theorem lsq_zero_row {j : Fin 5} (hj0 : j ≠ 0) (y : Fin 4) : lsq h p₀ j 0 y = y := by
  by_cases hj1 : j = 1
  · rw [hj1, lsq_one_left]
  have hmem : mu h p₀ j y ∈ tline h p₀ 0 y := by
    have htl : tline h p₀ 0 y = lineThrough 𝓛 (o₀ h p₀) (μ₁ h p₀ y) := by
      rw [tline, mu_zero_zero, mu_one]
    rw [htl, mu_of_two_le h p₀ hj0 hj1]
    exact (muAux_spec h p₀ j y).1
  exact (eq_lsq h p₀ hmem).symm

theorem lsq_two_col (x : Fin 4) : lsq h p₀ 2 x 0 = x := by
  obtain ⟨hM, -, h1M, h2M⟩ := lineThrough_μ₁_spec h p₀ x
  have hne : mu h p₀ 0 x ≠ mu h p₀ 1 0 := mu_ne_mu h p₀ (i := 0) (j := 1) (by decide) x 0
  have heq : lineThrough 𝓛 (μ₁ h p₀ 0) (muAux h p₀ 2 x) = tline h p₀ x 0 :=
    h.eq_lineThrough hne hM (mu_zero_spec h p₀ x).1 (by rw [mu_one]; exact h1M)
  have hmem : mu h p₀ 2 x ∈ tline h p₀ x 0 := by
    rw [mu_of_two_le h p₀ (by decide) (by decide), ← heq]
    exact h2M
  exact (eq_lsq h p₀ hmem).symm

@[expose] def rowPerms {j : Fin 5} (hj : j ≠ 0) (i : Fin 3) : Perm (Fin 4) :=
  Equiv.ofBijective (lsq h p₀ j i.succ)
    ((Finite.injective_iff_bijective).1 (lsq_row_injective h p₀ hj i.succ))

theorem latinSq_rowPerms {j : Fin 5} (hj : j ≠ 0) : latinSq (rowPerms h p₀ hj) = lsq h p₀ j := by
  funext x y
  by_cases hx : (x : ℕ) = 0
  · have : x = 0 := Fin.ext hx
    rw [latinSq, dite_eq_left hx, this, lsq_zero_row h p₀ hj]
  · rw [latinSq, dite_eq_right hx]
    change lsq h p₀ j (Fin.succ ⟨x - 1, by omega⟩) y = lsq h p₀ j x y
    congr 1
    ext
    simp
    omega

theorem columnsInj_lsq {j : Fin 5} (hj : j ≠ 1) : ColumnsInj (lsq h p₀ j) :=
  fun y _ _ e => lsq_col_injective h p₀ hj y e

theorem lsq_cases :
    (lsq h p₀ 2 = latinSq rA ∧ lsq h p₀ 3 = latinSq rB ∧ lsq h p₀ 4 = latinSq rC) ∨
      (lsq h p₀ 2 = latinSq rA ∧ lsq h p₀ 3 = latinSq rC ∧ lsq h p₀ 4 = latinSq rB) := by
  have h2 := latinSq_rowPerms h p₀ (j := 2) (by decide)
  have h3 := latinSq_rowPerms h p₀ (j := 3) (by decide)
  have h4 := latinSq_rowPerms h p₀ (j := 4) (by decide)
  have hcol : ∀ x : Fin 3, rowPerms h p₀ (j := 2) (by decide) x 0 = x.succ := fun x =>
    lsq_two_col h p₀ x.succ
  have hc : ∀ j : Fin 5, j ≠ 1 → ColumnsInj (lsq h p₀ j) := fun j hj => columnsInj_lsq h p₀ hj
  rcases mols_classification _ _ _ hcol (h2 ▸ hc 2 (by decide)) (h3 ▸ hc 3 (by decide))
    (h4 ▸ hc 4 (by decide)) (h2 ▸ h3 ▸ lsq_orth h p₀ (by decide))
    (h2 ▸ h4 ▸ lsq_orth h p₀ (by decide)) (h3 ▸ h4 ▸ lsq_orth h p₀ (by decide)) with
    ⟨e2, e3, e4⟩ | ⟨e2, e3, e4⟩
  · left
    rw [← h2, ← h3, ← h4, e2, e3, e4]
    exact ⟨rfl, rfl, rfl⟩
  · right
    rw [← h2, ← h3, ← h4, e2, e3, e4]
    exact ⟨rfl, rfl, rfl⟩

@[expose] def coordPt : Option (Fin 5 × Fin 4) → P
  | none => p₀
  | some (j, x) => mu h p₀ j x

theorem coordPt_bijective : Function.Bijective (coordPt h p₀) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by rw [h.card_points]; decide⟩
  rintro (_ | ⟨j, x⟩) (_ | ⟨k, y⟩) e
  · rfl
  · exact absurd e.symm (ne_p₀_of_mem_vpts h p₀ (mu_mem h p₀ k y))
  · exact absurd e (ne_p₀_of_mem_vpts h p₀ (mu_mem h p₀ j x))
  · change mu h p₀ j x = mu h p₀ k y at e
    have hjk : j = k := eq_of_mem_vpts h p₀ (mu_mem h p₀ j x) (e ▸ mu_mem h p₀ k y)
    subst hjk
    rw [mu_injective h p₀ j e]

theorem vline_eq_image (j : Fin 5) :
    vline h p₀ j = (insert none (Finset.univ.image fun x => some (j, x))).image (coordPt h p₀) := by
  rw [Finset.image_insert, Finset.image_image]
  have hv : vpts h p₀ j = Finset.univ.image (mu h p₀ j) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun hq => exists_mu_eq h p₀ hq, fun ⟨x, hx⟩ => hx ▸ mu_mem h p₀ j x⟩
  change vline h p₀ j = insert p₀ (Finset.univ.image (mu h p₀ j))
  rw [← hv, vpts, Finset.insert_erase (p₀_mem_vline h p₀ j)]

theorem tline_eq_image (x y : Fin 4) :
    tline h p₀ x y = ({some (0, x), some (1, y), some (2, lsq h p₀ 2 x y),
      some (3, lsq h p₀ 3 x y), some (4, lsq h p₀ 4 x y)} :
        Finset (Option (Fin 5 × Fin 4))).image (coordPt h p₀) := by
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro q hq
    simp only [Finset.image_insert, Finset.image_singleton, Finset.mem_insert,
      Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact (tline_spec h p₀ x y).2.2.1
    · exact (tline_spec h p₀ x y).2.2.2
    · exact mu_lsq_mem h p₀ 2 x y
    · exact mu_lsq_mem h p₀ 3 x y
    · exact mu_lsq_mem h p₀ 4 x y
  · rw [h.card_line (tline_spec h p₀ x y).1,
      Finset.card_image_of_injective _ (coordPt_bijective h p₀).1]
    simp

theorem line_cases {M : Finset P} (hM : M ∈ 𝓛) :
    (∃ j, M = vline h p₀ j) ∨ ∃ x y, M = tline h p₀ x y := by
  by_cases hp : p₀ ∈ M
  · obtain ⟨j, hj⟩ := exists_vline_eq h p₀ hM hp
    exact Or.inl ⟨j, hj.symm⟩
  right
  obtain ⟨h0M, h0v⟩ := meetPoint_mem_vpts h p₀ hM hp 0
  obtain ⟨h1M, h1v⟩ := meetPoint_mem_vpts h p₀ hM hp 1
  obtain ⟨x, hx⟩ := exists_mu_eq h p₀ h0v
  obtain ⟨y, hy⟩ := exists_mu_eq h p₀ h1v
  refine ⟨x, y, ?_⟩
  rw [tline]
  exact h.eq_lineThrough (mu_ne_mu h p₀ (i := 0) (j := 1) (by decide) x y) hM (hx ▸ h0M)
    (hy ▸ h1M)

end Squares

@[expose] def encWith (τ : Perm (Fin 5)) : Option (Fin 5 × Fin 4) → Fin 21
  | none => 0
  | some (j, x) => enc (τ j) x

theorem encWith_bijective (τ : Perm (Fin 5)) : Function.Bijective (encWith τ) := by
  have : encWith τ = encOpt ∘ Option.map (Prod.map τ id) := by
    funext t
    rcases t with _ | ⟨j, x⟩ <;> rfl
  rw [this]
  refine encOpt_bijective.comp ?_
  exact (Equiv.optionCongr (Equiv.prodCongr τ (Equiv.refl _))).bijective

theorem steinerPlane_iso_projLine (h : IsSteinerPlane 𝓛) :
    ∃ ι : P ≃ Fin 21, 𝓛.image (fun L => L.map ι.toEmbedding) = Finset.univ.image projLine := by
  have hne : Nonempty P := by
    rw [← Fintype.card_pos_iff, h.card_points]
    norm_num
  obtain ⟨p₀⟩ := hne
  obtain ⟨τ, hτ0, hτ1, hτ2, himg⟩ : ∃ τ : Perm (Fin 5), τ 0 = 0 ∧ τ 1 = 1 ∧ τ 2 = 2 ∧
      ∀ x y : Fin 4, ({enc 0 x, enc 1 y, enc 2 (lsq h p₀ 2 x y), enc (τ 3) (lsq h p₀ 3 x y),
        enc (τ 4) (lsq h p₀ 4 x y)} : Finset (Fin 21)) ∈ Finset.univ.image projLine := by
    rcases lsq_cases h p₀ with ⟨e2, e3, e4⟩ | ⟨e2, e3, e4⟩
    · exact ⟨1, rfl, rfl, rfl, fun x y => by rw [e2, e3, e4]; exact tlineImage_mem x y⟩
    · refine ⟨swap 3 4, by decide, by decide, by decide, fun x y => ?_⟩
      rw [e2, e3, e4, swap_apply_left, swap_apply_right]
      rw [Finset.pair_comm]
      exact tlineImage_mem x y
  set e := Equiv.ofBijective (coordPt h p₀) (coordPt_bijective h p₀)
  set f := Equiv.ofBijective (encWith τ) (encWith_bijective τ)
  refine ⟨e.symm.trans f, ?_⟩
  have hmap : ∀ T : Finset (Option (Fin 5 × Fin 4)),
      (T.image (coordPt h p₀)).map (e.symm.trans f).toEmbedding = T.image (encWith τ) := by
    intro T
    rw [Finset.map_eq_image, Finset.image_image]
    refine Finset.image_congr fun t _ => ?_
    change f (e.symm (e t)) = encWith τ t
    rw [Equiv.symm_apply_apply]
    rfl
  have hsub : 𝓛.image (fun L => L.map (e.symm.trans f).toEmbedding) ⊆
      Finset.univ.image projLine := by
    intro A hA
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hA
    rcases line_cases h p₀ hM with ⟨j, rfl⟩ | ⟨x, y, rfl⟩
    · rw [vline_eq_image, hmap, Finset.image_insert, Finset.image_image]
      exact vlineImage_mem (τ j)
    · rw [tline_eq_image, hmap]
      simp only [Finset.image_insert, Finset.image_singleton]
      change ({enc (τ 0) x, enc (τ 1) y, enc (τ 2) (lsq h p₀ 2 x y),
        enc (τ 3) (lsq h p₀ 3 x y), enc (τ 4) (lsq h p₀ 4 x y)} : Finset (Fin 21)) ∈ _
      rw [hτ0, hτ1, hτ2]
      exact himg x y
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [card_image_projLine, Finset.card_image_of_injective _ (Finset.map_injective _),
    h.card_lines]

end CFSG.ComponentClassification.WittDesign
