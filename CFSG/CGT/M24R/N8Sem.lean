module

public import CFSG.CGT.M24R.N8Inputs
public import CFSG.CGT.T75JM.N6Main

public section

namespace CFSG.CGT.M24R

open CFSG.CGT.T75JM

@[expose] def modelInv8 (i : Fin 6) : Cols := compC (modelCols8 i) (modelCols8 i)

theorem modelInv8_applyC : ∀ i : Fin 6, ∀ v, v < 16 →
    applyC (modelInv8 i) (applyC (modelCols8 i) v) = v := by
  decide

theorem modelCols8_lt : ∀ i : Fin 6, ∀ j, (modelCols8 i).col j < 16 := by
  decide

theorem isGL8_modelCols8 : ∀ i : Fin 6, isGL8 (modelCols8 i) = true := by
  decide

@[expose] def affStep8 (a : Fin 10 × Bool) (p : ℕ × Cols) : ℕ × Cols :=
  if h : a.1.val < 6 then
    (applyC (if a.2 then modelCols8 ⟨a.1.val, h⟩ else modelInv8 ⟨a.1.val, h⟩) p.1,
      compC (if a.2 then modelCols8 ⟨a.1.val, h⟩ else modelInv8 ⟨a.1.val, h⟩) p.2)
  else (2 ^ (a.1.val - 6) ^^^ p.1, p.2)

@[expose] def affEval8 (w : List (Fin 10 × Bool)) : ℕ × Cols := w.foldr affStep8 (0, idC)

theorem affEval8_relsN8Ten : ∀ r ∈ relsN8Ten, affEval8 r = (0, idC) := by
  have h : ∀ r ∈ relsN8Ten, (affEval8 r).1 = 0 ∧ (affEval8 r).2.c0 = 1 ∧
      (affEval8 r).2.c1 = 2 ∧ (affEval8 r).2.c2 = 4 ∧ (affEval8 r).2.c3 = 8 := by
    decide
  intro r hr
  obtain ⟨h0, h1, h2, h3, h4⟩ := h r hr
  exact Prod.ext h0 (Cols.ext h1 h2 h3 h4)

variable {G : Type*} [Group G] {T : Subgroup G} (c : Coords T) (L : Subgroup G)

def Rep8 (n : Subgroup.normalizer (T : Set G)) (p : ℕ × Cols) : Prop :=
  ∃ t : T, ∃ l : Subgroup.normalizer (T : Set G), (l : G) ∈ L ∧ n = inN t * l ∧
    c.coord t = p.1 ∧ colsOf c l = p.2

theorem rep8_one : Rep8 c L 1 (0, idC) :=
  ⟨1, 1, L.one_mem, Subtype.ext (by simp [inN]), coord_one c, colsOf_one c⟩

theorem rep8_mulL {a : Subgroup.normalizer (T : Set G)} (ha : (a : G) ∈ L)
    {n : Subgroup.normalizer (T : Set G)} {p : ℕ × Cols} (h : Rep8 c L n p) :
    Rep8 c L (a * n) (applyC (colsOf c a) p.1, compC (colsOf c a) p.2) := by
  obtain ⟨t, l, hl, rfl, ht, hlc⟩ := h
  refine ⟨ctr a t, a * l, L.mul_mem ha hl, Subtype.ext ?_, by rw [coord_ctr, ht], by
    rw [colsOf_mul, hlc]⟩
  simp only [inN, ctr, Subgroup.coe_mul]
  group

theorem rep8_mulT (u : T) {n : Subgroup.normalizer (T : Set G)} {p : ℕ × Cols}
    (h : Rep8 c L n p) : Rep8 c L (inN u * n) (c.coord u ^^^ p.1, p.2) := by
  obtain ⟨t, l, hl, rfl, ht, hlc⟩ := h
  exact ⟨u * t, l, hl, by rw [← mul_assoc, inN_mul], by rw [c.mul, ht], hlc⟩

theorem eq_one_of_colsOf_eq_idC8 (hC : Subgroup.centralizer (T : Set G) = T) (hLT : L ⊓ T = ⊥)
    {l : Subgroup.normalizer (T : Set G)} (hl : (l : G) ∈ L) (h : colsOf c l = idC) : l = 1 := by
  have hcen : (l : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (commute_of_colsOf c l h ⟨t, ht⟩).symm
  rw [hC] at hcen
  have hbot : (l : G) ∈ L ⊓ T := ⟨hl, hcen⟩
  rw [hLT] at hbot
  exact Subtype.ext (Subgroup.mem_bot.1 hbot)

theorem eq_one_of_rep8 (hC : Subgroup.centralizer (T : Set G) = T) (hLT : L ⊓ T = ⊥)
    {n : Subgroup.normalizer (T : Set G)} (h : Rep8 c L n (0, idC)) : n = 1 := by
  obtain ⟨t, l, hl, rfl, ht, hlc⟩ := h
  have ht1 : t = 1 := c.inj _ _ (by rw [ht, coord_one c])
  rw [ht1, eq_one_of_colsOf_eq_idC8 c L hC hLT hl hlc, mul_one]
  exact Subtype.ext rfl

theorem colsOf_inv_eq8 (n : Subgroup.normalizer (T : Set G)) {A A' : Cols} (hA : colsOf c n = A)
    (hinv : ∀ v, v < 16 → applyC A' (applyC A v) = v) : colsOf c n⁻¹ = A' := by
  have key : ∀ v, v < 16 → applyC (colsOf c n⁻¹) v = applyC A' v := by
    intro v hv
    have h1 : ctr n (ctr n⁻¹ (tOf c v)) = tOf c v := by
      rw [← ctr_mul, mul_inv_cancel, ctr_one]
    have h2 : applyC A (c.coord (ctr n⁻¹ (tOf c v))) = v := by
      rw [← hA, ← coord_ctr, h1, coord_tOf c hv]
    calc applyC (colsOf c n⁻¹) v = c.coord (ctr n⁻¹ (tOf c v)) := by
          rw [coord_ctr, coord_tOf c hv]
      _ = applyC A' (applyC A (c.coord (ctr n⁻¹ (tOf c v)))) := (hinv _ (c.lt _)).symm
      _ = applyC A' v := by rw [h2]
  exact cols_ext fun i => key _ (by fin_cases i <;> decide)

@[expose] noncomputable def gens8 (l : Fin 6 → Subgroup.normalizer (T : Set G)) :
    Fin 10 → Subgroup.normalizer (T : Set G) :=
  fun k => if h : k.val < 6 then l ⟨k.val, h⟩ else tN c (k.val - 6)

theorem lift_mk_cons8 {α H : Type*} [Group H] (f : α → H) (a : α × Bool) (w : List (α × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (a :: w)) =
      cond a.2 (f a.1) (f a.1)⁻¹ * FreeGroup.lift f (FreeGroup.mk w) := by
  simp only [FreeGroup.lift_mk, List.map_cons, List.prod_cons]

theorem rep8_lift {l : Fin 6 → Subgroup.normalizer (T : Set G)} (hl : ∀ i, (l i : G) ∈ L)
    (hcl : ∀ i, colsOf c (l i) = modelCols8 i) (w : List (Fin 10 × Bool)) :
    Rep8 c L (FreeGroup.lift (gens8 c l) (FreeGroup.mk w)) (affEval8 w) := by
  induction w with
  | nil => simpa [affEval8] using rep8_one c L
  | cons a w ih =>
    rw [lift_mk_cons8]
    obtain ⟨⟨k, hk⟩, b⟩ := a
    show Rep8 c L _ (affStep8 ((⟨k, hk⟩ : Fin 10), b) (affEval8 w))
    by_cases h6 : k < 6
    · have hg : gens8 c l ⟨k, hk⟩ = l ⟨k, h6⟩ := by simp [gens8, h6]
      cases b
      · have h := rep8_mulL c L (a := (l ⟨k, h6⟩)⁻¹) (L.inv_mem (hl _)) ih
        rw [colsOf_inv_eq8 c _ (hcl _) (modelInv8_applyC _)] at h
        simpa [affStep8, h6, hg] using h
      · have h := rep8_mulL c L (hl ⟨k, h6⟩) ih
        rw [hcl] at h
        simpa [affStep8, h6, hg] using h
    · have hj : 2 ^ (k - 6) < 16 := by
        have : k - 6 < 4 := by omega
        interval_cases (k - 6) <;> norm_num
      have hg : gens8 c l ⟨k, hk⟩ = inN (tOf c (2 ^ (k - 6))) := by simp [gens8, h6, tN]
      have hinv : (inN (tOf c (2 ^ (k - 6))))⁻¹ =
          (inN (tOf c (2 ^ (k - 6))) : Subgroup.normalizer (T : Set G)) :=
        inv_eq_of_mul_eq_one_right (inN_sq c _)
      have h := rep8_mulT c L (tOf c (2 ^ (k - 6))) ih
      rw [coord_tOf c hj] at h
      cases b <;> simpa [affStep8, h6, hg, hinv] using h

theorem lift_relsN8Ten_eq_one (hC : Subgroup.centralizer (T : Set G) = T) (hLT : L ⊓ T = ⊥)
    {l : Fin 6 → Subgroup.normalizer (T : Set G)} (hl : ∀ i, (l i : G) ∈ L)
    (hcl : ∀ i, colsOf c (l i) = modelCols8 i) :
    ∀ r ∈ relsN8Ten, FreeGroup.lift (gens8 c l) (FreeGroup.mk r) = 1 := by
  intro r hr
  have h := rep8_lift c L hl hcl r
  rw [affEval8_relsN8Ten r hr] at h
  exact eq_one_of_rep8 c L hC hLT h

end CFSG.CGT.M24R
