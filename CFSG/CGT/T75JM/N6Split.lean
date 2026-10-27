module

public import CFSG.CGT.T75JM.N6Basic
public import CFSG.CGT.T75JM.N6Class
public import CFSG.CGT.T75JM.N6Words
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.T75JM


section Fox

variable {G : Type*} [Group G] {T : Subgroup G}

@[expose] def tauT (g h : Subgroup.normalizer (T : Set G)) (a b : T) (w : List ℕ) : T :=
  w.foldl (fun τ l => ctr (if l = 0 then g⁻¹ else h⁻¹) τ * (if l = 0 then a else b)) 1

theorem fox_step (gl : Subgroup.normalizer (T : Set G)) (al τ : T) (E : G) :
    (E * (τ : G)) * ((gl : G) * (al : G)) = (E * (gl : G)) * ((ctr gl⁻¹ τ * al : T) : G) := by
  simp [ctr, mul_assoc]

theorem fox (g h : Subgroup.normalizer (T : Set G)) (a b : T) (w : List ℕ) :
    evalG ((g : G) * a) ((h : G) * b) w = evalG (g : G) (h : G) w * ((tauT g h a b w : T) : G) := by
  induction w using List.reverseRecOn with
  | nil => simp [evalG, tauT]
  | append_singleton w l ih =>
    have h1 : evalG ((g : G) * a) ((h : G) * b) [l] =
        ((if l = 0 then g else h : Subgroup.normalizer (T : Set G)) : G) *
          ((if l = 0 then a else b : T) : G) := by
      by_cases hl : l = 0 <;> simp [evalG, hl]
    have h2 : evalG (g : G) (h : G) [l] =
        ((if l = 0 then g else h : Subgroup.normalizer (T : Set G)) : G) := by
      by_cases hl : l = 0 <;> simp [evalG, hl]
    have h3 : tauT g h a b (w ++ [l]) =
        ctr (if l = 0 then g⁻¹ else h⁻¹) (tauT g h a b w) * (if l = 0 then a else b) := by
      simp only [tauT, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h4 : (if l = 0 then g⁻¹ else h⁻¹ : Subgroup.normalizer (T : Set G)) =
        (if l = 0 then g else h : Subgroup.normalizer (T : Set G))⁻¹ := by
      by_cases hl : l = 0 <;> simp [hl]
    rw [evalG_append, evalG_append, ih, h1, h2, h3, h4]
    exact fox_step _ _ _ _

theorem ctr_fix_of_pow (u : Subgroup.normalizer (T : Set G)) (n : ℕ) (t : T)
    (ht : (t : G) = (u : G) ^ n) : ctr u t = t := by
  apply Subtype.ext
  simp only [ctr, ht]
  rw [← pow_succ', pow_succ, mul_inv_cancel_right]

end Fox

@[expose] def tauN (fx fy : ℕ → ℕ) (a b : ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun τ l => if l = 0 then fx τ ^^^ a else fy τ ^^^ b) 0

section Coordinates

variable {G : Type*} [Group G] {T : Subgroup G} (c : Coords T)

include c

theorem coord_tauT (g h : Subgroup.normalizer (T : Set G)) (a b : T) (fx fy : ℕ → ℕ)
    (hfx : ∀ t : T, c.coord (ctr g⁻¹ t) = fx (c.coord t))
    (hfy : ∀ t : T, c.coord (ctr h⁻¹ t) = fy (c.coord t)) (w : List ℕ) :
    c.coord (tauT g h a b w) = tauN fx fy (c.coord a) (c.coord b) w := by
  induction w using List.reverseRecOn with
  | nil => simp [tauT, tauN, coord_one c]
  | append_singleton w l ih =>
    have h3 : tauT g h a b (w ++ [l]) =
        ctr (if l = 0 then g⁻¹ else h⁻¹) (tauT g h a b w) * (if l = 0 then a else b) := by
      simp only [tauT, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h5 : tauN fx fy (c.coord a) (c.coord b) (w ++ [l]) =
        if l = 0 then fx (tauN fx fy (c.coord a) (c.coord b) w) ^^^ c.coord a
        else fy (tauN fx fy (c.coord a) (c.coord b) w) ^^^ c.coord b := by
      simp only [tauN, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [h3, h5, c.mul]
    by_cases hl : l = 0 <;> simp [hl, hfx, hfy, ih]

theorem coord_ctr_inv (g : Subgroup.normalizer (T : Set G)) (X Xi : Cols)
    (hX : colsOf c g = X) (hXi : ∀ i, Xi.col i < 16)
    (hi : ∀ v, v < 16 → applyC X (applyC Xi v) = v)
    (hinj : ∀ u, u < 16 → ∀ w, w < 16 → applyC X u = applyC X w → u = w) (t : T) :
    c.coord (ctr g⁻¹ t) = applyC Xi (c.coord t) := by
  have h1 : applyC X (c.coord (ctr g⁻¹ t)) = c.coord t := by
    rw [← hX, ← coord_ctr, ← ctr_mul, mul_inv_cancel, ctr_one]
  have h2 : applyC X (applyC Xi (c.coord t)) = c.coord t := hi _ (c.lt t)
  exact hinj _ (c.lt _) _ (applyC_lt hXi _) (h1.trans h2.symm)

end Coordinates

@[expose] def modelXi : Cols := ⟨1, 11, 12, 8⟩

@[expose] def modelYi : Cols := ⟨6, 15, 2, 14⟩

theorem modelXi_lt : ∀ i, modelXi.col i < 16 := by decide
theorem modelYi_lt : ∀ i, modelYi.col i < 16 := by decide

theorem modelX_inv : ∀ v, v < 16 → applyC modelX (applyC modelXi v) = v := by decide
theorem modelY_inv : ∀ v, v < 16 → applyC modelY (applyC modelYi v) = v := by decide

theorem modelX_inj :
    ∀ u, u < 16 → ∀ w, w < 16 → applyC modelX u = applyC modelX w → u = w := by decide

theorem modelY_inj :
    ∀ u, u < 16 → ∀ w, w < 16 → applyC modelY u = applyC modelY w → u = w := by decide

theorem fixX : ∀ v, v < 16 → applyC modelX v = v → v = 0 ∨ v = 1 ∨ v = 8 ∨ v = 9 := by decide

theorem fixY : ∀ v, v < 16 → applyC modelY v = v → v = 0 ∨ v = 12 := by decide

theorem fixXY : ∀ v, v < 16 → applyC modelX (applyC modelY v) = v → v = 0 := by decide

theorem fixXYY :
    ∀ v, v < 16 → applyC modelX (applyC modelY (applyC modelY v)) = v → v = 0 := by decide

@[expose] def wordR1 : List ℕ := (List.replicate 2 [0]).flatten
@[expose] def wordR2 : List ℕ := (List.replicate 4 [1]).flatten
@[expose] def wordR3 : List ℕ := (List.replicate 5 [0, 1]).flatten
@[expose] def wordR4 : List ℕ := (List.replicate 5 [0, 1, 1]).flatten

@[expose] def abTable (v1 v2 : ℕ) : ℕ × ℕ :=
  ((if v1 = 0 then 0 else if v1 = 9 then 2 else if v1 = 8 then 4 else 6),
    if v2 = 0 then 0 else 2)

theorem table_ok : ∀ v1 ∈ [0, 1, 8, 9], ∀ v2 ∈ [0, 12],
    tauN (applyC modelXi) (applyC modelYi) (abTable v1 v2).1 (abTable v1 v2).2 wordR1 = v1 ∧
    tauN (applyC modelXi) (applyC modelYi) (abTable v1 v2).1 (abTable v1 v2).2 wordR2 = v2 ∧
    tauN (applyC modelXi) (applyC modelYi) (abTable v1 v2).1 (abTable v1 v2).2 wordR3 = 0 ∧
    tauN (applyC modelXi) (applyC modelYi) (abTable v1 v2).1 (abTable v1 v2).2 wordR4 = 0 := by
  decide

theorem abTable_lt : ∀ v1 ∈ [0, 1, 8, 9], ∀ v2 ∈ [0, 12],
    (abTable v1 v2).1 < 16 ∧ (abTable v1 v2).2 < 16 := by decide

section Adjust

variable {G : Type*} [Group G] {T : Subgroup G} (c : Coords T)

include c

theorem exists_adjust (g h : Subgroup.normalizer (T : Set G)) (hg : colsOf c g = modelX)
    (hh : colsOf c h = modelY) (t1 t2 t3 t4 : T)
    (h1 : evalG (g : G) h wordR1 = t1) (h2 : evalG (g : G) h wordR2 = t2)
    (h3 : evalG (g : G) h wordR3 = t3) (h4 : evalG (g : G) h wordR4 = t4) :
    ∃ a b : T, evalG ((g : G) * a) ((h : G) * b) wordR1 = 1 ∧
      evalG ((g : G) * a) ((h : G) * b) wordR2 = 1 ∧
      evalG ((g : G) * a) ((h : G) * b) wordR3 = 1 ∧
      evalG ((g : G) * a) ((h : G) * b) wordR4 = 1 := by
  have p1 : (t1 : G) = (g : G) ^ 2 := by
    rw [← h1, wordR1, evalG_flatten_replicate]; simp [evalG, pow_two]
  have p2 : (t2 : G) = (h : G) ^ 4 := by
    rw [← h2, wordR2, evalG_flatten_replicate]; simp [evalG, pow_succ, mul_assoc]
  have p3 : (t3 : G) = ((g * h : Subgroup.normalizer (T : Set G)) : G) ^ 5 := by
    rw [← h3, wordR3, evalG_flatten_replicate]; simp [evalG]
  have p4 : (t4 : G) = ((g * h * h : Subgroup.normalizer (T : Set G)) : G) ^ 5 := by
    rw [← h4, wordR4, evalG_flatten_replicate]; simp [evalG, mul_assoc]
  have c1 : applyC modelX (c.coord t1) = c.coord t1 := by
    rw [← hg, ← coord_ctr, ctr_fix_of_pow g 2 t1 p1]
  have c2 : applyC modelY (c.coord t2) = c.coord t2 := by
    rw [← hh, ← coord_ctr, ctr_fix_of_pow h 4 t2 p2]
  have c3 : applyC modelX (applyC modelY (c.coord t3)) = c.coord t3 := by
    have := congrArg c.coord (ctr_fix_of_pow (g * h) 5 t3 p3)
    rwa [coord_ctr, colsOf_mul, hg, hh, applyC_compC] at this
  have c4 : applyC modelX (applyC modelY (applyC modelY (c.coord t4))) = c.coord t4 := by
    have := congrArg c.coord (ctr_fix_of_pow (g * h * h) 5 t4 p4)
    rwa [coord_ctr, colsOf_mul, colsOf_mul, hg, hh, applyC_compC, applyC_compC] at this
  have d1 := fixX _ (c.lt t1) c1
  have d2 := fixY _ (c.lt t2) c2
  have d3 := fixXY _ (c.lt t3) c3
  have d4 := fixXYY _ (c.lt t4) c4
  have m1 : c.coord t1 ∈ [0, 1, 8, 9] := by rcases d1 with h | h | h | h <;> simp [h]
  have m2 : c.coord t2 ∈ [0, 12] := by rcases d2 with h | h <;> simp [h]
  obtain ⟨k1, k2, k3, k4⟩ := table_ok _ m1 _ m2
  obtain ⟨hl1, hl2⟩ := abTable_lt _ m1 _ m2
  set a : T := tOf c (abTable (c.coord t1) (c.coord t2)).1 with ha
  set b : T := tOf c (abTable (c.coord t1) (c.coord t2)).2 with hb
  have ca : c.coord a = (abTable (c.coord t1) (c.coord t2)).1 := coord_tOf c hl1
  have cb : c.coord b = (abTable (c.coord t1) (c.coord t2)).2 := coord_tOf c hl2
  have hfx := coord_ctr_inv c g modelX modelXi hg modelXi_lt modelX_inv modelX_inj
  have hfy := coord_ctr_inv c h modelY modelYi hh modelYi_lt modelY_inv modelY_inj
  have key : ∀ (w : List ℕ) (t : T), evalG (g : G) h w = t →
      tauN (applyC modelXi) (applyC modelYi) (c.coord a) (c.coord b) w = c.coord t →
      evalG ((g : G) * a) ((h : G) * b) w = 1 := by
    intro w t hw hτ
    have hc := coord_tauT c g h a b (applyC modelXi) (applyC modelYi) hfx hfy w
    have : tauT g h a b w = t := c.inj _ _ (hc.trans hτ)
    rw [fox, hw, this]
    have := coord_sq c t
    exact congrArg Subtype.val this
  refine ⟨a, b, key _ t1 h1 ?_, key _ t2 h2 ?_, key _ t3 h3 ?_, key _ t4 h4 ?_⟩
  · rw [ca, cb, k1]
  · rw [ca, cb, k2]
  · rw [ca, cb, k3, d3]
  · rw [ca, cb, k4, d4]

end Adjust

end CFSG.CGT.T75JM
