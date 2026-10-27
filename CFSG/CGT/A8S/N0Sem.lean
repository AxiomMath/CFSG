module

public import CFSG.CGT.A8S.N0Coords
public import CFSG.CGT.A8S.N0Model

public section

namespace CFSG.CGT.A8S.N0

open CFSG.CGT.T75JM

variable {G : Type*} [Group G] {T : Subgroup G}

@[expose] def inN3 (t : T) : Subgroup.normalizer (T : Set G) :=
  ⟨(t : G), Subgroup.le_normalizer t.2⟩

theorem inN3_mul (a b : T) :
    inN3 a * inN3 b = (inN3 (a * b) : Subgroup.normalizer (T : Set G)) :=
  rfl

variable (c : Coords3 T) (L : Subgroup G)

include c in
theorem inN3_sq (a : T) : inN3 a * inN3 a = (1 : Subgroup.normalizer (T : Set G)) := by
  rw [inN3_mul, coord_sq3 c]
  rfl

def Rep3 (n : Subgroup.normalizer (T : Set G)) (p : ℕ × Cols3) : Prop :=
  ∃ t : T, ∃ l : Subgroup.normalizer (T : Set G), (l : G) ∈ L ∧ n = inN3 t * l ∧
    c.coord t = p.1 ∧ colsOf3 c l = p.2

theorem rep3_one : Rep3 c L 1 (0, idC3) :=
  ⟨1, 1, L.one_mem, Subtype.ext (by simp [inN3]), coord_one3 c, colsOf3_one c⟩

theorem rep3_mulL {a : Subgroup.normalizer (T : Set G)} (ha : (a : G) ∈ L)
    {n : Subgroup.normalizer (T : Set G)} {p : ℕ × Cols3} (h : Rep3 c L n p) :
    Rep3 c L (a * n) (applyC3 (colsOf3 c a) p.1, compC3 (colsOf3 c a) p.2) := by
  obtain ⟨t, l, hl, rfl, ht, hlc⟩ := h
  refine ⟨ctr a t, a * l, L.mul_mem ha hl, Subtype.ext ?_, by rw [coord_ctr3, ht], by
    rw [colsOf3_mul, hlc]⟩
  simp only [inN3, ctr, Subgroup.coe_mul]
  group

theorem rep3_mulT (u : T) {n : Subgroup.normalizer (T : Set G)} {p : ℕ × Cols3}
    (h : Rep3 c L n p) : Rep3 c L (inN3 u * n) (c.coord u ^^^ p.1, p.2) := by
  obtain ⟨t, l, hl, rfl, ht, hlc⟩ := h
  exact ⟨u * t, l, hl, by rw [← mul_assoc, inN3_mul], by rw [c.mul, ht], hlc⟩

theorem rep3_unique (hLT : L ⊓ T = ⊥) {n : Subgroup.normalizer (T : Set G)} {p q : ℕ × Cols3}
    (hp : Rep3 c L n p) (hq : Rep3 c L n q) : p = q := by
  obtain ⟨t, l, hl, rfl, ht, hlc⟩ := hp
  obtain ⟨t', l', hl', hn, ht', hlc'⟩ := hq
  have h1 : (t : G) * l = t' * l' := congrArg Subtype.val hn
  have hx : (t' : G)⁻¹ * t = l' * (l : G)⁻¹ := by
    calc (t' : G)⁻¹ * t = (t' : G)⁻¹ * ((t : G) * l) * (l : G)⁻¹ := by group
      _ = (t' : G)⁻¹ * ((t' : G) * l') * (l : G)⁻¹ := by rw [h1]
      _ = l' * (l : G)⁻¹ := by group
  have hbot : (t' : G)⁻¹ * t ∈ L ⊓ T :=
    ⟨by rw [hx]; exact L.mul_mem hl' (L.inv_mem hl), T.mul_mem (T.inv_mem t'.2) t.2⟩
  rw [hLT, Subgroup.mem_bot] at hbot
  have htt : t = t' := Subtype.ext (inv_mul_eq_one.1 hbot).symm
  have hll : l = l' := by
    rw [hbot] at hx
    exact Subtype.ext (mul_inv_eq_one.1 hx.symm).symm
  subst htt hll
  exact Prod.ext (ht.symm.trans ht') (hlc.symm.trans hlc')

theorem eq_one_of_colsOf3_eq_idC3 (hC : Subgroup.centralizer (T : Set G) = T) (hLT : L ⊓ T = ⊥)
    {l : Subgroup.normalizer (T : Set G)} (hl : (l : G) ∈ L) (h : colsOf3 c l = idC3) :
    l = 1 := by
  have hcen : (l : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (commute_of_colsOf3 c l h ⟨t, ht⟩).symm
  rw [hC] at hcen
  have hbot : (l : G) ∈ L ⊓ T := ⟨hl, hcen⟩
  rw [hLT] at hbot
  exact Subtype.ext (Subgroup.mem_bot.1 hbot)

theorem eq_one_of_rep3 (hC : Subgroup.centralizer (T : Set G) = T) (hLT : L ⊓ T = ⊥)
    {n : Subgroup.normalizer (T : Set G)} (h : Rep3 c L n (0, idC3)) : n = 1 := by
  obtain ⟨t, l, hl, rfl, ht, hlc⟩ := h
  have ht1 : t = 1 := c.inj _ _ (by rw [ht, coord_one3 c])
  rw [ht1, eq_one_of_colsOf3_eq_idC3 c L hC hLT hl hlc, mul_one]
  exact Subtype.ext rfl

theorem colsOf3_inv_eq (n : Subgroup.normalizer (T : Set G)) {A A' : Cols3}
    (hA : colsOf3 c n = A) (hinv : ∀ v, v < 8 → applyC3 A' (applyC3 A v) = v) :
    colsOf3 c n⁻¹ = A' := by
  have key : ∀ v, v < 8 → applyC3 (colsOf3 c n⁻¹) v = applyC3 A' v := by
    intro v hv
    have h1 : ctr n (ctr n⁻¹ (tOf3 c v)) = tOf3 c v := by
      rw [← ctr_mul, mul_inv_cancel, ctr_one]
    have h2 : applyC3 A (c.coord (ctr n⁻¹ (tOf3 c v))) = v := by
      rw [← hA, ← coord_ctr3, h1, coord_tOf3 c hv]
    calc applyC3 (colsOf3 c n⁻¹) v = c.coord (ctr n⁻¹ (tOf3 c v)) := by
          rw [coord_ctr3, coord_tOf3 c hv]
      _ = applyC3 A' (applyC3 A (c.coord (ctr n⁻¹ (tOf3 c v)))) := (hinv _ (c.lt _)).symm
      _ = applyC3 A' v := by rw [h2]
  exact cols3_ext fun j => key _ (by fin_cases j <;> decide)

@[expose] noncomputable def gens3 (l : Fin 2 → Subgroup.normalizer (T : Set G)) :
    Fin 5 → Subgroup.normalizer (T : Set G) :=
  fun k => if h : k.val < 2 then l ⟨k.val, h⟩ else inN3 (tOf3 c (2 ^ (k.val - 2)))

theorem rep3_lift {l : Fin 2 → Subgroup.normalizer (T : Set G)} (hl : ∀ i, (l i : G) ∈ L)
    (hcl : ∀ i : Fin 2, colsOf3 c (l i) = modelCols3 i.val) (w : List (Fin 5 × Bool)) :
    Rep3 c L (FreeGroup.lift (gens3 c l) (FreeGroup.mk w)) (affEval w) := by
  induction w with
  | nil =>
    rw [show FreeGroup.mk ([] : List (Fin 5 × Bool)) = 1 from rfl, map_one]
    exact rep3_one c L
  | cons a w ih =>
    rw [lift_mk_cons, affEval_cons]
    obtain ⟨⟨k, hk⟩, b⟩ := a
    by_cases h2 : k < 2
    · have hg : gens3 c l ⟨k, hk⟩ = l ⟨k, h2⟩ := by simp [gens3, h2]
      cases b
      · have h := rep3_mulL c L (a := (l ⟨k, h2⟩)⁻¹) (L.inv_mem (hl _)) ih
        rw [colsOf3_inv_eq c _ (hcl ⟨k, h2⟩) (modelInv3_applyC3 k h2)] at h
        simpa [affStep, h2, hg] using h
      · have h := rep3_mulL c L (hl ⟨k, h2⟩) ih
        rw [hcl ⟨k, h2⟩] at h
        simpa [affStep, h2, hg] using h
    · have hj : 2 ^ (k - 2) < 8 := by
        have : k - 2 < 3 := by omega
        interval_cases (k - 2) <;> norm_num
      have hg : gens3 c l ⟨k, hk⟩ = inN3 (tOf3 c (2 ^ (k - 2))) := by simp [gens3, h2]
      have hinv : (inN3 (tOf3 c (2 ^ (k - 2))))⁻¹ =
          (inN3 (tOf3 c (2 ^ (k - 2))) : Subgroup.normalizer (T : Set G)) :=
        inv_eq_of_mul_eq_one_right (inN3_sq c _)
      have h := rep3_mulT c L (tOf3 c (2 ^ (k - 2))) ih
      rw [coord_tOf3 c hj] at h
      cases b <;> simpa [affStep, h2, hg, hinv, Nat.one_shiftLeft] using h

theorem lift_relsN0A8_eq_one (hC : Subgroup.centralizer (T : Set G) = T) (hLT : L ⊓ T = ⊥)
    {l : Fin 2 → Subgroup.normalizer (T : Set G)} (hl : ∀ i, (l i : G) ∈ L)
    (hcl : ∀ i : Fin 2, colsOf3 c (l i) = modelCols3 i.val) :
    ∀ r ∈ relsN0A8, FreeGroup.lift (gens3 c l) (FreeGroup.mk r) = 1 := by
  intro r hr
  have h := rep3_lift c L hl hcl r
  rw [affEval_relsN0A8 r hr] at h
  exact eq_one_of_rep3 c L hC hLT h

end CFSG.CGT.A8S.N0
