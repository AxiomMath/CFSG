module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentNode
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusPlane
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusRoots

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.LieType.Steinberg.SpinFrame
  QuadraticMap

variable {n : ℕ} {K : Type} [Field K] {b c : K}

@[expose] def ShapeZ (G : Matrix (SM n) (SM n) K) (p : SM n) : Prop :=
  ∀ x y, ¬ ((x = p ∧ y ≠ p) ∨ (y = barS n p ∧ x ≠ barS n p)) → G x y = if x = y then 1 else 0

theorem minusPos_true_ne_false (a : Fin (n - 1)) : minusPos n a true ≠ minusPos n a false :=
  minusPos_ne_not a true

theorem ShapeZ.col_p {G : Matrix (SM n) (SM n) K} {a0 : Fin (n - 1)}
    (hG : ShapeZ G (minusPos n a0 true)) (x : SM n) :
    G x (minusPos n a0 true) = if x = minusPos n a0 true then 1 else 0 := by
  refine hG x _ ?_
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · exact h rfl
  · rw [barS_minusPos] at h
    exact minusPos_true_ne_false a0 h

theorem ShapeZ.row_bar {G : Matrix (SM n) (SM n) K} {a0 : Fin (n - 1)}
    (hG : ShapeZ G (minusPos n a0 true)) (y : SM n) :
    G (minusPos n a0 false) y = if minusPos n a0 false = y then 1 else 0 := by
  refine hG _ y ?_
  rintro (⟨h, -⟩ | ⟨-, h⟩)
  · exact minusPos_true_ne_false a0 h.symm
  · rw [barS_minusPos] at h
    exact h rfl

theorem eq_one_of_mul_self_eq_one [CharP K 2] {g : K} (hg : g * g = 1) : g = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h : (g - 1) * (g - 1) = 0 := by linear_combination hg - g * h2 + h2
  have := mul_self_eq_zero.mp h
  linear_combination this

theorem mulVec_single_one_apply (G : Matrix (SM n) (SM n) K) (e x : SM n) :
    (G *ᵥ Pi.single e 1) x = G x e := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem polar_single_minusPos (v : SM n → K) (a : Fin (n - 1)) (r : Bool) :
    polar (quadMinus n K b c) (Pi.single (minusPos n a r) 1) v = v (minusPos n a (!r)) := by
  rw [polar_comm]
  cases r
  · exact polar_quadMinus_single_inr_inl n K b c v a
  · exact polar_quadMinus_single_inl n K b c v a

theorem polar_single_pl [CharP K 2] (v : SM n → K) (u : Fin 2) :
    polar (quadMinus n K b c) (Pi.single (pl n u) 1) v = b * v (pl n (1 - u)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [polar_comm]
  fin_cases u
  · show polar (quadMinus n K b c) v (Pi.single (.inr (.inr 0)) 1) = b * v (.inr (.inr 1))
    rw [polar_quadMinus_single_inr_inr_zero, h2]
    ring
  · show polar (quadMinus n K b c) v (Pi.single (.inr (.inr 1)) 1) = b * v (.inr (.inr 0))
    rw [polar_quadMinus_single_inr_inr_one, h2]
    ring

theorem shapeZ_of_comm [CharP K 2] (hb : b ≠ 0) {a0 : Fin (n - 1)} {G : Matrix (SM n) (SM n) K}
    (hH : ∀ (b' : Fin (n - 1)) (t : Bool), b' ≠ a0 →
      HMS G (minusPos n a0 true) (minusPos n b' t))
    {b₁ b₂ : Fin (n - 1)} (h1 : b₁ ≠ a0) (h2 : b₂ ≠ a0) (h12 : b₁ ≠ b₂)
    (hS : ∀ u, SId b c G a0 u)
    (hpol : polar (quadMinus n K b c) (G *ᵥ Pi.single (minusPos n a0 true) 1)
      (G *ᵥ Pi.single (minusPos n a0 false) 1) = 1) :
    ShapeZ G (minusPos n a0 true) := by
  classical
  have hbp : barS n (minusPos n a0 true) = minusPos n a0 false := barS_minusPos a0 true
  have hne : ∀ (b' : Fin (n - 1)) (t : Bool), b' ≠ a0 →
      minusPos n a0 true ≠ minusPos n b' t := fun b' t hb' e => hb' (minusPos_inj e).1.symm
  have hr12 : minusPos n b₁ true ≠ minusPos n b₂ true := fun e => h12 (minusPos_inj e).1
  obtain ⟨hcol, hrow⟩ := col_row_of_two hr12 (hne b₁ true h1) (hne b₂ true h2)
    (hH b₁ true h1) (hH b₂ true h2)
  rw [hbp] at hrow
  have D : PlaneData b c G a0 := ⟨hcol, hrow, hS⟩
  set lam := G (minusPos n a0 true) (minusPos n a0 true) with hlam
  set mu := G (minusPos n a0 false) (minusPos n a0 false) with hmu
  have hframe : ∀ (b' : Fin (n - 1)) (t' : Bool), b' ≠ a0 → ∀ y,
      G (minusPos n b' t') y = if y = minusPos n b' t' then lam else
        if y = minusPos n a0 false then G (minusPos n b' t') (minusPos n a0 false) else 0 := by
    intro b' t' hb' y
    have H := hH b' (!t') hb'
    have hbr : barS n (minusPos n b' (!t')) = minusPos n b' t' := by
      rw [barS_minusPos, Bool.not_not]
    by_cases hy1 : y = minusPos n b' t'
    · subst hy1
      rw [if_pos rfl]
      have := H.col_p (hne b' (!t') hb') (minusPos n a0 true)
      rw [if_pos rfl, if_neg (hne b' (!t') hb'), sub_zero, hbr] at this
      exact this.symm
    · rw [if_neg hy1]
      by_cases hy2 : y = minusPos n a0 false
      · rw [if_pos hy2, hy2]
      · rw [if_neg hy2]
        have := (H.row_bar (hne b' (!t') hb') (y := y) (by rwa [hbr]) (by rwa [hbp])).1
        rwa [hbr] at this
  have hlm : lam = mu := by
    have e1 := D.plane_row hb 0 (y := pl n 0) (minusPos_ne_pl a0 false 0).symm
    have e2 := D.plane_col 0 (x := pl n 0) (minusPos_ne_pl a0 true 0).symm
    rw [if_pos rfl] at e1 e2
    rw [← hlam] at e1
    rw [← hmu] at e2
    exact e1.symm.trans e2
  have hcolv : G *ᵥ Pi.single (minusPos n a0 true) 1 = lam • Pi.single (minusPos n a0 true) 1 := by
    funext x
    rw [mulVec_single_one_apply, hcol x, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hlm1 : lam * mu = 1 := by
    rw [hcolv, polar_smul_left, polar_single_minusPos, Bool.not_true,
      mulVec_single_one_apply] at hpol
    exact hpol
  have hl1 : lam = 1 := eq_one_of_mul_self_eq_one (by rw [hlm] at hlm1 ⊢; exact hlm1)
  have hm1 : mu = 1 := hlm ▸ hl1
  intro x y hxy
  by_cases hxp : x = minusPos n a0 true
  · subst hxp
    have hy : y = minusPos n a0 true := by
      by_contra hy
      exact hxy (Or.inl ⟨rfl, hy⟩)
    subst hy
    rw [if_pos rfl]
    exact hl1
  by_cases hxb : x = minusPos n a0 false
  · subst hxb
    rw [hrow y, hm1]
    by_cases h : y = minusPos n a0 false
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hyb : y ≠ minusPos n a0 false := fun hy => hxy (Or.inr ⟨by rw [hbp]; exact hy, by
    rw [hbp]; exact hxb⟩)
  rcases x with a | a | u
  · have ha : a ≠ a0 := fun e => hxp (by rw [e]; rfl)
    have := hframe a true ha y
    rw [if_neg hyb, hl1] at this
    rw [show (Sum.inl a : SM n) = minusPos n a true from rfl, this]
    simp only [eq_comm]
  · have ha : a ≠ a0 := fun e => hxb (by rw [e]; rfl)
    have := hframe a false ha y
    rw [if_neg hyb, hl1] at this
    rw [show (Sum.inr (Sum.inl a) : SM n) = minusPos n a false from rfl, this]
    simp only [eq_comm]
  · have := D.plane_row hb u hyb
    rw [← hlam, hl1] at this
    rw [show (Sum.inr (Sum.inr u) : SM n) = pl n u from rfl, this]
    simp only [eq_comm]

theorem mul_single_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι K) (i j x y : ι) :
    (G * Matrix.single i j (1 : K)) x y = if y = j then G x i else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero, ite_and]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  by_cases h : j = y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem shapeZ_mul_long {a0 b' : Fin (n - 1)} (hab : a0 ≠ b') (t : Bool) (r : K)
    {G : Matrix (SM n) (SM n) K} (hG : ShapeZ G (minusPos n a0 true)) :
    ShapeZ (G * mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd r)))
        (minusPos n a0 true) ∧
      ∀ y, y ≠ minusPos n a0 false →
        (G * mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd r)))
          (minusPos n a0 true) y = G (minusPos n a0 true) y + (if y = minusPos n b' (!t) then r else 0) := by
  classical
  have hE : ∀ x y, (G * mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd r))) x y =
      G x y + r * (if y = minusPos n b' (!t) then G x (minusPos n a0 true) else 0) -
        r * (if y = minusPos n a0 false then G x (minusPos n b' t) else 0) := by
    intro x y
    rw [mat_longRoot_eq hab true t r]
    simp only [longMat, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_sub,
      Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_single_entry,
      Bool.not_true]
    ring
  have hrowE : ∀ y, y ≠ minusPos n a0 false →
      (G * mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd r)))
        (minusPos n a0 true) y = G (minusPos n a0 true) y + (if y = minusPos n b' (!t) then r else 0) := by
    intro y hy
    rw [hE, if_neg hy, mul_zero, sub_zero, hG.col_p, if_pos rfl]
    split_ifs <;> ring
  refine ⟨fun x y hxy => ?_, hrowE⟩
  rw [hE]
  by_cases hy : y = minusPos n a0 false
  ·
    have hx : x = minusPos n a0 false := by
      by_contra hx
      exact hxy (Or.inr ⟨by rw [barS_minusPos]; exact hy, by rw [barS_minusPos]; exact hx⟩)
    subst hx hy
    have hb'ne : minusPos n a0 false ≠ minusPos n b' t := fun e => hab (minusPos_inj e).1
    have hb'ne' : minusPos n a0 false ≠ minusPos n b' (!t) := fun e => hab (minusPos_inj e).1
    rw [if_neg hb'ne', if_pos rfl, hG.row_bar (minusPos n a0 false),
      hG.row_bar (minusPos n b' t), if_neg hb'ne]
    simp
  · rw [if_neg hy, mul_zero, sub_zero, hG x y (by
      rintro (⟨hx, hy'⟩ | ⟨hy', hx⟩)
      · exact hxy (Or.inl ⟨hx, hy'⟩)
      · exact hy (by rw [hy', barS_minusPos]; rfl))]
    by_cases hx : x = minusPos n a0 true
    · subst hx
      have hy' : y = minusPos n a0 true := by
        by_contra hy'
        exact hxy (Or.inl ⟨rfl, hy'⟩)
      subst hy'
      have : minusPos n a0 true ≠ minusPos n b' (!t) := fun e => hab (minusPos_inj e).1
      rw [if_neg this]
      simp
    · rw [hG.col_p, if_neg hx]
      simp

theorem polar_single_planeVec_smul [CharP K 2] (y : SM n) (u : Fin 2) (r : K) :
    polar (quadMinus n K b c) (Pi.single y 1) (planeVec n (r • Pi.single u 1)) =
      if y = pl n (1 - u) then b * r else 0 := by
  rcases y with a | a | v
  · rw [polar_single_planeVec_of_ne n (fun t => by simp) _, if_neg (by simp [pl])]
  · rw [polar_single_planeVec_of_ne n (fun t => by simp) _, if_neg (by simp [pl])]
  · rw [show (Sum.inr (Sum.inr v) : SM n) = pl n v from rfl, polar_single_pl]
    simp only [planeVec, pl, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Sum.inr.injEq]
    fin_cases u <;> fin_cases v <;> simp

theorem shapeZ_mul_short [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a0 : Fin (n - 1)}
    (u : Fin 2) (r : K) {G : Matrix (SM n) (SM n) K} (hG : ShapeZ G (minusPos n a0 true)) :
    ShapeZ (G * mat n (twShortRoot n hirr a0 true (Multiplicative.ofAdd (r • Pi.single u 1))))
        (minusPos n a0 true) ∧
      ∀ y, y ≠ minusPos n a0 false →
        (G * mat n (twShortRoot n hirr a0 true (Multiplicative.ofAdd (r • Pi.single u 1))))
          (minusPos n a0 true) y = G (minusPos n a0 true) y - (if y = pl n (1 - u) then b * r else 0) := by
  classical
  set q : Fin 2 → K := r • Pi.single u 1 with hq
  have hE : ∀ x y, y ≠ minusPos n a0 false →
      (G * mat n (twShortRoot n hirr a0 true (Multiplicative.ofAdd q))) x y =
        G x y - polar (quadMinus n K b c) (Pi.single y 1) (planeVec n q) *
          G x (minusPos n a0 true) := by
    intro x y hy
    have hy' : minusPos n a0 false ≠ y := fun e => hy e.symm
    rw [Matrix.mul_apply]
    simp only [mat_twShortRoot_apply n hirr a0 true q, Bool.not_true, if_neg hy', zero_mul,
      add_zero, mul_zero, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hrowE : ∀ y, y ≠ minusPos n a0 false →
      (G * mat n (twShortRoot n hirr a0 true (Multiplicative.ofAdd q))) (minusPos n a0 true) y =
        G (minusPos n a0 true) y - (if y = pl n (1 - u) then b * r else 0) := by
    intro y hy
    rw [hE _ y hy, hG.col_p, if_pos rfl, mul_one, hq, polar_single_planeVec_smul]
  refine ⟨fun x y hxy => ?_, hrowE⟩
  by_cases hy : y = minusPos n a0 false
  · have hx : x = minusPos n a0 false := by
      by_contra hx
      exact hxy (Or.inr ⟨by rw [barS_minusPos]; exact hy, by rw [barS_minusPos]; exact hx⟩)
    subst hx hy
    rw [Matrix.mul_apply]
    simp only [hG.row_bar, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [mat_twShortRoot_apply]
    simp only [Bool.not_true, if_true, planeVec]
    have h1 : (if minusPos n a0 false = minusPos n a0 true then (1 : K) else 0) = 0 :=
      if_neg (minusPos_true_ne_false a0).symm
    rw [h1, polar_single_planeVec_of_ne n (fun t => by simp [minusPos])]
    simp [minusPos]
  · rw [hE x y hy, hG x y (by
      rintro (⟨hx, hy'⟩ | ⟨hy', hx⟩)
      · exact hxy (Or.inl ⟨hx, hy'⟩)
      · exact hy (by rw [hy', barS_minusPos]; rfl))]
    by_cases hx : x = minusPos n a0 true
    · subst hx
      have hy' : y = minusPos n a0 true := by
        by_contra hy'
        exact hxy (Or.inl ⟨rfl, hy'⟩)
      subst hy'
      rw [polar_single_planeVec_of_ne n (fun t => by simp [minusPos])]
      simp
    · rw [hG.col_p, if_neg hx]
      simp

theorem eq_one_of_shapeZ [CharP K 2] (hb : b ≠ 0) {a0 : Fin (n - 1)} {G : Matrix (SM n) (SM n) K}
    (hG : ShapeZ G (minusPos n a0 true))
    (hz : ∀ y, y ≠ minusPos n a0 true → y ≠ minusPos n a0 false → G (minusPos n a0 true) y = 0)
    (hpol : ∀ v w, polar (quadMinus n K b c) (G *ᵥ v) (G *ᵥ w) = polar (quadMinus n K b c) v w)
    (hquad : ∀ v, quadMinus n K b c (G *ᵥ v) = quadMinus n K b c v) : G = 1 := by
  classical
  set p := minusPos n a0 true with hp
  set pb := minusPos n a0 false with hpb
  have hppb : p ≠ pb := minusPos_true_ne_false a0
  have hcol : ∀ y, y ≠ pb → ∀ x, G x y = if x = y then 1 else 0 := by
    intro y hy x
    by_cases hx : x = p
    · subst hx
      by_cases hyp : y = p
      · subst hyp
        exact hG.col_p p
      · rw [hz y hyp hy, if_neg (Ne.symm hyp)]
    · exact hG x y (by
        rintro (⟨hx', -⟩ | ⟨hy', -⟩)
        · exact hx hx'
        · exact hy (by rw [hy', hp, barS_minusPos]; rfl))
  have hcolv : ∀ y, y ≠ pb → G *ᵥ Pi.single y 1 = Pi.single y 1 := by
    intro y hy
    funext x
    rw [mulVec_single_one_apply, hcol y hy x, Pi.single_apply]
  set w := G *ᵥ Pi.single pb 1 with hw
  have hwx : ∀ x, w x = G x pb := fun x => mulVec_single_one_apply G pb x
  have hwf : ∀ x, x ≠ p → x ≠ pb → (∀ u, x ≠ pl n u) → w x = 0 := by
    intro x hx1 hx2 hx3
    rcases x with a | a | u
    · have ha : a ≠ a0 := fun e => hx1 (by rw [e]; rfl)
      have hy : minusPos n a false ≠ pb := fun e => ha (minusPos_inj e).1
      have h := hpol (Pi.single (minusPos n a false) 1) (Pi.single pb 1)
      rw [hcolv _ hy, polar_single_minusPos, polar_single_minusPos, Bool.not_false,
        Pi.single_apply, if_neg (fun e => ha (minusPos_inj e).1)] at h
      exact h
    · have ha : a ≠ a0 := fun e => hx2 (by rw [e]; rfl)
      have hy : minusPos n a true ≠ pb := fun e => (minusPos_inj e).2 |> Bool.noConfusion
      have h := hpol (Pi.single (minusPos n a true) 1) (Pi.single pb 1)
      rw [hcolv _ hy, polar_single_minusPos, polar_single_minusPos, Bool.not_true,
        Pi.single_apply, if_neg (fun e => ha (minusPos_inj e).1)] at h
      exact h
    · exact absurd rfl (hx3 u)
  have hwp : ∀ u, w (pl n u) = 0 := by
    intro u
    have hy : pl n (1 - u) ≠ pb := (minusPos_ne_pl a0 false _).symm
    have h := hpol (Pi.single (pl n (1 - u)) 1) (Pi.single pb 1)
    rw [hcolv _ hy, polar_single_pl, polar_single_pl, one_sub_one_sub, Pi.single_apply,
      if_neg (minusPos_ne_pl a0 false u).symm, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hb
  have hwe : w = Pi.single pb 1 + Pi.single p (G p pb) := by
    funext x
    rw [Pi.add_apply]
    by_cases hx1 : x = p
    · subst hx1
      rw [hwx, Pi.single_apply, if_neg hppb, Pi.single_apply, if_pos rfl, zero_add]
    · by_cases hx2 : x = pb
      · subst hx2
        rw [hwx, hG.row_bar, if_pos rfl, Pi.single_apply, if_pos rfl, Pi.single_apply,
          if_neg (Ne.symm hppb), add_zero]
      · rw [Pi.single_apply, if_neg hx2, Pi.single_apply, if_neg hx1, add_zero]
        by_cases hx3 : ∃ u, x = pl n u
        · obtain ⟨u, rfl⟩ := hx3
          exact hwp u
        · exact hwf x hx1 hx2 (fun u e => hx3 ⟨u, e⟩)
  have hQ : G p pb = 0 := by
    have h := hquad (Pi.single pb 1)
    rw [← hw, hwe, quadMinus_apply, quadMinus_apply] at h
    rw [hp, hpb] at h ⊢
    simpa [minusPos, Pi.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq] using h
  ext x y
  by_cases hy : y = pb
  · subst hy
    rw [← hwx, hwe, hQ, Pi.single_zero, add_zero, Pi.single_apply, Matrix.one_apply]
  · rw [hcol y hy x, Matrix.one_apply]

@[expose] noncomputable def cntZ (G : Matrix (SM n) (SM n) K) (p : SM n) : ℕ :=
  open Classical in
  (Finset.univ.filter fun y : SM n => y ≠ p ∧ y ≠ barS n p ∧ G p y ≠ 0).card

theorem cntZ_lt {G G' : Matrix (SM n) (SM n) K} {p y₀ : SM n} (hy₁ : y₀ ≠ p)
    (hy₂ : y₀ ≠ barS n p) (hc : G p y₀ ≠ 0) (h0 : G' p y₀ = 0)
    (hsame : ∀ y, y ≠ y₀ → y ≠ barS n p → G' p y = G p y) : cntZ G' p < cntZ G p := by
  classical
  unfold cntZ
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨y₀, ?_, ?_⟩
    · simp [hy₁, hy₂, hc]
    · simp [h0]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨h1, h2, h3⟩ := hy
    refine ⟨h1, h2, ?_⟩
    by_cases hyy : y = y₀
    · subst hyy
      exact absurd h0 h3
    · rwa [hsame y hyy h2] at h3

theorem lift_zero [CharP K 2] [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hb : b ≠ 0)
    (R : Subgroup (spinGroup (quadMinus n K b c))) (a0 : Fin (n - 1))
    (hlong : ∀ (b' : Fin (n - 1)) (hab : a0 ≠ b') (t : Bool) (r : K),
      (minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd r) ∈ R)
    (hshort : ∀ q : Fin 2 → K, twShortRoot n hirr a0 true (Multiplicative.ofAdd q) ∈ R) :
    ∀ (N : ℕ) (k : spinGroup (quadMinus n K b c)), ShapeZ (mat n k) (minusPos n a0 true) →
      cntZ (mat n k) (minusPos n a0 true) = N → k ∈ R := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k hS hN
    have hbp : barS n (minusPos n a0 true) = minusPos n a0 false := barS_minusPos a0 true
    by_cases hN0 : N = 0
    · subst hN0
      have hz : ∀ y, y ≠ minusPos n a0 true → y ≠ minusPos n a0 false →
          mat n k (minusPos n a0 true) y = 0 := by
        intro y h1 h2
        by_contra hne
        unfold cntZ at hN
        have : y ∈ Finset.univ.filter fun y : SM n => y ≠ minusPos n a0 true ∧
            y ≠ barS n (minusPos n a0 true) ∧ mat n k (minusPos n a0 true) y ≠ 0 := by
          simp [h1, hbp, h2, hne]
        rw [Finset.card_eq_zero] at hN
        simp [hN] at this
      have h1 : mat n k = 1 := eq_one_of_shapeZ hb hS hz (polar_mat_mulVec k) (quad_mat_mulVec k)
      have hk : k = 1 := mat_injective hirr (h1.trans (mat_one n).symm)
      rw [hk]
      exact R.one_mem
    · have hpos : 0 < cntZ (mat n k) (minusPos n a0 true) := by omega
      unfold cntZ at hpos
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨hy1, hy2, hy3⟩ := hy
      rw [hbp] at hy2
      rcases y with a | a | v
      ·
        have hab : a0 ≠ a := fun e => hy1 (by rw [e]; rfl)
        set r := -mat n k (minusPos n a0 true) (Sum.inl a) with hr
        have hya : (Sum.inl a : SM n) = minusPos n a (!false) := rfl
        obtain ⟨hS', hrow⟩ := shapeZ_mul_long (b := b) (c := c) hab false r hS
        rw [← mat_mul] at hS' hrow
        have hlt : cntZ (mat n (k * (minusFrame n b c).longRoot hab true false
            (Multiplicative.ofAdd r))) (minusPos n a0 true) < N := by
          rw [← hN]
          refine cntZ_lt hy1 (by rw [hbp]; exact hy2) hy3 ?_ ?_
          · rw [hrow _ hy2, if_pos hya, hr]
            simp [minusPos]
          · intro y h1 h2
            rw [hbp] at h2
            rw [hrow y h2, if_neg (by rw [← hya]; exact h1), add_zero]
        have key := ih _ hlt _ hS' rfl
        have hk : k = (k * (minusFrame n b c).longRoot hab true false (Multiplicative.ofAdd r)) *
            ((minusFrame n b c).longRoot hab true false (Multiplicative.ofAdd r))⁻¹ :=
          (mul_inv_cancel_right _ _).symm
        rw [hk]
        exact R.mul_mem key (R.inv_mem (hlong a hab false r))
      ·
        have hab : a0 ≠ a := fun e => hy2 (by rw [e]; rfl)
        set r := -mat n k (minusPos n a0 true) (Sum.inr (Sum.inl a)) with hr
        have hya : (Sum.inr (Sum.inl a) : SM n) = minusPos n a (!true) := rfl
        obtain ⟨hS', hrow⟩ := shapeZ_mul_long (b := b) (c := c) hab true r hS
        rw [← mat_mul] at hS' hrow
        have hlt : cntZ (mat n (k * (minusFrame n b c).longRoot hab true true
            (Multiplicative.ofAdd r))) (minusPos n a0 true) < N := by
          rw [← hN]
          refine cntZ_lt hy1 (by rw [hbp]; exact hy2) hy3 ?_ ?_
          · rw [hrow _ hy2, if_pos hya, hr]
            simp [minusPos]
          · intro y h1 h2
            rw [hbp] at h2
            rw [hrow y h2, if_neg (by rw [← hya]; exact h1), add_zero]
        have key := ih _ hlt _ hS' rfl
        have hk : k = (k * (minusFrame n b c).longRoot hab true true (Multiplicative.ofAdd r)) *
            ((minusFrame n b c).longRoot hab true true (Multiplicative.ofAdd r))⁻¹ :=
          (mul_inv_cancel_right _ _).symm
        rw [hk]
        exact R.mul_mem key (R.inv_mem (hlong a hab true r))
      ·
        set r := mat n k (minusPos n a0 true) (pl n v) / b with hr
        have hv : (Sum.inr (Sum.inr v) : SM n) = pl n (1 - (1 - v)) := by rw [one_sub_one_sub]; rfl
        obtain ⟨hS', hrow⟩ := shapeZ_mul_short hirr (1 - v) r hS
        rw [← mat_mul] at hS' hrow
        have hlt : cntZ (mat n (k * twShortRoot n hirr a0 true
            (Multiplicative.ofAdd (r • Pi.single (1 - v) 1)))) (minusPos n a0 true) < N := by
          rw [← hN]
          refine cntZ_lt hy1 (by rw [hbp]; exact hy2) hy3 ?_ ?_
          · rw [hrow _ hy2, if_pos hv, hr, mul_div_cancel₀ _ hb]
            simp [pl]
          · intro y h1 h2
            rw [hbp] at h2
            rw [hrow y h2, if_neg (by rw [← hv]; exact h1), sub_zero]
        have key := ih _ hlt _ hS' rfl
        have hk : k = (k * twShortRoot n hirr a0 true (Multiplicative.ofAdd (r • Pi.single (1 - v) 1))) *
            (twShortRoot n hirr a0 true (Multiplicative.ofAdd (r • Pi.single (1 - v) 1)))⁻¹ :=
          (mul_inv_cancel_right _ _).symm
        rw [hk]
        exact R.mul_mem key (R.inv_mem (hshort _))

theorem mem_radical_of_comm_node_zero [CharP K 2] [Finite K]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hb : b ≠ 0) (hN : 3 ≤ n - 1) (j : Fin (n - 1))
    (hj : j.val = 0) (k : spinGroup (quadMinus n K b c))
    (hk : ∀ u ∈ CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j, k * u = u * k) :
    k ∈ CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j := by
  classical
  have hmat : ∀ u ∈ CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j,
      mat n k * mat n u = mat n u * mat n k := fun u hu => by
    rw [← mat_mul, ← mat_mul, hk u hu]
  have hjb : ∀ b' : Fin (n - 1), b' ≠ j → j.val < b'.val := by
    intro b' hb'
    have : b'.val ≠ 0 := fun h => hb' (Fin.ext (by omega))
    omega
  have hH : ∀ (b' : Fin (n - 1)) (t : Bool), b' ≠ j →
      HMS (mat n k) (minusPos n j true) (minusPos n b' t) := by
    intro b' t hb'
    exact hms_of_comm b c (Ne.symm hb') t (mat n k)
      (hmat _ (minusLong_mem_radical hirr j (Ne.symm hb') t le_rfl (Or.inl (hjb b' hb')) 1))
  have hS : ∀ u, SId b c (mat n k) j u := fun u x y =>
    comm_entries_short_mat hirr j u (mat n k)
      (hmat _ (minusShort_mem_radical hirr j le_rfl _)) x y
  obtain ⟨b₁, b₂, h1, h2, h12⟩ := exists_two_ne hN j
  have hpol := polar_mat_mulVec k (Pi.single (minusPos n j true) 1) (Pi.single (minusPos n j false) 1)
  rw [polar_single_minusPos, Bool.not_true, Pi.single_apply, if_pos rfl] at hpol
  have hShape := shapeZ_of_comm (c := c) hb hH h1 h2 h12 hS hpol
  exact lift_zero hirr hb _ j
    (fun b' hab t r => minusLong_mem_radical hirr j hab t le_rfl (Or.inl (hjb b' (Ne.symm hab))) r)
    (fun q => minusShort_mem_radical hirr j le_rfl q) _ k hShape rfl

end CFSG.HardMathSupport.Cooperstein.StructureLie
