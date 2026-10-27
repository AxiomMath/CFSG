module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegCrit
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.PushingUpLit.SolKNA

open scoped MatrixGroups

namespace PSL4Twin

theorem sqNeg : ∀ a b c d : ZMod 3, a * a + b * c = -1 → a * b + b * d = 0 →
    c * a + d * c = 0 → c * b + d * d = -1 →
      a * d - b * c = 1 ∧ ¬ (b = 0 ∧ c = 0 ∧ a = d) := by
  decide +kernel

theorem sqPos : ∀ a b c d : ZMod 3, a * a + b * c = 1 → a * b + b * d = 0 →
    c * a + d * c = 0 → c * b + d * d = 1 → a * d - b * c = 1 →
      b = 0 ∧ c = 0 ∧ a = d := by
  decide +kernel

theorem blocks_twin (a b c d e f g h : ZMod 3)
    (hsq : (a * a + b * c = -1 ∧ a * b + b * d = 0 ∧ c * a + d * c = 0 ∧ c * b + d * d = -1 ∧
        e * e + f * g = 1 ∧ e * f + f * h = 0 ∧ g * e + h * g = 0 ∧ g * f + h * h = 1) ∨
      (a * a + b * c = 1 ∧ a * b + b * d = 0 ∧ c * a + d * c = 0 ∧ c * b + d * d = 1 ∧
        e * e + f * g = -1 ∧ e * f + f * h = 0 ∧ g * e + h * g = 0 ∧ g * f + h * h = -1))
    (hdet : (a * d - b * c) * (e * h - f * g) = 1) :
    (b * g = c * f ∧ a * f + b * h = e * b + f * d ∧ c * e + d * g = g * a + h * c) ∧
      ¬ (e = a ∧ f = b ∧ g = c ∧ h = d) ∧ ¬ (e = -a ∧ f = -b ∧ g = -c ∧ h = -d) := by
  rcases hsq with ⟨p1, p2, p3, p4, s1, s2, s3, s4⟩ | ⟨p1, p2, p3, p4, s1, s2, s3, s4⟩
  · obtain ⟨hdP, hnP⟩ := sqNeg a b c d p1 p2 p3 p4
    rw [hdP, one_mul] at hdet
    obtain ⟨hf, hg, hhe⟩ := sqPos e f g h s1 s2 s3 s4 hdet
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hg, hf]; ring
    · rw [hf, ← hhe]; ring
    · rw [hg, ← hhe]; ring
    · rintro ⟨h1, h2, h3, h4⟩
      exact hnP ⟨h2.symm.trans hf, h3.symm.trans hg, h1.symm.trans (hhe.trans h4)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact hnP ⟨neg_eq_zero.mp (h2.symm.trans hf), neg_eq_zero.mp (h3.symm.trans hg),
        neg_inj.mp (h1.symm.trans (hhe.trans h4))⟩
  · obtain ⟨hdS, hnS⟩ := sqNeg e f g h s1 s2 s3 s4
    rw [hdS, mul_one] at hdet
    obtain ⟨hb, hc, had⟩ := sqPos a b c d p1 p2 p3 p4 hdet
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hb, hc]; ring
    · rw [hb, ← had]; ring
    · rw [hc, ← had]; ring
    · rintro ⟨h1, h2, h3, h4⟩
      exact hnS ⟨h2.trans hb, h3.trans hc, h1.trans (had.trans h4.symm)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact hnS ⟨h2.trans (by rw [hb, neg_zero]), h3.trans (by rw [hc, neg_zero]),
        h1.trans ((congrArg Neg.neg had).trans h4.symm)⟩

theorem zero_of_mixed : ∀ (x : ZMod 3) (i j : Fin 4), (i.val < 2 ↔ ¬ j.val < 2) →
    x * (if j.val < 2 then (-1 : ZMod 3) else 1) =
      (if i.val < 2 then (-1 : ZMod 3) else 1) * x → x = 0 := by
  decide +kernel

@[expose] def diagBlk (a b c d e f g h : ZMod 3) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![a, b, 0, 0; c, d, 0, 0; 0, 0, e, f; 0, 0, g, h]

theorem diagBlk_mul (a b c d e f g h a' b' c' d' e' f' g' h' : ZMod 3) :
    diagBlk a b c d e f g h * diagBlk a' b' c' d' e' f' g' h' =
      diagBlk (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d')
        (e * e' + f * g') (e * f' + f * h') (g * e' + h * g') (g * f' + h * h') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagBlk, Matrix.mul_apply, Fin.sum_univ_four]

theorem diagBlk_neg (a b c d e f g h : ZMod 3) :
    -diagBlk a b c d e f g h = diagBlk (-a) (-b) (-c) (-d) (-e) (-f) (-g) (-h) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagBlk]

theorem diagBlk_inj {a b c d e f g h a' b' c' d' e' f' g' h' : ZMod 3} :
    diagBlk a b c d e f g h = diagBlk a' b' c' d' e' f' g' h' ↔
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' ∧ g = g' ∧ h = h' := by
  constructor
  · intro H
    have h00 := congrFun (congrFun H 0) 0
    have h01 := congrFun (congrFun H 0) 1
    have h10 := congrFun (congrFun H 1) 0
    have h11 := congrFun (congrFun H 1) 1
    have h22 := congrFun (congrFun H 2) 2
    have h23 := congrFun (congrFun H 2) 3
    have h32 := congrFun (congrFun H 3) 2
    have h33 := congrFun (congrFun H 3) 3
    simp [diagBlk] at h00 h01 h10 h11 h22 h23 h32 h33
    exact ⟨h00, h01, h10, h11, h22, h23, h32, h33⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem diagBlk_det (a b c d e f g h : ZMod 3) :
    (diagBlk a b c d e f g h).det = (a * d - b * c) * (e * h - f * g) := by
  simp [diagBlk, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

@[expose] def deltaMat : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.diagonal fun j : Fin 4 => if j.val < 2 then (-1 : ZMod 3) else 1

@[expose] def swapMat : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem deltaMat_eq : deltaMat = diagBlk (-1) 0 0 (-1) 1 0 0 1 := by decide +kernel

theorem deltaMat_mul_self : deltaMat * deltaMat = 1 := by decide +kernel

theorem deltaMat_det : deltaMat.det = 1 := by decide +kernel

theorem swapMat_mul_self : swapMat * swapMat = 1 := by decide +kernel

theorem swapMat_det : swapMat.det = 1 := by decide +kernel

theorem swapMat_deltaMat : swapMat * deltaMat = -(deltaMat * swapMat) := by decide +kernel

theorem swapMat_diagBlk (a b c d e f g h : ZMod 3) :
    swapMat * diagBlk a b c d e f g h * swapMat = diagBlk e f g h a b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat, diagBlk, Matrix.mul_apply, Fin.sum_univ_four]

theorem diagBlk_mul_deltaMat (a b c d e f g h : ZMod 3) :
    diagBlk a b c d e f g h * deltaMat = diagBlk (-a) (-b) (-c) (-d) e f g h := by
  rw [deltaMat_eq, diagBlk_mul, diagBlk_inj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem diagBlk_swap_comm (a b c d e f g h : ZMod 3) (h1 : b * g = c * f)
    (h2 : a * f + b * h = e * b + f * d) (h3 : c * e + d * g = g * a + h * c) :
    diagBlk e f g h a b c d * diagBlk a b c d e f g h =
      diagBlk a b c d e f g h * diagBlk e f g h a b c d := by
  rw [diagBlk_mul, diagBlk_mul, diagBlk_inj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -h1
  · linear_combination -h2
  · linear_combination -h3
  · linear_combination h1
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination -h1

theorem eq_diagBlk_of_comm (A : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (h : A * deltaMat = deltaMat * A) :
    A = diagBlk (A 0 0) (A 0 1) (A 1 0) (A 1 1) (A 2 2) (A 2 3) (A 3 2) (A 3 3) := by
  have h' : ∀ i j : Fin 4, (i.val < 2 ↔ ¬ j.val < 2) → A i j = 0 := fun i j hij =>
    zero_of_mixed _ i j hij (by
      have := congrFun (congrFun h i) j
      simpa [deltaMat, Matrix.mul_diagonal, Matrix.diagonal_mul] using this)
  have h02 : A 0 2 = 0 := h' 0 2 (by decide)
  have h03 : A 0 3 = 0 := h' 0 3 (by decide)
  have h12 : A 1 2 = 0 := h' 1 2 (by decide)
  have h13 : A 1 3 = 0 := h' 1 3 (by decide)
  have h20 : A 2 0 = 0 := h' 2 0 (by decide)
  have h21 : A 2 1 = 0 := h' 2 1 (by decide)
  have h30 : A 3 0 = 0 := h' 3 0 (by decide)
  have h31 : A 3 1 = 0 := h' 3 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagBlk, h02, h03, h12, h13, h20, h21, h30, h31]

theorem mem_center_sl4 (z : SL(4, ZMod 3)) :
    z ∈ Subgroup.center SL(4, ZMod 3) ↔
      (z : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 1 ∨ (z : Matrix (Fin 4) (Fin 4) (ZMod 3)) = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hrz⟩
    have hr4 : r ^ 4 = 1 := by simpa using hr
    rcases (by decide : ∀ r : ZMod 3, r ^ 4 = 1 → r = 1 ∨ r = -1) r hr4 with rfl | rfl
    · left
      rw [← hrz, map_one]
    · right
      rw [← hrz, map_neg, map_one]
  · rintro (h | h)
    · exact ⟨1, by rw [one_pow], by rw [h, map_one]⟩
    · exact ⟨-1, by rw [Fintype.card_fin]; decide, by rw [h, map_neg, map_one]⟩

theorem mk_eq_mk_iff (X Y : SL(4, ZMod 3)) :
    (QuotientGroup.mk X : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) = QuotientGroup.mk Y ↔
      (X : Matrix (Fin 4) (Fin 4) (ZMod 3)) = (Y : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∨
        (X : Matrix (Fin 4) (Fin 4) (ZMod 3)) = -(Y : Matrix (Fin 4) (Fin 4) (ZMod 3)) := by
  have e1 : (QuotientGroup.mk X : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) =
      QuotientGroup.mk Y ↔ Y⁻¹ * X ∈ Subgroup.center SL(4, ZMod 3) := by
    rw [eq_comm]
    exact QuotientGroup.eq
  rw [e1, mem_center_sl4]
  have hX : (X : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      (Y : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
        ((Y⁻¹ * X : SL(4, ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  constructor
  · rintro (h | h)
    · left
      rw [hX, h, mul_one]
    · right
      rw [hX, h, Matrix.mul_neg, mul_one]
  · rintro (h | h)
    · left
      have hXY : X = Y := Subtype.ext h
      rw [hXY, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    · right
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, h,
        Matrix.mul_neg, Matrix.adjugate_mul, Matrix.SpecialLinearGroup.det_coe, one_smul]

@[expose] def deltaSL : SL(4, ZMod 3) := ⟨deltaMat, deltaMat_det⟩

@[expose] def swapSL : SL(4, ZMod 3) := ⟨swapMat, swapMat_det⟩

theorem coe_deltaSL : (deltaSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) = deltaMat := rfl

theorem coe_swapSL : (swapSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) = swapMat := rfl

theorem deltaSL_mul_self : deltaSL * deltaSL = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_deltaSL, Matrix.SpecialLinearGroup.coe_one]
    exact deltaMat_mul_self)

theorem swapSL_inv : swapSL⁻¹ = swapSL :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_swapSL, Matrix.SpecialLinearGroup.coe_one]
    exact swapMat_mul_self))

theorem blk_data (A : SL(4, ZMod 3))
    (hsq : (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) * A = deltaMat ∨
      (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) * A = -deltaMat) :
    ∃ a b c d e f g h : ZMod 3, (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) = diagBlk a b c d e f g h ∧
      (b * g = c * f ∧ a * f + b * h = e * b + f * d ∧ c * e + d * g = g * a + h * c) ∧
      ¬ (e = a ∧ f = b ∧ g = c ∧ h = d) ∧ ¬ (e = -a ∧ f = -b ∧ g = -c ∧ h = -d) := by
  have hcomm : (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) * deltaMat = deltaMat * A := by
    rcases hsq with h | h
    · rw [← h]
      exact (Matrix.mul_assoc _ _ _).symm
    · have h' : deltaMat = -((A : Matrix (Fin 4) (Fin 4) (ZMod 3)) * A) := by rw [h, neg_neg]
      rw [h', Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  obtain ⟨a, b, c, d, e, f, g, h', hA⟩ : ∃ a b c d e f g h : ZMod 3,
      (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) = diagBlk a b c d e f g h :=
    ⟨_, _, _, _, _, _, _, _, eq_diagBlk_of_comm _ hcomm⟩
  have hdet : (a * d - b * c) * (e * h' - f * g) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe A
    rwa [hA, diagBlk_det] at this
  refine ⟨a, b, c, d, e, f, g, h', hA, blocks_twin a b c d e f g h' ?_ hdet⟩
  rw [hA, diagBlk_mul] at hsq
  rcases hsq with hsq | hsq
  · exact Or.inl (diagBlk_inj.mp (hsq.trans deltaMat_eq))
  · right
    rw [deltaMat_eq, diagBlk_neg] at hsq
    have := diagBlk_inj.mp hsq
    simp only [neg_neg, neg_zero] at this
    exact this

theorem twinAt_mk_deltaSL :
    TwinAt (QuotientGroup.mk deltaSL : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) := by
  refine twinAt_of_commuting ?_ ?_
  · rw [← QuotientGroup.mk_mul, deltaSL_mul_self, QuotientGroup.mk_one]
  · intro a _ ha2
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective a
    rw [pow_two, ← QuotientGroup.mk_mul, mk_eq_mk_iff] at ha2
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_deltaSL] at ha2
    obtain ⟨a, b, c, d, e, f, g, h, hA, ⟨hc1, hc2, hc3⟩, hn1, hn2⟩ := blk_data A ha2
    have hw : (QuotientGroup.mk swapSL :
        SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3))⁻¹ = QuotientGroup.mk swapSL := by
      rw [← QuotientGroup.mk_inv, swapSL_inv]
    have e1 : (QuotientGroup.mk swapSL : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) *
        QuotientGroup.mk A * (QuotientGroup.mk swapSL)⁻¹ =
          QuotientGroup.mk (swapSL * A * swapSL) := by
      rw [hw]
      simp only [QuotientGroup.mk_mul]
    have key : swapSL * A * swapSL * A = A * (swapSL * A * swapSL) := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_swapSL]
      rw [hA, swapMat_diagBlk]
      exact diagBlk_swap_comm a b c d e f g h hc1 hc2 hc3
    refine ⟨QuotientGroup.mk swapSL, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        mk_eq_mk_iff]
      right
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_swapSL, coe_deltaSL]
      exact swapMat_deltaMat
    · rw [e1, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, key]
    · rw [e1]
      intro hne
      rw [mk_eq_mk_iff] at hne
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_swapSL] at hne
      rw [hA, swapMat_diagBlk] at hne
      rcases hne with hne | hne
      · obtain ⟨h1, h2, h3, h4, -⟩ := diagBlk_inj.mp hne
        exact hn1 ⟨h1, h2, h3, h4⟩
      · rw [diagBlk_neg] at hne
        obtain ⟨h1, h2, h3, h4, -⟩ := diagBlk_inj.mp hne
        exact hn2 ⟨h1, h2, h3, h4⟩
    · rw [e1, ← QuotientGroup.mk_mul]
      intro hne
      rw [mk_eq_mk_iff] at hne
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_swapSL, coe_deltaSL] at hne
      rw [hA, swapMat_diagBlk, diagBlk_mul_deltaMat] at hne
      rcases hne with hne | hne
      · obtain ⟨h1, h2, h3, h4, -⟩ := diagBlk_inj.mp hne
        exact hn2 ⟨h1, h2, h3, h4⟩
      · rw [diagBlk_neg] at hne
        obtain ⟨h1, h2, h3, h4, -⟩ := diagBlk_inj.mp hne
        rw [neg_neg] at h1 h2 h3 h4
        exact hn1 ⟨h1, h2, h3, h4⟩

theorem diag_classes : ∀ a : ℕ, a ≤ 4 →
    (Matrix.diagonal fun j : Fin 4 => if j.val < a then (-1 : ZMod 3) else 1).det = 1 →
      (Matrix.diagonal fun j : Fin 4 => if j.val < a then (-1 : ZMod 3) else 1) = 1 ∨
      (Matrix.diagonal fun j : Fin 4 => if j.val < a then (-1 : ZMod 3) else 1) = -1 ∨
      (Matrix.diagonal fun j : Fin 4 => if j.val < a then (-1 : ZMod 3) else 1) = deltaMat := by
  decide +kernel

end PSL4Twin

theorem twinAt_psl4_of_sq_eq_one (g : SL(4, ZMod 3))
    (hg2 : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * g = 1)
    (hgc : g ∉ Subgroup.center SL(4, ZMod 3)) :
    TwinAt (QuotientGroup.mk g : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) := by
  obtain ⟨a, ha, P, hP⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_sl_conj_diagonal
    (by decide : (2 : ZMod 3) ≠ 0) (by norm_num : 0 < 4) hg2
  have hdet :
      (Matrix.diagonal fun j : Fin 4 => if j.val < a then (-1 : ZMod 3) else 1).det = 1 := by
    have := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul, g.2, P.2, one_mul, one_mul] at this
    exact this.symm
  let D : SL(4, ZMod 3) :=
    ⟨Matrix.diagonal fun j : Fin 4 => if j.val < a then (-1 : ZMod 3) else 1, hdet⟩
  have hgD : g = P * D * P⁻¹ := by
    have h1 : g * P = P * D := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact hP)
    rw [← h1]
    group
  have hcentral : D ∈ Subgroup.center SL(4, ZMod 3) → False := fun hD => hgc (by
    rw [hgD]
    exact (inferInstance : (Subgroup.center SL(4, ZMod 3)).Normal).conj_mem D hD P)
  rcases PSL4Twin.diag_classes a ha hdet with h1 | h1 | h1
  · exact (hcentral ((PSL4Twin.mem_center_sl4 D).mpr (Or.inl h1))).elim
  · exact (hcentral ((PSL4Twin.mem_center_sl4 D).mpr (Or.inr h1))).elim
  · have hDd : D = PSL4Twin.deltaSL := Subtype.ext h1
    have hg : (QuotientGroup.mk g : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) =
        QuotientGroup.mk P * QuotientGroup.mk PSL4Twin.deltaSL * (QuotientGroup.mk P)⁻¹ := by
      rw [hgD, hDd]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hg]
    exact PSL4Twin.twinAt_mk_deltaSL.conj _

end CFSG.CGT.PushingUpLit.SolKNA
