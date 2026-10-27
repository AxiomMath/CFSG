module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411L34Q
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.QuasithinUnique.Lin2.L34

open Matrix MatrixGroups

structure F4 (F : Type) [Field F] : Prop where
  two : (2 : F) = 0
  frob : ∀ x : F, x ^ 4 = x
  exists_ω : ∃ w : F, w ≠ 0 ∧ w ≠ 1

variable {F : Type} [Field F]

theorem F4.cube (h : F4 F) {x : F} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have h4 := h.frob x
  have : x * (x ^ 3 - 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.1 this with h0 | h1
  · exact absurd h0 hx
  · exact sub_eq_zero.1 h1

theorem F4.add_self (h : F4 F) (x : F) : x + x = 0 := by
  have : x + x = 2 * x := by ring
  rw [this, h.two, zero_mul]

theorem F4.of_card [Fintype F] (h : Fintype.card F = 4) : F4 F where
  two := two_eq_zero_of_card (n := 2) (by norm_num) (by rw [h]; norm_num)
  frob x := by
    have := FiniteField.pow_card x
    rwa [h] at this
  exists_ω := by
    by_contra hcon
    push Not at hcon
    have hs : Function.Surjective (fun b : Bool => if b then (1 : F) else 0) := by
      intro y
      by_cases hy0 : y = 0
      · exact ⟨false, by simp [hy0]⟩
      · exact ⟨true, by simp [hcon y hy0]⟩
    have := Fintype.card_le_of_surjective _ hs
    rw [h] at this
    simp at this

@[expose] def uT (a b c : F) : SL(3, F) :=
  ⟨!![1, a, c; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem uT_mul (a b c a' b' c' : F) :
    uT a b c * uT a' b' c' = uT (a + a') (b + b') (c + c' + a * b') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uT, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uT_one : uT (0 : F) 0 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uT]

theorem uT_inv (a b c : F) : (uT a b c)⁻¹ = uT (-a) (-b) (a * b - c) := by
  rw [inv_eq_iff_mul_eq_one, uT_mul]
  have h1 : (a + -a) = 0 := by ring
  have h2 : (b + -b) = 0 := by ring
  have h3 : c + (a * b - c) + a * -b = 0 := by ring
  rw [h1, h2, h3, uT_one]

theorem uT_injective : Function.Injective (fun p : F × F × F => uT p.1 p.2.1 p.2.2) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h01 := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  have h12 := congrFun (congrFun (congrArg Subtype.val h) 1) 2
  have h02 := congrFun (congrFun (congrArg Subtype.val h) 0) 2
  simp [uT] at h01 h12 h02
  simp [h01, h12, h02]

@[expose] def UT : Subgroup SL(3, F) where
  carrier := {M | ∃ a b c, M = uT a b c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, uT_mul _ _ _ _ _ _⟩
  one_mem' := ⟨0, 0, 0, uT_one.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, uT_inv _ _ _⟩

@[expose] def Xs : Subgroup SL(3, F) where
  carrier := {M | ∃ a c, M = uT a 0 c}
  mul_mem' := by
    rintro _ _ ⟨a, c, rfl⟩ ⟨a', c', rfl⟩
    exact ⟨a + a', c + c', by rw [uT_mul]; simp⟩
  one_mem' := ⟨0, 0, uT_one.symm⟩
  inv_mem' := by
    rintro _ ⟨a, c, rfl⟩
    exact ⟨-a, -c, by rw [uT_inv]; simp⟩

@[expose] def Ys : Subgroup SL(3, F) where
  carrier := {M | ∃ b c, M = uT 0 b c}
  mul_mem' := by
    rintro _ _ ⟨b, c, rfl⟩ ⟨b', c', rfl⟩
    exact ⟨b + b', c + c', by rw [uT_mul]; simp⟩
  one_mem' := ⟨0, 0, uT_one.symm⟩
  inv_mem' := by
    rintro _ ⟨b, c, rfl⟩
    exact ⟨-b, -c, by rw [uT_inv]; simp⟩

theorem mem_center_iff {z : SL(3, F)} :
    z ∈ Subgroup.center SL(3, F) ↔ ∃ r : F, r ^ 3 = 1 ∧ scalar (Fin 3) r = (z : Matrix (Fin 3) (Fin 3) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  simp

@[expose] def sc (r : F) (hr : r ^ 3 = 1) : SL(3, F) :=
  ⟨scalar (Fin 3) r, by
    rw [Matrix.scalar_apply, Matrix.det_diagonal]
    simp [hr]⟩

theorem sc_val (r : F) (hr : r ^ 3 = 1) :
    (sc r hr : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) r := rfl

theorem sc_mem_center (r : F) (hr : r ^ 3 = 1) : sc r hr ∈ Subgroup.center SL(3, F) :=
  mem_center_iff.2 ⟨r, hr, rfl⟩

theorem center_entries {z : SL(3, F)} (hz : z ∈ Subgroup.center SL(3, F)) :
    ∃ r : F, r ^ 3 = 1 ∧ z.1 0 0 = r ∧ z.1 1 1 = r ∧ z.1 2 2 = r ∧ z.1 0 1 = 0 ∧ z.1 0 2 = 0 ∧
      z.1 1 0 = 0 ∧ z.1 1 2 = 0 ∧ z.1 2 0 = 0 ∧ z.1 2 1 = 0 := by
  obtain ⟨r, hr, hz⟩ := mem_center_iff.1 hz
  refine ⟨r, hr, ?_⟩
  rw [← hz]
  simp [Matrix.scalar_apply]

@[expose] def Pst0 : Subgroup SL(3, F) where
  carrier := {g | g.1 1 0 = 0 ∧ g.1 2 0 = 0}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    constructor <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg1, hg2, hh1, hh2]
  one_mem' := by
    constructor <;> simp
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    constructor <;>
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, hg1, hg2]

theorem mem_Pst0 {g : SL(3, F)} : g ∈ (Pst0 : Subgroup SL(3, F)) ↔ g.1 1 0 = 0 ∧ g.1 2 0 = 0 :=
  Iff.rfl

theorem det_Pst0 {g : SL(3, F)} (hg : g ∈ (Pst0 : Subgroup SL(3, F))) :
    g.1 0 0 * (g.1 1 1 * g.1 2 2 - g.1 1 2 * g.1 2 1) = 1 := by
  obtain ⟨h1, h2⟩ := hg
  have := g.2
  rw [Matrix.det_fin_three, h1, h2] at this
  linear_combination this

theorem conj_Xs {g : SL(3, F)} (hg : g ∈ (Pst0 : Subgroup SL(3, F))) (a c : F) :
    g * uT a 0 c * g⁻¹ =
      uT ((g.1 0 0) ^ 2 * (a * g.1 2 2 - c * g.1 2 1)) 0
        ((g.1 0 0) ^ 2 * (-(a * g.1 1 2) + c * g.1 1 1)) := by
  rw [mul_inv_eq_iff_eq_mul]
  have hd := det_Pst0 hg
  obtain ⟨h1, h2⟩ := hg
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uT, Matrix.mul_apply, Fin.sum_univ_three, h1, h2]
  · linear_combination (-(g.1 0 0 * a)) * hd
  · linear_combination (-(g.1 0 0 * c)) * hd

theorem aux_zero (r u v : F) (h1 : r * u = u) (h2 : r * v = u + v) : u = 0 := by
  by_cases hr : r = 1
  · subst hr
    simpa using h2
  · have : (r - 1) * u = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hr
    · exact h

@[expose] def XZ : Subgroup SL(3, F) := Xs ⊔ Subgroup.center SL(3, F)

theorem mem_XZ {y : SL(3, F)} :
    y ∈ (XZ : Subgroup SL(3, F)) ↔
      ∃ x ∈ (Xs : Subgroup SL(3, F)), ∃ z ∈ Subgroup.center SL(3, F), x * z = y :=
  Subgroup.mem_sup_of_normal_right

@[expose] def Pst : Subgroup SL(3, F) := Subgroup.normalizer ((XZ : Subgroup SL(3, F)) : Set SL(3, F))

theorem mem_Pst_iff {g : SL(3, F)} :
    g ∈ (Pst : Subgroup SL(3, F)) ↔ g.1 1 0 = 0 ∧ g.1 2 0 = 0 := by
  constructor
  · intro hg
    have hx₁ : uT (1 : F) 0 0 ∈ (XZ : Subgroup SL(3, F)) :=
      Subgroup.mem_sup_left ⟨1, 0, rfl⟩
    have h1 : g * uT (1 : F) 0 0 * g⁻¹ ∈ (XZ : Subgroup SL(3, F)) :=
      (Subgroup.mem_normalizer_iff.1 hg _).1 hx₁
    obtain ⟨x, ⟨a, c, rfl⟩, z, hz, hxz⟩ := mem_XZ.1 h1
    obtain ⟨r, -, hz00, hz11, hz22, hz01, hz02, hz10, hz12, hz20, hz21⟩ := center_entries hz
    have e : (uT a 0 c * z) * g = g * uT 1 0 0 := by
      rw [hxz]
      group
    have eM : (uT a 0 c : Matrix (Fin 3) (Fin 3) F) * z.1 * g.1 =
        g.1 * (uT (1 : F) 0 0 : Matrix (Fin 3) (Fin 3) F) := by
      have := congrArg Subtype.val e
      simpa [Matrix.SpecialLinearGroup.coe_mul, mul_assoc] using this
    have hzm : z.1 = !![r, 0, 0; 0, r, 0; 0, 0, r] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz00, hz11, hz22, hz01, hz02, hz10, hz12, hz20, hz21]
    rw [hzm] at eM
    constructor
    · have h10 := congrFun (congrFun eM 1) 0
      have h11 := congrFun (congrFun eM 1) 1
      simp [uT, Matrix.mul_apply, Fin.sum_univ_three] at h10 h11
      exact aux_zero r _ _ h10 h11
    · have h20 := congrFun (congrFun eM 2) 0
      have h21 := congrFun (congrFun eM 2) 1
      simp [uT, Matrix.mul_apply, Fin.sum_univ_three] at h20 h21
      exact aux_zero r _ _ h20 h21
  · intro hg
    have hP : g ∈ (Pst0 : Subgroup SL(3, F)) := hg
    have hconj : ∀ g ∈ (Pst0 : Subgroup SL(3, F)), ∀ y ∈ (XZ : Subgroup SL(3, F)),
        g * y * g⁻¹ ∈ (XZ : Subgroup SL(3, F)) := by
      intro g hg y hy
      obtain ⟨x, ⟨a, c, rfl⟩, z, hz, rfl⟩ := mem_XZ.1 hy
      have hzg : g⁻¹ * z = z * g⁻¹ := Subgroup.mem_center_iff.1 hz g⁻¹
      have e : g * (uT a 0 c * z) * g⁻¹ = (g * uT a 0 c * g⁻¹) * z := by
        calc g * (uT a 0 c * z) * g⁻¹ = g * uT a 0 c * (z * g⁻¹) := by group
          _ = g * uT a 0 c * (g⁻¹ * z) := by rw [hzg]
          _ = (g * uT a 0 c * g⁻¹) * z := by group
      rw [e, conj_Xs hg a c]
      exact mem_XZ.2 ⟨_, ⟨_, _, rfl⟩, z, hz, rfl⟩
    exact le_normalizer_of_conj_mem hconj hP

@[expose] def psiMat (g : SL(3, F)) : Matrix (Fin 2) (Fin 2) F :=
  !![(g.1 0 0) ^ 2 * g.1 1 1, (g.1 0 0) ^ 2 * g.1 1 2;
    (g.1 0 0) ^ 2 * g.1 2 1, (g.1 0 0) ^ 2 * g.1 2 2]

theorem det_psiMat (hF : F4 F) {g : SL(3, F)} (hg : g ∈ (Pst0 : Subgroup SL(3, F))) :
    (psiMat g).det = 1 := by
  have hd := det_Pst0 hg
  have hα : g.1 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hd
    exact zero_ne_one hd
  have h3 := hF.cube hα
  rw [psiMat, Matrix.det_fin_two_of]
  linear_combination (g.1 0 0 ^ 3) * hd + h3

@[expose] def psiSL (hF : F4 F) (g : ↥(Pst0 : Subgroup SL(3, F))) : SL(2, F) :=
  ⟨psiMat g, det_psiMat hF g.2⟩

theorem psiSL_val (hF : F4 F) (g : ↥(Pst0 : Subgroup SL(3, F))) :
    ((psiSL hF g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = psiMat g := rfl

@[expose] def psi (hF : F4 F) : ↥(Pst0 : Subgroup SL(3, F)) →* SL(2, F) where
  toFun := psiSL hF
  map_one' := by
    apply Subtype.ext
    rw [psiSL_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [psiMat]
  map_mul' g h := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, psiSL_val, psiSL_val, psiSL_val]
    obtain ⟨hg1, hg2⟩ := g.2
    obtain ⟨hh1, hh2⟩ := h.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [psiMat, Matrix.mul_apply, Fin.sum_univ_three, hg1, hg2, hh1, hh2] <;> ring

theorem psi_val (hF : F4 F) (g : ↥(Pst0 : Subgroup SL(3, F))) :
    ((psi hF g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = psiMat g := rfl

theorem psi_surjective (hF : F4 F) : Function.Surjective (psi hF) := by
  intro M
  let g : SL(3, F) := ⟨!![1, 0, 0; 0, M.1 0 0, M.1 0 1; 0, M.1 1 0, M.1 1 1], by
    have := M.2
    rw [Matrix.det_fin_two] at this
    rw [Matrix.det_fin_three]
    simp
    linear_combination this⟩
  have hg : g ∈ (Pst0 : Subgroup SL(3, F)) := by
    constructor <;> simp [g]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  rw [psi_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [psiMat, g]

theorem psi_ker (hF : F4 F) (g : ↥(Pst0 : Subgroup SL(3, F))) :
    psi hF g = 1 ↔ (g : SL(3, F)) ∈ (Xs : Subgroup SL(3, F)) ⊔ Subgroup.center SL(3, F) := by
  have hd := det_Pst0 g.2
  obtain ⟨hg1, hg2⟩ := g.2
  have hα : g.1.1 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hd
    exact zero_ne_one hd
  have hα3 := hF.cube hα
  constructor
  · intro h
    have hM : psiMat (g : SL(3, F)) = 1 := by
      have := congrArg Subtype.val h
      simpa [psi_val] using this
    have e00 := congrFun (congrFun hM 0) 0
    have e01 := congrFun (congrFun hM 0) 1
    have e10 := congrFun (congrFun hM 1) 0
    have e11 := congrFun (congrFun hM 1) 1
    simp [psiMat] at e00 e01 e10 e11
    have hq : g.1.1 1 2 = 0 := by
      rcases e01 with h | h
      · exact absurd h hα
      · exact h
    have hs : g.1.1 2 1 = 0 := by
      rcases e10 with h | h
      · exact absurd h hα
      · exact h
    have hp : g.1.1 1 1 = g.1.1 0 0 := by
      have : g.1.1 1 1 = g.1.1 0 0 ^ 3 * g.1.1 1 1 := by rw [hα3, one_mul]
      rw [this]
      linear_combination (g.1.1 0 0) * e00
    have ht : g.1.1 2 2 = g.1.1 0 0 := by
      have : g.1.1 2 2 = g.1.1 0 0 ^ 3 * g.1.1 2 2 := by rw [hα3, one_mul]
      rw [this]
      linear_combination (g.1.1 0 0) * e11
    have hdec : (g : SL(3, F)) =
        sc (g.1.1 0 0) hα3 * uT ((g.1.1 0 0)⁻¹ * g.1.1 0 1) 0 ((g.1.1 0 0)⁻¹ * g.1.1 0 2) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sc_val, uT, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three, hg1, hg2,
          hq, hs, hp, ht] <;> field_simp
    rw [hdec]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (sc_mem_center _ hα3))
      (Subgroup.mem_sup_left ⟨_, _, rfl⟩)
  · intro h
    obtain ⟨x, ⟨a, c, rfl⟩, z, hz, hxz⟩ := mem_XZ.1 h
    obtain ⟨r, hr, hz00, hz11, hz22, hz01, hz02, hz10, hz12, hz20, hz21⟩ := center_entries hz
    have hzm : z.1 = !![r, 0, 0; 0, r, 0; 0, 0, r] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz00, hz11, hz22, hz01, hz02, hz10, hz12, hz20, hz21]
    have hgm : g.1.1 = (uT a 0 c : Matrix (Fin 3) (Fin 3) F) * !![r, 0, 0; 0, r, 0; 0, 0, r] := by
      rw [← hzm, ← Matrix.SpecialLinearGroup.coe_mul, hxz]
    apply Subtype.ext
    rw [psi_val]
    ext i j
    simp only [psiMat]
    rw [hgm]
    fin_cases i <;> fin_cases j <;> simp [uT, Matrix.mul_apply, Fin.sum_univ_three] <;>
      linear_combination hr

theorem fix_Xs (hF : F4 F) {x : SL(3, F)} (hx : x ∈ (Xs : Subgroup SL(3, F)))
    (h : ∀ g ∈ (Pst0 : Subgroup SL(3, F)), g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center SL(3, F)) :
    x = 1 := by
  obtain ⟨a, c, rfl⟩ := hx
  obtain ⟨w, hw0, hw1⟩ := hF.exists_ω
  have hw3 := hF.cube hw0
  let d : SL(3, F) := ⟨!![w, 0, 0; 0, w ^ 2, 0; 0, 0, 1], by
    simp [Matrix.det_fin_three]
    linear_combination hw3⟩
  have hd : d ∈ (Pst0 : Subgroup SL(3, F)) := by
    constructor <;> simp [d]
  have hconj : d * uT a 0 c = uT (w ^ 2 * a) 0 (w * c) * d := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have h4 := hF.frob w
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d, uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (-a) * h4
  have e : d * uT a 0 c * d⁻¹ * (uT a 0 c)⁻¹ = uT (w ^ 2 * a - a) 0 (w * c - c) := by
    rw [hconj, mul_inv_cancel_right, uT_inv, uT_mul]
    congr 1 <;> ring
  have hz := h d hd
  rw [e] at hz
  obtain ⟨r, -, -, -, -, hz01, hz02, -⟩ := center_entries hz
  simp [uT] at hz01 hz02
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.2 hw1
  have hc : c = 0 := by
    have : (w - 1) * c = 0 := by linear_combination hz02
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hw1'
    · exact h0
  have ha : a = 0 := by
    have h2 : w ^ 2 - 1 = (w - 1) ^ 2 := by linear_combination (w - 1) * hF.two
    have : (w - 1) ^ 2 * a = 0 := by linear_combination hz01 - a * h2
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h0) hw1'
    · exact h0
  rw [ha, hc, uT_one]

theorem sl2_simple [Fintype F] (hcard : Fintype.card F = 4) :
    IsSimpleGroup SL(2, F) := by
  have hF := F4.of_card hcard
  have hN : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hcard]
  have hP : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by rw [hN]; norm_num))
      (Or.inr (by rw [hN]; norm_num))
  have hc : Subgroup.center SL(2, F) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
    obtain ⟨r, hr, hzr⟩ := hz
    simp only [Fintype.card_fin] at hr
    have hr1 : r = 1 := by
      have : (r - 1) ^ 2 = 0 := by linear_combination hr - r * hF.two + hF.two
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hzr, hr1]
    simp
  have e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem normProps_Xs [Fintype F] (hcard : Fintype.card F = 4) :
    NormProps ((Xs : Subgroup SL(3, F)).map (QuotientGroup.mk' (Subgroup.center SL(3, F)))) := by
  have hF := F4.of_card hcard
  have := sl2_simple hcard
  refine normProps_quotient (Z := Subgroup.center SL(3, F)) (X := Xs) (P := Pst0) (T := SL(2, F))
    (fun g => (mem_Pst0).trans (mem_Pst_iff (g := g)).symm) (psi hF) (psi_surjective hF)
    (fun g => psi_ker hF g) (fun x hx h => fix_Xs hF hx h)

end CFSG.QuasithinUnique.Lin2.L34
