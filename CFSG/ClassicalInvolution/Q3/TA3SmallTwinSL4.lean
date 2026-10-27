module

public import CFSG.GH74.Generic.Front.DataLin
public import CFSG.GH74.Generic.Front.DataUni
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinThree

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution CFSG.GH74.L5U5 Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem model_frame (M : ModelData F) (h2 : (2 : F) ≠ 0) {F' : Type} [Field F']
    (e2 : SL(2, F') ≃* M.H2) : Frame (⊤ : Subgroup ↥M.K4) F' M.xK M.yK M.J2 M.J4 where
  le₂ := le_top
  le₄ := le_top
  mem₂ := M.yK_mem_J2
  mem₄ := by rw [M.xK_mul_yK]; exact M.xyK_mem_J4
  orderOf_xt := by rw [M.xK_mul_yK]; exact M.orderOf_xyK h2
  ne_one := fun h => by
    have := M.orderOf_xK h2
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  equiv₂ := ⟨M.J2EquivH2.trans e2.symm⟩
  equiv₄ := ⟨M.J4EquivH2.trans e2.symm⟩
  comm := fun _ ha _ hb => M.J2_comm_J4 ha hb
  cent₂ := M.J2_le_centralizer
  norm₂ := fun g _ hg j hj => (Subgroup.mem_normalizer_iff.mp
    (M.centralizer_yK_le_normalizer_J2 h2 (Subgroup.mem_centralizer_singleton_iff.mpr hg)) j).mp hj
  norm₄ := fun g _ hg j hj => (Subgroup.mem_normalizer_iff.mp
    (M.centralizer_yK_le_normalizer_J4 h2 (Subgroup.mem_centralizer_singleton_iff.mpr hg)) j).mp hj

theorem lin_conj [Finite F] (hF : Nat.card F % 4 = 3) {u : ↥(ModelData.lin F).K4} (hu : u * u = 1)
    (hc : u ∉ Subgroup.center ↥(ModelData.lin F).K4) :
    ∃ g, g * u * g⁻¹ = (ModelData.lin F).yK :=
  GH74.Generic.hone_of_model _ (mem_center_lin_iff hF)
    (fun t hT h1 hm1 => GH74.Generic.hmat_lin (two_ne_zero_of_odd_card
      (Nat.odd_iff.2 (by omega))) t hT h1 hm1) u hu (fun h => hc (h ▸ Subgroup.one_mem _)) hc

theorem uni_conj [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {u : ↥(ModelData.uni hF).K4} (hu : u * u = 1)
    (hc : u ∉ Subgroup.center ↥(ModelData.uni hF).K4) :
    ∃ g, g * u * g⁻¹ = (ModelData.uni hF).yK := by
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  exact GH74.Generic.hone_of_model _ (mem_center_uni_iff hF hq)
    (fun t hT h1 hm1 => GH74.Generic.hmat_uni hF (two_ne_zero_of_odd_card hodd) t hT h1 hm1) u hu
    (fun h => hc (h ▸ Subgroup.one_mem _)) hc

theorem three_eq_zero [Finite F] (h3 : Nat.card F = 3) : (3 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, h3] at h
  exact_mod_cast h

theorem two_ne_zero_three [Finite F] (h3 : Nat.card F = 3) : (2 : F) ≠ 0 := fun h =>
  one_ne_zero (by linear_combination three_eq_zero h3 - h : (1 : F) = 0)

theorem mul_self_eq_one_three [Finite F] (h3 : Nat.card F = 3) {c : F} (hc : c ≠ 0) :
    c * c = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [← Nat.card_eq_fintype_card, h3, show 3 - 1 = 2 from rfl, sq] at h

theorem det_eq_one_of_sq_three [Finite F] (h3 : Nat.card F = 3) {A : Matrix (Fin 2) (Fin 2) F}
    (hA : A * A = -1) : A.det = 1 := by
  have e : ∀ i j, (A * A) i j = (-1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [hA]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  rw [Matrix.det_fin_two]
  by_cases h : A 0 0 + A 1 1 = 0
  · linear_combination A 0 0 * h - e00
  · exfalso
    have h01 : A 0 1 = 0 :=
      (mul_eq_zero.mp (by linear_combination e01 : A 0 1 * (A 0 0 + A 1 1) = 0)).resolve_right h
    have h10 : A 1 0 = 0 :=
      (mul_eq_zero.mp (by linear_combination e10 : A 1 0 * (A 0 0 + A 1 1) = 0)).resolve_right h
    have hne : A 0 0 ≠ 0 := fun h0 => by
      have : (1 : F) = 0 := by linear_combination e00 - A 0 0 * h0 - A 1 0 * h01
      exact one_ne_zero this
    have hsq := mul_self_eq_one_three h3 hne
    exact one_ne_zero (by
      linear_combination three_eq_zero h3 - e00 + hsq + A 1 0 * h01 : (1 : F) = 0)

theorem eq_scalar_of_comm_three [Finite F] (h3 : Nat.card F = 3) {A : Matrix (Fin 2) (Fin 2) F}
    (hA : ∀ C : Matrix (Fin 2) (Fin 2) F, C.det = 1 → C * C = -1 → A * C = C * A) :
    A = Matrix.scalar (Fin 2) (A 0 0) := by
  have h30 := three_eq_zero h3
  have h₁ := hA !![0, -1; 1, 0] (by simp [Matrix.det_fin_two]) (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
  have h₂ := hA !![1, 1; 1, -1] (by rw [Matrix.det_fin_two_of]; linear_combination -h30) (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination h30)
  have a00 := congrFun (congrFun h₁ 0) 0
  have a01 := congrFun (congrFun h₁ 0) 1
  have b00 := congrFun (congrFun h₂ 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a00 a01 b00
  have hx : A 0 1 = 0 := (mul_eq_zero.mp (by linear_combination a00 + b00 :
    (2 : F) * A 0 1 = 0)).resolve_left (two_ne_zero_three h3)
  have hy : A 1 0 = 0 := by linear_combination hx - b00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hx, hy]
  linear_combination -a01

theorem lin_frame3 [Finite F] (h3 : Nat.card F = 3) :
    Frame3 (⊤ : Subgroup ↥(ModelData.lin F).K4) F (ModelData.lin F).xK (ModelData.lin F).yK
      (ModelData.lin F).J2 (ModelData.lin F).J4 := by
  have h2 := two_ne_zero_three h3
  set M := ModelData.lin F with hM
  have hH : ∀ a : GL (Fin 2) F, a ∈ M.H2 ↔ (a : Matrix (Fin 2) (Fin 2) F).det = 1 := fun a => by
    rw [M.mem_H2]
    exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top a, h⟩⟩
  refine ⟨model_frame M h2 (lin_sl2_equiv_H2 F), h3, fun g => ?_, ?_, ?_⟩
  · exact Subgroup.mem_center_iff.mp M.xK_mem_center g
  · intro n _ hnt hnn
    obtain ⟨a, b, hab, -, -, hdet⟩ := M.exists_diagGL_of_comm h2 n.2 (congrArg Subtype.val hnt)
    have hsq : diagGL (a * a) (b * b) = diagGL (-1 : GL (Fin 2) F) 1 := by
      rw [← diagGL_mul, ← hab]
      exact congrArg Subtype.val hnn
    obtain ⟨haa, hbb⟩ := diagGL_inj hsq
    have hda : (a : Matrix (Fin 2) (Fin 2) F).det = 1 := det_eq_one_of_sq_three h3 (by
      have := congrArg Units.val haa
      simpa using this)
    have hdb : (b : Matrix (Fin 2) (Fin 2) F).det = 1 := by rwa [hda, one_mul] at hdet
    have ha : a ∈ M.H2 := (hH a).2 hda
    refine ⟨⟨blkL F a, M.blkL_mem_K4 ha⟩, M.blkL_mem_J2 ha, ?_⟩
    rcases CFSG.ComponentClassification.CatFactsSp4.eq_one_or_neg_one_of_sq h2 hdb (by
      have := congrArg Units.val hbb
      simpa using this) with hb | hb
    · left
      apply Subtype.ext
      show (n : GL (Fin 4) F) = blkL F a
      rw [hab, blkL_apply, show b = 1 from Units.ext hb]
    · right
      apply Subtype.ext
      show (n : GL (Fin 4) F) = xGL F * yGL F * blkL F a
      rw [hab, blkL_apply, xGL, yGL, diagGL_mul, diagGL_mul,
        show b = -1 from Units.ext (by rw [hb]; simp)]
      congr 1 <;> simp
  · intro g _ hgt hgb
    obtain ⟨a, c, hac, -, -, hdet⟩ := M.exists_diagGL_of_comm h2 g.2 (congrArg Subtype.val hgt)
    have hcomm : ∀ C : Matrix (Fin 2) (Fin 2) F, C.det = 1 → C * C = -1 →
        (a : Matrix (Fin 2) (Fin 2) F) * C = C * a := by
      intro C hC hCC
      let s : GL (Fin 2) F := Matrix.GeneralLinearGroup.mk'' C (by rw [hC]; exact isUnit_one)
      have hs : s ∈ M.H2 := (hH s).2 hC
      have hss : (⟨blkL F s, M.blkL_mem_K4 hs⟩ : ↥M.K4) * ⟨blkL F s, M.blkL_mem_K4 hs⟩ =
          M.yK := by
        apply Subtype.ext
        show blkL F s * blkL F s = blkL F (-1)
        rw [← map_mul]
        exact congrArg (blkL F) (Units.ext (by simpa [s] using hCC))
      have h1 := congrArg Subtype.val (hgb _ (M.blkL_mem_J2 hs) hss)
      have h1' : diagGL (a * s) c = diagGL (s * a) c := by
        have e1 : (g : GL (Fin 4) F) * blkL F s = blkL F s * g := h1
        rwa [hac, blkL_apply, diagGL_mul, diagGL_mul, one_mul, mul_one] at e1
      have := congrArg Units.val (diagGL_inj h1').1
      simpa [s] using this
    have hsc := eq_scalar_of_comm_three h3 hcomm
    have hda : (a : Matrix (Fin 2) (Fin 2) F).det =
        (a : Matrix (Fin 2) (Fin 2) F) 0 0 * (a : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      conv_lhs => rw [hsc]
      simp only [Matrix.det_fin_two, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Matrix.diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide)]
      ring
    have hl0 : (a : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := fun h0 => by
      rw [hda, h0, mul_zero, zero_mul] at hdet
      exact zero_ne_one hdet
    have hll := mul_self_eq_one_three h3 hl0
    have hdc : (c : Matrix (Fin 2) (Fin 2) F).det = 1 := by rwa [hda, hll, one_mul] at hdet
    have hc : c ∈ M.H2 := (hH c).2 hdc
    refine ⟨⟨blkR F c, M.blkR_mem_K4 hc⟩, M.blkR_mem_J4 hc, ?_⟩
    rcases mul_self_eq_one_iff.mp hll with hl | hl
    · left
      apply Subtype.ext
      show (g : GL (Fin 4) F) = blkR F c
      rw [hac, blkR_apply, show a = 1 from Units.ext (by
        rw [hsc, hl]; ext i j; fin_cases i <;> fin_cases j <;> simp)]
    · right
      apply Subtype.ext
      show (g : GL (Fin 4) F) = yGL F * blkR F c
      rw [hac, blkR_apply, yGL, diagGL_mul, show a = -1 from Units.ext (by
        rw [hsc, hl]; ext i j; fin_cases i <;> fin_cases j <;> simp)]
      congr 1 <;> simp

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
