module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.Timmesfeld.RankTwo.SLThreeGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatalogueBHigherLinearAction


variable {F : Type} [Field F]

private lemma tv_eq_uSL (c : F) :
    CFSG.Timmesfeld.tv (n := 2) 0 1 c = uSL c := by
  rw [CFSG.Timmesfeld.tv_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, coe_uSL]

private lemma tv_eq_vSL (c : F) :
    CFSG.Timmesfeld.tv (n := 2) 1 0 c = vSL c := by
  rw [CFSG.Timmesfeld.tv_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, coe_vSL]

private def diagGL {n : ℕ} (d : Fin n → F) (hd : ∀ k, d k ≠ 0) :
    Matrix.GeneralLinearGroup (Fin n) F where
  val := Matrix.diagonal d
  inv := Matrix.diagonal fun k => (d k)⁻¹
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hd k)
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact inv_mul_cancel₀ (hd k)

private lemma diagonal_mul_single_mul_diagonal_inv {n : ℕ} (d : Fin n → F)
    (i j : Fin n) (c : F) :
    Matrix.diagonal d * Matrix.single i j c * Matrix.diagonal (fun k => (d k)⁻¹) =
      Matrix.single i j (d i * c * (d j)⁻¹) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp_all

private lemma diagonal_conj_transvection {n : ℕ} (d : Fin n → F) (hd : ∀ k, d k ≠ 0)
    {i j : Fin n} (hij : i ≠ j) (c : F) :
    Matrix.diagonal d * Matrix.transvection i j c * Matrix.diagonal (fun k => (d k)⁻¹) =
      Matrix.transvection i j (d i * (d j)⁻¹ * c) := by
  have h1 : Matrix.diagonal d * Matrix.diagonal (fun k => (d k)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hd k)
  rw [Matrix.transvection, Matrix.transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
    h1, diagonal_mul_single_mul_diagonal_inv,
    show d i * c * (d j)⁻¹ = d i * (d j)⁻¹ * c by ring]

private lemma slConj_diag_transvection {n : ℕ} (d : Fin n → F) (hd : ∀ k, d k ≠ 0)
    {i j : Fin n} (hij : i ≠ j) (c : F) :
    slConjugation n F (diagGL d hd) (CFSG.Timmesfeld.tv i j c) =
      CFSG.Timmesfeld.tv i j (d i * (d j)⁻¹ * c) := by
  apply Subtype.ext
  rw [slConjugation_matrix, CFSG.Timmesfeld.tv_of_ne hij, CFSG.Timmesfeld.tv_of_ne hij]
  change Matrix.diagonal d * Matrix.transvection i j c * Matrix.diagonal (fun k => (d k)⁻¹) =
    Matrix.transvection i j (d i * (d j)⁻¹ * c)
  exact diagonal_conj_transvection d hd hij c

private def block01Fun (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![(g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
      (g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1, 0;
      0, 0, 1], by
    rw [Matrix.det_fin_three]
    simpa using (det_SL2 g)⟩

private lemma block01Fun_apply (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (block01Fun g : Matrix (Fin 3) (Fin 3) F) =
      !![(g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
        (g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1, 0;
        0, 0, 1] := rfl

private def block01 : Matrix.SpecialLinearGroup (Fin 2) F →*
    Matrix.SpecialLinearGroup (Fin 3) F where
  toFun := block01Fun
  map_one' := by
    apply Subtype.ext
    rw [block01Fun_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := by
    intro g g'
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, block01Fun_apply, block01Fun_apply, block01Fun_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_two]
    all_goals ring

private lemma block01_uSL (c : F) :
    block01 (uSL c) = CFSG.Timmesfeld.tv (n := 3) 0 1 c := by
  apply Subtype.ext
  show (block01Fun (uSL c) : Matrix (Fin 3) (Fin 3) F) =
    (CFSG.Timmesfeld.tv (n := 3) 0 1 c : Matrix (Fin 3) (Fin 3) F)
  rw [block01Fun_apply, CFSG.Timmesfeld.tv_of_ne (show (0 : Fin 3) ≠ 1 by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_uSL,Matrix.SpecialLinearGroup.transvection_coe]

private lemma block01_vSL (c : F) :
    block01 (vSL c) = CFSG.Timmesfeld.tv (n := 3) 1 0 c := by
  apply Subtype.ext
  show (block01Fun (vSL c) : Matrix (Fin 3) (Fin 3) F) =
    (CFSG.Timmesfeld.tv (n := 3) 1 0 c : Matrix (Fin 3) (Fin 3) F)
  rw [block01Fun_apply, CFSG.Timmesfeld.tv_of_ne (show (1 : Fin 3) ≠ 0 by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_vSL,Matrix.SpecialLinearGroup.transvection_coe]

private lemma block01_HSL (t : Fˣ) :
    (block01 (HSL t) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![↑t, ↑(t⁻¹), 1] := by
  show (block01Fun (HSL t) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![↑t, ↑(t⁻¹), 1]
  rw [block01Fun_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_HSL]

private def block12Fun (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0;
      0, (g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 0 1;
      0, (g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1], by
    rw [Matrix.det_fin_three]
    simpa using (det_SL2 g)⟩

private lemma block12Fun_apply (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (block12Fun g : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0;
        0, (g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 0 1;
        0, (g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1] := rfl

private def block12 : Matrix.SpecialLinearGroup (Fin 2) F →*
    Matrix.SpecialLinearGroup (Fin 3) F where
  toFun := block12Fun
  map_one' := by
    apply Subtype.ext
    rw [block12Fun_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := by
    intro g g'
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, block12Fun_apply, block12Fun_apply, block12Fun_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_two]
    all_goals ring

private lemma block12_uSL (c : F) :
    block12 (uSL c) = CFSG.Timmesfeld.tv (n := 3) 1 2 c := by
  apply Subtype.ext
  show (block12Fun (uSL c) : Matrix (Fin 3) (Fin 3) F) =
    (CFSG.Timmesfeld.tv (n := 3) 1 2 c : Matrix (Fin 3) (Fin 3) F)
  rw [block12Fun_apply, CFSG.Timmesfeld.tv_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_uSL,Matrix.SpecialLinearGroup.transvection_coe]

private lemma block12_vSL (c : F) :
    block12 (vSL c) = CFSG.Timmesfeld.tv (n := 3) 2 1 c := by
  apply Subtype.ext
  show (block12Fun (vSL c) : Matrix (Fin 3) (Fin 3) F) =
    (CFSG.Timmesfeld.tv (n := 3) 2 1 c : Matrix (Fin 3) (Fin 3) F)
  rw [block12Fun_apply, CFSG.Timmesfeld.tv_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_vSL,Matrix.SpecialLinearGroup.transvection_coe]

private lemma block12_HSL (t : Fˣ) :
    (block12 (HSL t) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![1, ↑t, ↑(t⁻¹)] := by
  show (block12Fun (HSL t) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![1, ↑t, ↑(t⁻¹)]
  rw [block12Fun_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_HSL]

private lemma sl3_conjDiag_hom {i j : Fin TwistTag.E6.tag.rank}
    (ι : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F)
    (hι : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c ∧
      ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) (d : Fin 3 → F) (hd : ∀ k : Fin 3, d k ≠ 0)
    (h0 : d 0 = (b i : F)) (h1 : d 1 = 1) (h2 : d 2 = (↑(b j))⁻¹) :
    (MulAut.conj (rootDiagUnit TwistTag.E6.tag b)).toMonoidHom.comp ι =
      ι.comp (slConjugation 3 F (diagGL d hd)).toMonoidHom := by
  refine MonoidHom.eq_of_eqOn_dense (CFSG.Timmesfeld.closure_tv_three (F := F)) ?_
  intro g hg
  simp only [Set.mem_union, Set.mem_setOf_eq] at hg
  rcases hg with ((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(hι c).1, (root_diagonal_conjugation TwistTag.E6.tag F b).1 i c,
      slConj_diag_transvection (n := 3) d hd (i := 0) (j := 1) (by decide) c, (hι _).1]
    congr 1
    simp [h0, h1]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(hι c).2.1, (root_diagonal_conjugation TwistTag.E6.tag F b).2.1 i c,
      slConj_diag_transvection (n := 3) d hd (i := 1) (j := 0) (by decide) c, (hι _).2.1]
    congr 1
    simp [h0, h1]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(hι c).2.2.1, (root_diagonal_conjugation TwistTag.E6.tag F b).1 j c,
      slConj_diag_transvection (n := 3) d hd (i := 1) (j := 2) (by decide) c, (hι _).2.2.1]
    congr 1
    simp [h1, h2]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(hι c).2.2.2, (root_diagonal_conjugation TwistTag.E6.tag F b).2.1 j c,
      slConj_diag_transvection (n := 3) d hd (i := 2) (j := 1) (by decide) c, (hι _).2.2.2]
    congr 1
    simp [h1, h2]

theorem exists_diag_conj_sl3 {i j : Fin TwistTag.E6.tag.rank}
    (ι : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F)
    (hι : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c ∧
      ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) :
    ∃ D : Matrix.GeneralLinearGroup (Fin 3) F,
      (∀ a a' : Fin 3, a ≠ a' → (D : Matrix (Fin 3) (Fin 3) F) a a' = 0) ∧
      ∀ g, rootDiagUnit TwistTag.E6.tag b * ι g * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
        ι (slConjugation 3 F D g) := by
  let d : Fin 3 → F := ![↑(b i), 1, (↑(b j))⁻¹]
  have hd : ∀ k : Fin 3, d k ≠ 0 := by
    intro k
    fin_cases k
    · simpa [d] using (b i).ne_zero
    · simpa [d] using one_ne_zero
    · simpa [d] using inv_ne_zero (b j).ne_zero
  refine ⟨diagGL d hd, ?_, ?_⟩
  · intro a a' haa'
    change Matrix.diagonal d a a' = 0
    rw [Matrix.diagonal_apply, if_neg haa']
  · have hφψ := sl3_conjDiag_hom ι hι b d hd (by simp [d]) (by simp [d]) (by simp [d])
    intro g
    exact DFunLike.congr_fun hφψ g

theorem exists_diag_conj_sl2 {k : Fin TwistTag.E6.tag.rank}
    (ι : Matrix.SpecialLinearGroup (Fin 2) F →* ModGL TwistTag.E6.tag F)
    (hι : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F k c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F k c)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) :
    ∃ D : Matrix.GeneralLinearGroup (Fin 2) F,
      (∀ a a' : Fin 2, a ≠ a' → (D : Matrix (Fin 2) (Fin 2) F) a a' = 0) ∧
      ∀ g, rootDiagUnit TwistTag.E6.tag b * ι g * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
        ι (slConjugation 2 F D g) := by
  let d : Fin 2 → F := ![↑(b k), 1]
  have hd : ∀ m : Fin 2, d m ≠ 0 := by
    intro m
    fin_cases m
    · simpa [d] using (b k).ne_zero
    · simpa [d] using one_ne_zero
  refine ⟨diagGL d hd, ?_, ?_⟩
  · intro a a' haa'
    change Matrix.diagonal d a a' = 0
    rw [Matrix.diagonal_apply, if_neg haa']
  · intro g
    let φ : Matrix.SpecialLinearGroup (Fin 2) F →* ModGL TwistTag.E6.tag F :=
      (MulAut.conj (rootDiagUnit TwistTag.E6.tag b)).toMonoidHom.comp ι
    let ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ModGL TwistTag.E6.tag F :=
      ι.comp (slConjugation 2 F (diagGL d hd)).toMonoidHom
    have hφψ : φ = ψ := by
      refine MonoidHom.eq_of_eqOn_dense (CFSG.Timmesfeld.closure_tv_two (F := F)) ?_
      rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · dsimp only [φ, ψ]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [(hι c).1, (root_diagonal_conjugation TwistTag.E6.tag F b).1 k c,
          slConj_diag_transvection (n := 2) d hd (i := 0) (j := 1) (by decide) c,
          (hι _).1]
        congr 1
        simp [d]
      · dsimp only [φ, ψ]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [(hι c).2, (root_diagonal_conjugation TwistTag.E6.tag F b).2.1 k c,
          slConj_diag_transvection (n := 2) d hd (i := 1) (j := 0) (by decide) c,
          (hι _).2]
        congr 1
        simp [d]
    exact DFunLike.congr_fun hφψ g

private lemma sl3_diag_eq_block_prod (a b c : F) (ha : a ≠ 0)
    (hcEq : c = (a * b)⁻¹) (t u : Fˣ) (ht : (t : F) = a) (hu : (u : F) = a * b)
    {h : Matrix.SpecialLinearGroup (Fin 3) F}
    (hdiag : (h : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![a, b, c]) :
    h = block01 (HSL t) * block12 (HSL u) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, block01_HSL, block12_HSL, hdiag,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  fin_cases p
  · change a = (↑t : F) * 1
    rw [mul_one, ht]
  · change b = (↑(t⁻¹) : F) * (↑u : F)
    rw [show (↑(t⁻¹) : F) = a⁻¹ by rw [Units.val_inv_eq_inv_val, ht], hu, ← mul_assoc,
      inv_mul_cancel₀ ha, one_mul]
  · change c = (1 : F) * (↑(u⁻¹) : F)
    rw [one_mul, show (↑(u⁻¹) : F) = (a * b)⁻¹ by rw [Units.val_inv_eq_inv_val, hu]]
    exact hcEq

private lemma sl3_block_torus {i j : Fin TwistTag.E6.tag.rank}
    (ι : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F)
    (hι : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c ∧
      ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c)
    (t u : Fˣ) :
    ι (block01 (HSL t)) = torusElt TwistTag.E6.tag F i t ∧
      ι (block12 (HSL u)) = torusElt TwistTag.E6.tag F j u := by
  constructor
  · have hI : ι.comp block01 = simpleRootSL2 TwistTag.E6.tag F i := by
      refine eq_simpleRootSL2 i ?_ ?_
      · intro c'
        show ι (block01 (uSL c')) = xUnit TwistTag.E6.tag F i c'
        rw [block01_uSL]
        exact (hι c').1
      · intro c'
        show ι (block01 (vSL c')) = yUnit TwistTag.E6.tag F i c'
        rw [block01_vSL]
        exact (hι c').2.1
    change (ι.comp block01) (HSL t) = torusElt TwistTag.E6.tag F i t
    rw [hI, simpleRootSL2_HSL]
  · have hI : ι.comp block12 = simpleRootSL2 TwistTag.E6.tag F j := by
      refine eq_simpleRootSL2 j ?_ ?_
      · intro c'
        show ι (block12 (uSL c')) = xUnit TwistTag.E6.tag F j c'
        rw [block12_uSL]
        exact (hι c').2.2.1
      · intro c'
        show ι (block12 (vSL c')) = yUnit TwistTag.E6.tag F j c'
        rw [block12_vSL]
        exact (hι c').2.2.2
    change (ι.comp block12) (HSL u) = torusElt TwistTag.E6.tag F j u
    rw [hI, simpleRootSL2_HSL]

theorem mem_range_rootDiagUnitHom_of_diag_sl3 {i j : Fin TwistTag.E6.tag.rank}
    (ι : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F)
    (hι : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c ∧
      ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c)
    {h : Matrix.SpecialLinearGroup (Fin 3) F}
    (hh : ∀ a a' : Fin 3, a ≠ a' → (h : Matrix (Fin 3) (Fin 3) F) a a' = 0) :
    ι h ∈ (rootDiagUnitHom TwistTag.E6.tag F).range := by
  let a : F := (h : Matrix (Fin 3) (Fin 3) F) 0 0
  let b : F := (h : Matrix (Fin 3) (Fin 3) F) 1 1
  let c : F := (h : Matrix (Fin 3) (Fin 3) F) 2 2
  have hdiag : (h : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![a, b, c] := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [Matrix.diagonal_apply, a, b, c, hh]
  have habc : a * b * c = 1 := by
    have hdet := h.2
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
    simpa [a, b, c] using hdet
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at habc
    exact zero_ne_one habc
  have hb : b ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_mul] at habc
    exact zero_ne_one habc
  have hcEq : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right habc
  let t : Fˣ := Units.mk0 a ha
  let u : Fˣ := Units.mk0 (a * b) (mul_ne_zero ha hb)
  have ht : (t : F) = a := by simp [t]
  have hu : (u : F) = a * b := by simp [u]
  have hdecomp := sl3_diag_eq_block_prod a b c ha hcEq t u ht hu hdiag
  obtain ⟨hA, hB⟩ := sl3_block_torus ι hι t u
  rw [hdecomp, map_mul, hA, hB, torusElt_eq_rootDiagUnit i t, torusElt_eq_rootDiagUnit j u]
  refine ⟨(fun l => t ^ TwistTag.E6.tag.cartan i l) *
      (fun l => u ^ TwistTag.E6.tag.cartan j l), ?_⟩
  rw [map_mul]
  rfl

theorem mem_range_rootDiagUnitHom_of_diag_sl2 {k : Fin TwistTag.E6.tag.rank}
    (ι : Matrix.SpecialLinearGroup (Fin 2) F →* ModGL TwistTag.E6.tag F)
    (hι : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F k c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F k c)
    {h : Matrix.SpecialLinearGroup (Fin 2) F}
    (hh : ∀ a a' : Fin 2, a ≠ a' → (h : Matrix (Fin 2) (Fin 2) F) a a' = 0) :
    ι h ∈ (rootDiagUnitHom TwistTag.E6.tag F).range := by
  have h01 : (h : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := hh 0 1 (by decide)
  have h10 : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hh 1 0 (by decide)
  have h00 : (h : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    have hdet := h.2
    rw [Matrix.det_fin_two, h01, h10, h0] at hdet
    norm_num at hdet
  let t : Fˣ := Units.mk0 ((h : Matrix (Fin 2) (Fin 2) F) 0 0) h00
  have ht : (t : F) = (h : Matrix (Fin 2) (Fin 2) F) 0 0 := by simp [t]
  have h11 : (h : Matrix (Fin 2) (Fin 2) F) 1 1 = ((t⁻¹ : Fˣ) : F) := by
    have hdet := h.2
    rw [Matrix.det_fin_two, h01, h10, mul_zero, sub_zero] at hdet
    rw [Units.val_inv_eq_inv_val, ht]
    exact eq_inv_of_mul_eq_one_right hdet
  have hHSL : h = HSL t := by
    refine SL2_ext ?_ ?_ ?_ ?_
    · rw [coe_HSL]; exact ht.symm
    · rw [coe_HSL, h01]; simp
    · rw [coe_HSL, h10]; simp
    · rw [coe_HSL, h11]
      simp
  have hu : ∀ c : F, ι (uSL c) = xUnit TwistTag.E6.tag F k c := by
    intro c
    rw [← tv_eq_uSL]
    exact (hι c).1
  have hv : ∀ c : F, ι (vSL c) = yUnit TwistTag.E6.tag F k c := by
    intro c
    rw [← tv_eq_vSL]
    exact (hι c).2
  have hI : ι = simpleRootSL2 TwistTag.E6.tag F k :=
    eq_simpleRootSL2 k hu hv
  rw [hHSL, hI, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]
  exact ⟨fun l => t ^ TwistTag.E6.tag.cartan k l, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace
