module

public import CFSG.GH74.Generic.BProg.B2.FixFourS45
public import CFSG.GH74.Generic.BProg.B2.GenLocL5Out
public import CFSG.GH74.Generic.BProg.B2.GenLocDiagU
public import CFSG.GH74.Generic.BProg.B2.GenLocL3NF

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

namespace FixFourS3

variable {F : Type} [Field F]

def diagSet (F : Type) [Field F] : Set (GL (Fin 3) F) :=
  {x | (x : Matrix (Fin 3) (Fin 3) F).IsDiag ∧ x * x = 1 ∧ (x : Matrix (Fin 3) (Fin 3) F).det = 1}

theorem sq_eq_one_iff_pm {a : F} : a * a = 1 ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    have : (a - 1) * (a + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  · rintro (rfl | rfl) <;> ring

theorem diag_entry_sq {x : GL (Fin 3) F} (hd : (x : Matrix (Fin 3) (Fin 3) F).IsDiag) (hx : x * x = 1)
    (i : Fin 3) : (x : Matrix (Fin 3) (Fin 3) F) i i = 1 ∨ (x : Matrix (Fin 3) (Fin 3) F) i i = -1 := by
  have h1 : ((x * x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by rw [hx]; rfl
  rw [Units.val_mul] at h1
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Fintype.sum_eq_single i (fun j hj => by
    rw [hd (Ne.symm hj), zero_mul])] at h2
  simp only [Matrix.one_apply_eq] at h2
  exact sq_eq_one_iff_pm.1 h2

theorem ncard_diagSet_le : (diagSet F).ncard ≤ 4 := by
  let f : GL (Fin 3) F → F × F := fun x => ((x : Matrix (Fin 3) (Fin 3) F) 0 0, (x : Matrix (Fin 3) (Fin 3) F) 1 1)
  have hmaps : ∀ x ∈ diagSet F, f x ∈ (({1, -1} : Set F) ×ˢ ({1, -1} : Set F)) := by
    intro x hx
    obtain ⟨hd, hsq, -⟩ := hx
    exact ⟨diag_entry_sq hd hsq 0, diag_entry_sq hd hsq 1⟩
  have hinj : Set.InjOn f (diagSet F) := by
    intro x hx y hy hxy
    obtain ⟨hdx, hsx, hdetx⟩ := hx
    obtain ⟨hdy, hsy, hdety⟩ := hy
    have h0 : (x : Matrix (Fin 3) (Fin 3) F) 0 0 = (y : Matrix (Fin 3) (Fin 3) F) 0 0 := congrArg Prod.fst hxy
    have h1 : (x : Matrix (Fin 3) (Fin 3) F) 1 1 = (y : Matrix (Fin 3) (Fin 3) F) 1 1 := congrArg Prod.snd hxy
    have hx' := (Matrix.IsDiag.diagonal_diag hdx).symm
    have hy' := (Matrix.IsDiag.diagonal_diag hdy).symm
    rw [hx', Matrix.det_diagonal, Fin.prod_univ_three] at hdetx
    rw [hy', Matrix.det_diagonal, Fin.prod_univ_three] at hdety
    have hdetx' : (x : Matrix (Fin 3) (Fin 3) F) 0 0 * (x : Matrix (Fin 3) (Fin 3) F) 1 1 *
        (x : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := hdetx
    have hdety' : (y : Matrix (Fin 3) (Fin 3) F) 0 0 * (y : Matrix (Fin 3) (Fin 3) F) 1 1 *
        (y : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := hdety
    have hne : (x : Matrix (Fin 3) (Fin 3) F) 0 0 * (x : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 := by
      intro h; rw [h, zero_mul] at hdetx'; exact zero_ne_one hdetx'
    have h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 2 = (y : Matrix (Fin 3) (Fin 3) F) 2 2 := by
      rw [← h0, ← h1] at hdety'
      exact mul_left_cancel₀ hne (hdetx'.trans hdety'.symm)
    apply Units.ext
    rw [hx', hy']
    congr 1
    ext i
    fin_cases i <;> simp [Matrix.diag, h0, h1, h2]
  have hfin : (({1, -1} : Set F) ×ˢ ({1, -1} : Set F)).Finite := (Set.toFinite _).prod (Set.toFinite _)
  calc (diagSet F).ncard ≤ (({1, -1} : Set F) ×ˢ ({1, -1} : Set F)).ncard :=
        Set.ncard_le_ncard_of_injOn f hmaps hinj hfin
    _ = ({1, -1} : Set F).ncard * ({1, -1} : Set F).ncard := Set.ncard_prod
    _ ≤ 2 * 2 := Nat.mul_le_mul ((Set.ncard_insert_le _ _).trans (by simp)) ((Set.ncard_insert_le _ _).trans (by simp))
    _ = 4 := rfl


section Lin

open scoped MatrixGroups

theorem exists_diag_lift_sl3 (hF : ringChar F ≠ 2) [Finite F]
    (D : Subgroup (LinearFlag.projectiveSL 3 F)) (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ (B : GL (Fin 3) F) (σ : ↥D →* SL(3, F)),
      (∀ d, LinearFlag.proj 3 F (σ d) = d) ∧
      ∀ d, ((B⁻¹ * Matrix.SpecialLinearGroup.toGL (σ d) * B : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).IsDiag ∧ σ d * σ d = 1 := by
  have := hD
  obtain ⟨σ, hσπ, hσsq⟩ := GenLocDiag.exists_involutive_section (by decide : Odd 3) D hD
  let ρ : ↥D →* GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL.comp σ
  have hρsq : ∀ d, ρ d * ρ d = 1 := fun d => by
    show Matrix.SpecialLinearGroup.toGL (σ d) * Matrix.SpecialLinearGroup.toGL (σ d) = 1
    rw [← map_mul, hσsq, map_one]
  have hcomm : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := by
    rintro _ ⟨d, rfl⟩ _ ⟨d', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm' d d']
  have hexp : ∀ x ∈ ρ.range, x ^ 2 = 1 := by
    rintro _ ⟨d, rfl⟩
    rw [pow_two]
    exact hρsq d
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime
    ⟨-1, IsPrimitiveRoot.neg_one (ringChar F) hF⟩ ρ.range hcomm hexp
  refine ⟨g⁻¹, σ, hσπ, fun d => ⟨?_, hσsq d⟩⟩
  rw [inv_inv]
  intro i j hij
  exact hg (ρ d) ⟨d, rfl⟩ i j hij

end Lin


section LinMain

def torus1 (δ : Fˣ) : GL (Fin 3) F where
  val := Matrix.diagonal ![(δ : F), 1, 1]
  inv := Matrix.diagonal ![((δ⁻¹ : Fˣ) : F), 1, 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp

theorem det_torus1 (δ : Fˣ) : ((torus1 δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = δ := by
  change (Matrix.diagonal ![(δ : F), 1, 1]).det = δ
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem diag_commute {x y : GL (Fin 3) F} (hx : (x : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hy : (y : Matrix (Fin 3) (Fin 3) F).IsDiag) : x * y = y * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← Matrix.IsDiag.diagonal_diag hx, ← Matrix.IsDiag.diagonal_diag hy,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp [mul_comm]

theorem torus1_isDiag (δ : Fˣ) : ((torus1 δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag :=
  Matrix.isDiag_diagonal _

theorem det_conj_gl (B g : GL (Fin 3) F) :
    ((B⁻¹ * g * B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  have h : ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det * (B : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel]
    simp
  calc _ = (((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det * (B : Matrix (Fin 3) (Fin 3) F).det) *
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det := by ring
    _ = _ := by rw [h, one_mul]

end LinMain


section LinConj

open Matrix.SpecialLinearGroup in
theorem exists_conj_four_projectiveSL3 [Finite F] (hF : ringChar F ≠ 2)
    {D D' : Subgroup (LinearFlag.projectiveSL 3 F)} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hc : Nat.card ↥D = 4) (hD' : CFSG.IsElementaryAbelian 2 ↥D') (hc' : Nat.card ↥D' = 4) :
    ∃ s : SL(3, F), D' = D.map (MulAut.conj (LinearFlag.proj 3 F s)).toMonoidHom := by
  obtain ⟨B, σ, hσπ, hσ⟩ := exists_diag_lift_sl3 hF D hD
  obtain ⟨B', σ', hσ'π, hσ'⟩ := exists_diag_lift_sl3 hF D' hD'
  have hmem : ∀ (B : GL (Fin 3) F) (g : SL(3, F)),
      ((B⁻¹ * toGL g * B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag → g * g = 1 →
      B⁻¹ * toGL g * B ∈ diagSet F := by
    intro B g hdiag hsq
    refine ⟨hdiag, ?_, ?_⟩
    · have h1 : (B⁻¹ * toGL g * B) * (B⁻¹ * toGL g * B) = B⁻¹ * (toGL g * toGL g) * B := by group
      rw [h1, ← map_mul, hsq, map_one]
      group
    · rw [det_conj_gl]
      exact g.2
  have hinj' : Function.Injective (fun d' : ↥D' => B'⁻¹ * toGL (σ' d') * B') := by
    intro a b hab
    have h1 : toGL (σ' a) = toGL (σ' b) := by
      have := hab
      simp only [mul_left_inj, mul_right_inj] at this
      exact this
    have h2 : σ' a = σ' b := toGL_injective h1
    have h3 := congrArg (LinearFlag.proj 3 F) h2
    rw [hσ'π a, hσ'π b] at h3
    exact Subtype.ext h3
  have hsub : Set.range (fun d' : ↥D' => B'⁻¹ * toGL (σ' d') * B') ⊆ diagSet F := by
    rintro _ ⟨d', rfl⟩
    exact hmem B' (σ' d') (hσ' d').1 (hσ' d').2
  have hT : (Set.range (fun d' : ↥D' => B'⁻¹ * toGL (σ' d') * B')).ncard = 4 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj', Set.ncard_univ, hc']
  have hrange : Set.range (fun d' : ↥D' => B'⁻¹ * toGL (σ' d') * B') = diagSet F :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hT]; exact ncard_diagSet_le) (Set.toFinite _)
  let δ : Fˣ := Matrix.GeneralLinearGroup.det B * (Matrix.GeneralLinearGroup.det B')⁻¹
  let t : GL (Fin 3) F := torus1 δ
  let M : GL (Fin 3) F := B' * t * B⁻¹
  have hdetM : (M : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det t = δ := Units.ext (det_torus1 δ)
    have h2 : Matrix.GeneralLinearGroup.det M = 1 := by
      simp only [M, map_mul, map_inv, h1, δ]
      rw [mul_comm (Matrix.GeneralLinearGroup.det B') (Matrix.GeneralLinearGroup.det B *
        (Matrix.GeneralLinearGroup.det B')⁻¹)]
      group
    have := congrArg Units.val h2
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  let s : SL(3, F) := ⟨(M : Matrix (Fin 3) (Fin 3) F), hdetM⟩
  have hs : toGL s = M := Units.ext rfl
  have hfix : ∀ d : ↥D, ∃ d' : ↥D', σ' d' = s * σ d * s⁻¹ := by
    intro d
    have hx : B⁻¹ * toGL (σ d) * B ∈ diagSet F := hmem B (σ d) (hσ d).1 (hσ d).2
    rw [← hrange] at hx
    obtain ⟨d', hd'⟩ := hx
    refine ⟨d', toGL_injective ?_⟩
    have hdiag : ((B⁻¹ * toGL (σ d) * B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag :=
      (hσ d).1
    have hcomm : t * (B⁻¹ * toGL (σ d) * B) = (B⁻¹ * toGL (σ d) * B) * t :=
      diag_commute (torus1_isDiag δ) hdiag
    rw [map_mul, map_mul, map_inv, hs]
    simp only at hd'
    calc toGL (σ' d') = B' * (B'⁻¹ * toGL (σ' d') * B') * B'⁻¹ := by group
      _ = B' * (B⁻¹ * toGL (σ d) * B) * B'⁻¹ := by rw [hd']
      _ = B' * (t * (B⁻¹ * toGL (σ d) * B) * t⁻¹) * B'⁻¹ := by
          rw [hcomm, mul_inv_cancel_right]
      _ = M * toGL (σ d) * M⁻¹ := by simp only [M]; group
  refine ⟨s, ?_⟩
  have hle : D.map (MulAut.conj (LinearFlag.proj 3 F s)).toMonoidHom ≤ D' := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨d', hd'⟩ := hfix ⟨d, hd⟩
    have h1 : (MulAut.conj (LinearFlag.proj 3 F s)).toMonoidHom d = (d' : LinearFlag.projectiveSL 3 F) := by
      have e1 : d = LinearFlag.proj 3 F (σ ⟨d, hd⟩) := (hσπ ⟨d, hd⟩).symm
      show (MulAut.conj (LinearFlag.proj 3 F s)) d = _
      rw [e1, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← hd', hσ'π d']
    rw [h1]
    exact d'.2
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (MulAut.conj (LinearFlag.proj 3 F s)).injective, hc, hc']

end LinConj


section UniConj

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

omit [Finite K] in
theorem bar_det_mul_det {h : UnitaryFieldData p f K} {B : GL (Fin 3) K}
    (hB : B ∈ primeFormUnitary h (idGram K 3)) :
    h.bar ((B : Matrix (Fin 3) (Fin 3) K).det) * (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h1 := (mem_primeFormUnitary (h := h)).1 hB
  simp only [idGram, Units.val_one, Matrix.mul_one] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  have h3 : ((B : Matrix (Fin 3) (Fin 3) K).map h.bar).det = h.bar ((B : Matrix (Fin 3) (Fin 3) K).det) := by
    rw [RingHom.map_det]
    rfl
  rwa [h3] at h2

omit [Finite K] in
theorem torus1_mem_primeFormUnitary {h : UnitaryFieldData p f K} (δ : Kˣ)
    (hδ : h.bar (δ : K) * δ = 1) : torus1 δ ∈ primeFormUnitary h (idGram K 3) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  change ((Matrix.diagonal ![(δ : K), 1, 1]).map h.bar)ᵀ * Matrix.diagonal ![(δ : K), 1, 1] = 1
  rw [Matrix.diagonal_map (by simp), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [hδ]

open CFSG.LieType.Universal.Unitary in
theorem exists_conj_four_statedSU3 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    {D D' : Subgroup (StatedProj (StatedSU 3 (p ^ f) K))} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hc : Nat.card ↥D = 4) (hD' : CFSG.IsElementaryAbelian 2 ↥D') (hc' : Nat.card ↥D' = 4) :
    ∃ s : ↥(StatedSU 3 (p ^ f) K),
      D' = D.map (MulAut.conj (QuotientGroup.mk s : StatedProj (StatedSU 3 (p ^ f) K))).toMonoidHom := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  obtain ⟨B, ρ, hB, hρ, hmk⟩ := exists_diag_lift_of_odd_unitary hp hp2 hK (by decide) D hD
  obtain ⟨B', ρ', hB', hρ', hmk'⟩ :=
    exists_diag_lift_of_odd_unitary hp hp2 hK (by decide) D' hD'
  have hBu : B ∈ primeFormUnitary h (idGram K 3) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    convert hB using 3
    ext i j
    simp [UnitaryFieldData.bar_apply]
  have hBu' : B' ∈ primeFormUnitary h (idGram K 3) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    convert hB' using 3
    ext i j
    simp [UnitaryFieldData.bar_apply]
  have hmem : ∀ (B : GL (Fin 3) K) (g : GL (Fin 3) K), g ∈ StatedSU 3 (p ^ f) K →
      ((B⁻¹ * g * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag → g * g = 1 →
      B⁻¹ * g * B ∈ diagSet K := by
    intro B g hg hdiag hsq
    refine ⟨hdiag, ?_, ?_⟩
    · have h1 : (B⁻¹ * g * B) * (B⁻¹ * g * B) = B⁻¹ * (g * g) * B := by group
      rw [h1, hsq]
      group
    · rw [det_conj_gl]
      exact det_eq_one_of_mem_statedSU hg
  have hinj' : Function.Injective (fun d' : ↥D' => B'⁻¹ * ρ' d' * B') := by
    intro a b hab
    have h1 : ρ' a = ρ' b := by
      have := hab
      simp only [mul_left_inj, mul_right_inj] at this
      exact this
    obtain ⟨ha, hma⟩ := hmk' a
    obtain ⟨hb, hmb⟩ := hmk' b
    apply Subtype.ext
    rw [← hma, ← hmb]
    congr 1
    exact Subtype.ext h1
  have hsub : Set.range (fun d' : ↥D' => B'⁻¹ * ρ' d' * B') ⊆ diagSet K := by
    rintro _ ⟨d', rfl⟩
    exact hmem B' (ρ' d') (hmk' d').1 (hρ' d').1 (hρ' d').2
  have hT : (Set.range (fun d' : ↥D' => B'⁻¹ * ρ' d' * B')).ncard = 4 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj', Set.ncard_univ, hc']
  have hrange : Set.range (fun d' : ↥D' => B'⁻¹ * ρ' d' * B') = diagSet K :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hT]; exact ncard_diagSet_le) (Set.toFinite _)
  let δ : Kˣ := Matrix.GeneralLinearGroup.det B * (Matrix.GeneralLinearGroup.det B')⁻¹
  let t : GL (Fin 3) K := torus1 δ
  let M : GL (Fin 3) K := B' * t * B⁻¹
  have hδ : h.bar (δ : K) * δ = 1 := by
    have e1 := bar_det_mul_det hBu
    have e2 := bar_det_mul_det hBu'
    have hB0 : (B : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at e1; exact zero_ne_one e1
    have hB0' : (B' : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at e2; exact zero_ne_one e2
    have hδv : (δ : K) = (B : Matrix (Fin 3) (Fin 3) K).det / (B' : Matrix (Fin 3) (Fin 3) K).det := by
      simp [δ, div_eq_mul_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [hδv, map_div₀, div_mul_div_comm, e1, e2, div_one]
  have hdetM : (M : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det t = δ := Units.ext (det_torus1 δ)
    have h2 : Matrix.GeneralLinearGroup.det M = 1 := by
      simp only [M, map_mul, map_inv, h1, δ]
      rw [mul_comm (Matrix.GeneralLinearGroup.det B') (Matrix.GeneralLinearGroup.det B *
        (Matrix.GeneralLinearGroup.det B')⁻¹)]
      group
    have := congrArg Units.val h2
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hMu : M ∈ primeFormUnitary h (idGram K 3) :=
    (primeFormUnitary h (idGram K 3)).mul_mem
      ((primeFormUnitary h (idGram K 3)).mul_mem hBu' (torus1_mem_primeFormUnitary δ hδ))
      ((primeFormUnitary h (idGram K 3)).inv_mem hBu)
  have hMS : M ∈ StatedSU 3 (p ^ f) K := by
    have h1 := (mem_primeFormUnitary (h := h)).1 hMu
    simp only [idGram, Units.val_one, Matrix.mul_one] at h1
    exact (mem_unitarySU_iff h).2 ⟨hdetM, h1⟩
  let s : ↥(StatedSU 3 (p ^ f) K) := ⟨M, hMS⟩
  have hfix : ∀ d : ↥D, ∃ d' : ↥D', ρ' d' = M * ρ d * M⁻¹ := by
    intro d
    have hx : B⁻¹ * ρ d * B ∈ diagSet K := hmem B (ρ d) (hmk d).1 (hρ d).1 (hρ d).2
    rw [← hrange] at hx
    obtain ⟨d', hd'⟩ := hx
    refine ⟨d', ?_⟩
    have hdiag : ((B⁻¹ * ρ d * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := (hρ d).1
    have hcomm : t * (B⁻¹ * ρ d * B) = (B⁻¹ * ρ d * B) * t :=
      diag_commute (torus1_isDiag δ) hdiag
    simp only at hd'
    calc ρ' d' = B' * (B'⁻¹ * ρ' d' * B') * B'⁻¹ := by group
      _ = B' * (B⁻¹ * ρ d * B) * B'⁻¹ := by rw [hd']
      _ = B' * (t * (B⁻¹ * ρ d * B) * t⁻¹) * B'⁻¹ := by
          rw [hcomm, mul_inv_cancel_right]
      _ = M * ρ d * M⁻¹ := by simp only [M]; group
  refine ⟨s, ?_⟩
  have hle : D.map (MulAut.conj (QuotientGroup.mk s : StatedProj (StatedSU 3 (p ^ f) K))).toMonoidHom ≤ D' := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨d', hd'⟩ := hfix ⟨d, hd⟩
    obtain ⟨hdS, hmd⟩ := hmk ⟨d, hd⟩
    obtain ⟨hd'S, hmd'⟩ := hmk' d'
    have hsub : s * ⟨ρ ⟨d, hd⟩, hdS⟩ * s⁻¹ = ⟨ρ' d', hd'S⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hd']
      rfl
    have h1 : (MulAut.conj (QuotientGroup.mk s : StatedProj (StatedSU 3 (p ^ f) K))).toMonoidHom d =
        (d' : StatedProj (StatedSU 3 (p ^ f) K)) := by
      have hmd'' : (QuotientGroup.mk ⟨ρ ⟨d, hd⟩, hdS⟩ : StatedProj (StatedSU 3 (p ^ f) K)) = d := hmd
      show (MulAut.conj (QuotientGroup.mk s : StatedProj (StatedSU 3 (p ^ f) K))) d = _
      rw [← hmd'', MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, hsub]
      exact hmd'.symm ▸ rfl
    rw [h1]
    exact d'.2
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hc, hc']

end UniConj


section Shape3

theorem map_conj_transport {Kt Y : Type} [Group Kt] [Group Y] (ψ : Kt ≃* Y) {E E' : Subgroup Kt}
    {y : Y} (h : E'.map ψ.toMonoidHom = (E.map ψ.toMonoidHom).map (MulAut.conj y).toMonoidHom) :
    E' = E.map (MulAut.conj (ψ.symm y)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    have h1 : ψ x ∈ E'.map ψ.toMonoidHom := ⟨x, hx, rfl⟩
    rw [h] at h1
    obtain ⟨_, ⟨a, ha, rfl⟩, hy⟩ := h1
    refine ⟨a, ha, ψ.injective ?_⟩
    change ψ ((MulAut.conj (ψ.symm y)) a) = ψ x
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨a, ha, rfl⟩
    have h1 : (MulAut.conj y) (ψ a) ∈ E'.map ψ.toMonoidHom := by
      rw [h]
      exact ⟨ψ a, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨b, hb, hb2⟩ := h1
    have : b = (MulAut.conj (ψ.symm y)) a := by
      apply ψ.injective
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hb2
    show (MulAut.conj (ψ.symm y)) a ∈ E'
    rw [← this]
    exact hb

theorem isElementaryAbelian_map_equiv {Kt Y : Type} [Group Kt] [Group Y] (ψ : Kt ≃* Y)
    {E : Subgroup Kt} (hE : CFSG.IsElementaryAbelian 2 ↥E) :
    CFSG.IsElementaryAbelian 2 ↥(E.map ψ.toMonoidHom) := by
  have hEc := hE.1
  refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have := (WeakSigGen.forall_of_isElementaryAbelian hE).1 a ha b hb
    change ψ a * ψ b = ψ b * ψ a
    rw [← map_mul, ← map_mul, this]
  · obtain ⟨a, ha, rfl⟩ := hu
    have := (WeakSigGen.forall_of_isElementaryAbelian hE).2 a ha
    change ψ a * ψ a = 1
    rw [← map_mul, this, map_one]

theorem fourConj_shape3 : FourConj QShape3 := by
  intro Kt _ _ hKt E E' hE hcE hE' hcE'
  obtain ⟨p, f, hp, hp2, -, hm | hm⟩ := hKt
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hm
    let ψ : Kt ≃* LinearFlag.projectiveSL 3 F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
    have hF2 : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
    obtain ⟨s, hs⟩ := exists_conj_four_projectiveSL3 hF2 (isElementaryAbelian_map_equiv ψ hE)
      (by rw [Subgroup.card_map_of_injective ψ.injective, hcE])
      (isElementaryAbelian_map_equiv ψ hE')
      (by rw [Subgroup.card_map_of_injective ψ.injective, hcE'])
    exact ⟨ψ.symm (LinearFlag.proj 3 F s), map_conj_transport ψ hs⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GenLocL5Out.stated_PSU hm
    obtain ⟨s, hs⟩ := exists_conj_four_statedSU3 hp hp2 hK (isElementaryAbelian_map_equiv e hE)
      (by rw [Subgroup.card_map_of_injective e.injective, hcE])
      (isElementaryAbelian_map_equiv e hE')
      (by rw [Subgroup.card_map_of_injective e.injective, hcE'])
    exact ⟨e.symm (QuotientGroup.mk s), map_conj_transport e hs⟩

end Shape3


section Vhat

variable (F : Type) [Field F]

theorem sl_diag_commute {s t : SL(3, F)} (hs : (s : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (ht : (t : Matrix (Fin 3) (Fin 3) F).IsDiag) : s * t = t * s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.IsDiag.diagonal_diag hs, ← Matrix.IsDiag.diagonal_diag ht,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp [mul_comm]

@[expose] def Vhat : Subgroup SL(3, F) where
  carrier := {s | (s : Matrix (Fin 3) (Fin 3) F).IsDiag ∧ s * s = 1}
  one_mem' := ⟨by simp, one_mul 1⟩
  mul_mem' := by
    rintro s t ⟨hs, hs2⟩ ⟨ht, ht2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.IsDiag.diagonal_diag hs,
        ← Matrix.IsDiag.diagonal_diag ht, Matrix.diagonal_mul_diagonal]
      exact Matrix.isDiag_diagonal _
    · have hc := sl_diag_commute F hs ht
      calc s * t * (s * t) = s * (t * s) * t := by group
        _ = s * (s * t) * t := by rw [← hc]
        _ = (s * s) * (t * t) := by group
        _ = 1 := by rw [hs2, ht2, one_mul]
  inv_mem' := by
    rintro s ⟨hs, hs2⟩
    have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    rw [hinv]
    exact ⟨hs, hs2⟩

end Vhat


section VhatCard

variable {F : Type} [Field F]

def dsl (a b c : F) (h : a * b * c = 1) : SL(3, F) :=
  ⟨Matrix.diagonal ![a, b, c], by rw [Matrix.det_diagonal, Fin.prod_univ_three]; simpa using h⟩

theorem dsl_isDiag (a b c : F) (h : a * b * c = 1) :
    ((dsl a b c h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).IsDiag :=
  Matrix.isDiag_diagonal _

theorem dsl_mul_self (a b c : F) (h : a * b * c = 1) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    dsl a b c h * dsl a b c h = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change Matrix.diagonal ![a, b, c] * Matrix.diagonal ![a, b, c] = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [ha, hb, hc]

theorem card_Vhat (h2 : (2 : F) ≠ 0) [Finite F] : Nat.card ↥(Vhat F) = 4 := by
  have hm1 : (-1 : F) * -1 = 1 := by ring
  have h1 : (1 : F) * 1 = 1 := by ring
  have hne : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  let e0 : ↥(Vhat F) := ⟨dsl 1 1 1 (by ring), dsl_isDiag _ _ _ _, dsl_mul_self _ _ _ _ h1 h1 h1⟩
  let e1 : ↥(Vhat F) := ⟨dsl (-1) (-1) 1 (by ring), dsl_isDiag _ _ _ _, dsl_mul_self _ _ _ _ hm1 hm1 h1⟩
  let e2 : ↥(Vhat F) := ⟨dsl (-1) 1 (-1) (by ring), dsl_isDiag _ _ _ _, dsl_mul_self _ _ _ _ hm1 h1 hm1⟩
  let e3 : ↥(Vhat F) := ⟨dsl 1 (-1) (-1) (by ring), dsl_isDiag _ _ _ _, dsl_mul_self _ _ _ _ h1 hm1 hm1⟩
  refine le_antisymm ?_ ?_
  ·
    let f : ↥(Vhat F) → ↥(diagSet F) := fun s => ⟨Matrix.SpecialLinearGroup.toGL s.1, s.2.1, by
        rw [← map_mul, s.2.2, map_one], s.1.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective this)
    calc Nat.card ↥(Vhat F) ≤ Nat.card ↥(diagSet F) := Nat.card_le_card_of_injective f hf
      _ = (diagSet F).ncard := (Nat.card_coe_set_eq _)
      _ ≤ 4 := ncard_diagSet_le
  · let ent : ↥(Vhat F) → F × F := fun x =>
      (((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0, ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 1 1)
    let g : Fin 4 → ↥(Vhat F) := ![e0, e1, e2, e3]
    have hent : Function.Injective (ent ∘ g) := by
      intro i j hij
      have hne' : (1 : F) ≠ -1 := hne.symm
      fin_cases i <;> fin_cases j <;>
        simp [ent, g, e0, e1, e2, e3, dsl, Prod.ext_iff, hne, hne'] at hij ⊢
    have := Nat.card_le_card_of_injective g (Function.Injective.of_comp hent)
    simpa using this

end VhatCard


section VProj

variable {F : Type} [Field F]

theorem proj_injective_Vhat [Finite F] :
    Function.Injective ((LinearFlag.proj 3 F).comp (Vhat F).subtype) := by
  intro a b hab
  have h1 : LinearFlag.proj 3 F (b.1⁻¹ * a.1) = 1 := by
    rw [map_mul, map_inv]
    have : LinearFlag.proj 3 F a.1 = LinearFlag.proj 3 F b.1 := hab
    rw [this, inv_mul_cancel]
  rw [LinearFlag.proj_eq_one_iff] at h1
  obtain ⟨c, hc3, hc⟩ := h1
  have hmem : b.1⁻¹ * a.1 ∈ Vhat F := (Vhat F).mul_mem ((Vhat F).inv_mem b.2) a.2
  have hsq : (b.1⁻¹ * a.1) * (b.1⁻¹ * a.1) = 1 := hmem.2
  have hsq' := congrArg (fun m : SL(3, F) => (m : Matrix (Fin 3) (Fin 3) F)) hsq
  simp only [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.SpecialLinearGroup.coe_one] at hsq'
  have hcc : (c : F) * c = 1 := by
    rw [← map_mul] at hsq'
    have := congrFun (congrFun hsq' 0) 0
    simpa [Matrix.scalar_apply] using this
  have hc1 : c = 1 := by
    have h3 : c * c = 1 := Units.ext hcc
    calc c = c * (c * c) := by rw [h3, mul_one]
      _ = c ^ 3 := by rw [pow_succ, pow_two, mul_assoc]
      _ = 1 := hc3
  have hone : b.1⁻¹ * a.1 = 1 := by
    apply Subtype.ext
    rw [hc, hc1]
    simp
  exact Subtype.ext (by simpa using (inv_mul_eq_one.1 hone).symm)

end VProj


section VFix

variable {F : Type} [Field F]

@[expose] def Vproj (F : Type) [Field F] : Subgroup (LinearFlag.projectiveSL 3 F) :=
  ((LinearFlag.proj 3 F).comp (Vhat F).subtype).range

theorem card_Vproj [Finite F] (h2 : (2 : F) ≠ 0) : Nat.card ↥(Vproj F) = 4 := by
  rw [Vproj, ← card_Vhat h2]
  exact (Nat.card_congr (MonoidHom.ofInjective proj_injective_Vhat).toEquiv).symm

theorem isElementaryAbelian_Vproj : CFSG.IsElementaryAbelian 2 ↥(Vproj F) := by
  refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · obtain ⟨⟨s, hs⟩, rfl⟩ := hu
    obtain ⟨⟨t, ht⟩, rfl⟩ := hv
    show (LinearFlag.proj 3 F s) * (LinearFlag.proj 3 F t) = (LinearFlag.proj 3 F t) * (LinearFlag.proj 3 F s)
    rw [← map_mul, ← map_mul, sl_diag_commute F hs.1 ht.1]
  · obtain ⟨⟨s, hs⟩, rfl⟩ := hu
    show (LinearFlag.proj 3 F s) * (LinearFlag.proj 3 F s) = 1
    rw [← map_mul, hs.2, map_one]

theorem matrix_diag_comm {a b : Matrix (Fin 3) (Fin 3) F} (ha : a.IsDiag) (hb : b.IsDiag) :
    a * b = b * a := by
  rw [← Matrix.IsDiag.diagonal_diag ha, ← Matrix.IsDiag.diagonal_diag hb,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp [mul_comm]

def stabV (F : Type) [Field F] : Subgroup (MulAut (LinearFlag.projectiveSL 3 F)) where
  carrier := {g | ∀ v ∈ Vproj F, g v = v}
  one_mem' := fun v _ => rfl
  mul_mem' := fun {a b} ha hb v hv => by
    rw [MulAut.mul_apply, hb v hv, ha v hv]
  inv_mem' := fun {a} ha v hv => by
    have h := ha v hv
    calc a⁻¹ v = a⁻¹ (a v) := by rw [h]
      _ = v := by simp

theorem Vhat_entry {s : SL(3, F)} (hs : s ∈ Vhat F) (i : Fin 3) :
    (s : Matrix (Fin 3) (Fin 3) F) i i = 1 ∨ (s : Matrix (Fin 3) (Fin 3) F) i i = -1 := by
  have h2 : Matrix.SpecialLinearGroup.toGL s * Matrix.SpecialLinearGroup.toGL s = 1 := by
    rw [← map_mul, hs.2, map_one]
  exact diag_entry_sq (x := Matrix.SpecialLinearGroup.toGL s) hs.1 h2 i

theorem frameStab_le_stabV [Finite F] : frameStab 3 F ≤ stabV F := by
  rw [frameStab, Subgroup.closure_le]
  rintro _ ((⟨⟨x, hx⟩, rfl⟩ | ⟨σ, rfl⟩) | rfl)
  · rintro _ ⟨⟨s, hs⟩, rfl⟩
    show LinearFlag.conjAut 3 F x (LinearFlag.proj 3 F s) = LinearFlag.proj 3 F s
    rw [LinearFlag.conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [LinearFlag.coe_slConjugation, matrix_diag_comm hx hs.1, Matrix.mul_assoc]
    have h1 : (x : Matrix (Fin 3) (Fin 3) F) * ((x⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
      Units.mul_inv x
    rw [h1, Matrix.mul_one]
  · rintro _ ⟨⟨s, hs⟩, rfl⟩
    show LinearFlag.fieldAut 3 F σ (LinearFlag.proj 3 F s) = LinearFlag.proj 3 F s
    rw [LinearFlag.fieldAut_proj]
    congr 1
    apply Subtype.ext
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    by_cases hij : i = j
    · subst hij
      rcases Vhat_entry hs i with h | h <;> rw [h] <;> simp
    · rw [hs.1 hij, map_zero]
  · rintro _ ⟨⟨s, hs⟩, rfl⟩
    show LinearFlag.dualAut 3 F (LinearFlag.proj 3 F s) = LinearFlag.proj 3 F s
    rw [LinearFlag.dualAut_proj]
    congr 1
    have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs.2
    rw [hinv]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_transpose]
    exact Matrix.IsDiag.isSymm hs.1

end VFix


section InvolLin

variable {F : Type} [Field F] [Finite F]

theorem involFixFour_linear {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (ψ : ↥L ≃* LinearFlag.projectiveSL 3 F) {y : X} (hy : orderOf y = 2) :
    ∃ E : Subgroup X, E ≤ L ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 ∧
      ∀ e ∈ E, y * e = e * y := by
  have hF2 : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  let α : MulAut (LinearFlag.projectiveSL 3 F) := MulAut.congr ψ (MulAut.conjNormal y)
  have hα2 : α * α = 1 := by
    have h1 : (MulAut.conjNormal y : MulAut ↥L) * MulAut.conjNormal y = 1 := by
      rw [← map_mul, hy2, map_one]
    show MulAut.congr ψ (MulAut.conjNormal y) * MulAut.congr ψ (MulAut.conjNormal y) = 1
    rw [← map_mul, h1, map_one]
  let D : Subgroup (MulAut (LinearFlag.projectiveSL 3 F)) := Subgroup.zpowers α
  have hD : CFSG.IsElementaryAbelian 2 ↥D := by
    refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      exact (Commute.zpow_zpow_self α m n).eq
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      have hα2' : α ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hα2
      rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul, hα2', _root_.one_zpow]
  obtain ⟨β, hβ⟩ := exists_conj_le_frameStab hp hp2 hF D hD
  have hα' : β * α * β⁻¹ ∈ frameStab 3 F := hβ ⟨α, Subgroup.mem_zpowers α, rfl⟩
  have hfix : ∀ v ∈ Vproj F, α (β.symm v) = β.symm v := by
    intro v hv
    have h1 : (β * α * β⁻¹) v = v := frameStab_le_stabV hα' v hv
    have h2 : β (α (β⁻¹ v)) = v := h1
    have h3 := congrArg β.symm h2
    simpa using h3
  let Θ : LinearFlag.projectiveSL 3 F →* X :=
    L.subtype.comp (ψ.symm.toMonoidHom.comp β.symm.toMonoidHom)
  have hΘ : Function.Injective Θ := fun a b hab =>
    β.symm.injective (ψ.symm.injective (Subtype.ext hab))
  have hΘL : ∀ v, Θ v ∈ L := fun v => (ψ.symm (β.symm v)).2
  refine ⟨(Vproj F).map Θ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, _, rfl⟩
    exact hΘL v
  · obtain ⟨hcomm, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian (isElementaryAbelian_Vproj (F := F))
    refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu w hw => ?_) (fun u hu => ?_)
    · obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hw
      rw [← map_mul, ← map_mul, hcomm a ha b hb]
    · obtain ⟨a, ha, rfl⟩ := hu
      rw [← map_mul, hsq a ha, map_one]
  · rw [Subgroup.card_map_of_injective hΘ, card_Vproj h2]
  · rintro _ ⟨v, hv, rfl⟩
    have hl := hfix v hv
    let l : ↥L := ψ.symm (β.symm v)
    have h1 : MulAut.conjNormal y l = l := by
      apply ψ.injective
      have h2 : α (ψ l) = ψ (MulAut.conjNormal y l) := by
        show ψ ((MulAut.conjNormal y) (ψ.symm (ψ l))) = ψ ((MulAut.conjNormal y) l)
        rw [MulEquiv.symm_apply_apply]
      rw [← h2]
      have h3 : ψ l = β.symm v := by simp [l]
      rw [h3]
      exact hl
    have h4 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h4
    show y * (l : X) = (l : X) * y
    calc y * (l : X) = y * (l : X) * y⁻¹ * y := by group
      _ = (l : X) * y := by rw [h4]

end InvolLin

section Assembly

@[expose] def InvolFixFourSU3 : Prop :=
  ∀ {K : Type} [Field K] [Finite K] {p f : ℕ}, p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 →
    ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal]
      (_ : ↥L ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K))
      (y : X), orderOf y = 2 →
      ∃ E : Subgroup X, E ≤ L ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 ∧
        ∀ e ∈ E, y * e = e * y

theorem involFixFour_shape3 (hU : InvolFixFourSU3) : InvolFixFour QShape3 := by
  intro X _ _ L hL hKt y hy
  obtain ⟨p, f, hp, hp2, -, hm | hm⟩ := hKt
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hm
    let ψ : ↥L ≃* LinearFlag.projectiveSL 3 F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
    exact involFixFour_linear hp hp2 hF L ψ hy
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GenLocL5Out.stated_PSU hm
    exact hU hp hp2 hK X L e y hy

end Assembly

end FixFourS3

end CFSG.GH74.Generic.BProg.B2
