module

public import CFSG.LieType.Steinberg.Classical.Symplectic.Basic
public import CFSG.LieType.Steinberg.PartB
public import CFSG.LieType.Universal.SymplecticExtras.RankOne
import all CFSG.LieType.Universal.SymplecticExtras.RankOne

public noncomputable section

namespace CFSG.LieType.Steinberg.Sp

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank

variable {n : ℕ} {F : Type} [Field F]

section Block

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ}

@[expose] def blockMat (p q : κ) (A : Matrix (Fin 2) (Fin 2) F) : Matrix κ κ F :=
  Matrix.of fun a b =>
    if a = p then (if b = p then A 0 0 else if b = q then A 0 1 else 0)
    else if a = q then (if b = p then A 1 0 else if b = q then A 1 1 else 0)
    else (1 : Matrix κ κ F) a b

omit [Fintype κ] in
theorem isBlk_blockMat (A : Matrix (Fin 2) (Fin 2) F) : IsBlk p q (blockMat p q A) := by
  intro a b hab
  simp only [blockMat, of_apply]
  rcases hab with ⟨ha, hb⟩ | ⟨hbp, hbq⟩
  · simp [ha, hb]
  · simp only [hbp, hbq, ite_false]
    split_ifs with h1 h2
    · subst h1
      exact (Matrix.one_apply_ne (Ne.symm hbp)).symm
    · subst h2
      exact (Matrix.one_apply_ne (Ne.symm hbq)).symm
    · rfl

omit [Fintype κ] in
theorem toBlock_blockMat (hpq : p ≠ q) (A : Matrix (Fin 2) (Fin 2) F) :
    SpExtras.toBlock p q (blockMat p q A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpExtras.toBlock, blockMat, Ne.symm hpq]

theorem blockMat_mul (hpq : p ≠ q) (A B : Matrix (Fin 2) (Fin 2) F) :
    blockMat p q (A * B) = blockMat p q A * blockMat p q B :=
  eq_of_toBlock_eq (isBlk_blockMat _) (isBlk_mul (isBlk_blockMat _) (isBlk_blockMat _)) (by
    rw [SpExtras.toBlock_mul hpq (isBlk_blockMat _), toBlock_blockMat hpq, toBlock_blockMat hpq,
      toBlock_blockMat hpq])

omit [Fintype κ] in
theorem blockMat_one (hpq : p ≠ q) : blockMat p q (1 : Matrix (Fin 2) (Fin 2) F) = 1 :=
  eq_of_toBlock_eq (isBlk_blockMat _) isBlk_one
    (by rw [toBlock_blockMat hpq, SpExtras.toBlock_one hpq])

omit [Fintype κ] in
theorem blockMat_injective (hpq : p ≠ q) : Function.Injective (blockMat (F := F) p q) :=
  fun A B h => by rw [← toBlock_blockMat hpq A, ← toBlock_blockMat hpq B, h]

omit [Fintype κ] in
theorem blockMat_upper (hpq : p ≠ q) (c : F) :
    blockMat p q !![1, c; 0, 1] = transvection p q c :=
  eq_of_toBlock_eq (isBlk_blockMat _) (isBlk_transvection (Or.inl ⟨rfl, rfl⟩) c)
    (by rw [toBlock_blockMat hpq, SpExtras.toBlock_transvection_pq hpq])

omit [Fintype κ] in
theorem blockMat_lower (hpq : p ≠ q) (c : F) :
    blockMat p q !![1, 0; c, 1] = transvection q p c :=
  eq_of_toBlock_eq (isBlk_blockMat _) (isBlk_transvection (Or.inr ⟨rfl, rfl⟩) c)
    (by rw [toBlock_blockMat hpq, SpExtras.toBlock_transvection_qp hpq])

variable (F) in
@[expose] def blockMatHom (hpq : p ≠ q) : Matrix (Fin 2) (Fin 2) F →* Matrix κ κ F where
  toFun := blockMat p q
  map_one' := blockMat_one hpq
  map_mul' := blockMat_mul hpq

variable (F) in
@[expose] def blockHom (hpq : p ≠ q) : Matrix.SpecialLinearGroup (Fin 2) F →* GL κ F :=
  (Units.map (blockMatHom F hpq)).comp Matrix.SpecialLinearGroup.toGL

theorem coe_blockHom (hpq : p ≠ q) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((blockHom F hpq A : GL κ F) : Matrix κ κ F) = blockMat p q (A : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem blockHom_injective (hpq : p ≠ q) : Function.Injective (blockHom F hpq) :=
  fun _ _ h => Subtype.ext (blockMat_injective hpq (congrArg Units.val h))

theorem blockHom_upper (hpq : p ≠ q) (c : F) :
    blockHom F hpq (sl2Upper c) = TauCeti.transvectionUnit hpq c :=
  Units.ext (by rw [coe_blockHom, TauCeti.coe_transvectionUnit]; exact blockMat_upper hpq c)

theorem blockHom_lower (hpq : p ≠ q) (c : F) :
    blockHom F hpq (sl2Lower c) = TauCeti.transvectionUnit hpq.symm c :=
  Units.ext (by rw [coe_blockHom, TauCeti.coe_transvectionUnit]; exact blockMat_lower hpq c)

end Block

theorem coe_sl2Upper (c : F) :
    ((sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, c; 0, 1] := rfl

theorem coe_sl2Lower (c : F) :
    ((sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; c, 1] := rfl

theorem mem_closure_sl2 (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    A ∈ Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) := by
  set S := Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower)
  have hU : ∀ c, sl2Upper c ∈ S := fun c => Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  have hL : ∀ c, sl2Lower c ∈ S := fun c => Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  have hdet : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      (B : Matrix (Fin 2) (Fin 2) F) 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := fun B => by
    have := B.2
    rwa [Matrix.det_fin_two] at this
  have key : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F, (B : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 →
      B ∈ S := by
    intro B hc
    have hB : B = sl2Upper ((B 0 0 - 1) / B 1 0) * sl2Lower (B 1 0) *
        sl2Upper ((B 1 1 - 1) / B 1 0) := by
      ext i j
      have h := hdet B
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper,
        coe_sl2Lower, coe_sl2Upper]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
        first | ring1 | linear_combination h | linear_combination -h
    rw [hB]
    exact mul_mem (mul_mem (hU _) (hL _)) (hU _)
  by_cases hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h
      have := hdet A
      rw [h, hc] at this
      simp at this
    have hLA : ((sl2Lower 1 * A : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, h00]
    have e : A = (sl2Lower 1)⁻¹ * (sl2Lower 1 * A) := by group
    rw [e]
    exact mul_mem (inv_mem (hL 1)) (key _ hLA)
  · exact key A hc

theorem rankOne_short {i : Fin n} (hk : i.val + 1 < n) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp n F, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = x n F (Pi.single i 1) c) ∧
        ∀ c, φ (sl2Lower c) = x n F (-Pi.single i 1) c := by
  have hk' := ne_succ' hk
  refine ⟨(equivStatedSp n F).toMonoidHom.comp (leviHom.comp (blockHom F hk')),
    (equivStatedSp n F).injective.comp (leviHom_injective.comp (blockHom_injective hk')),
    fun c => ?_, fun c => ?_⟩
  · rw [x_eq (stdVec_shortPos_eq hk), elt_difference_eq_leviHom]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, blockHom_upper]
  · rw [x_eq (stdVec_shortNeg_eq hk), elt_difference_eq_leviHom]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, blockHom_lower]

theorem rankOne_long {i : Fin n} (hk : ¬i.val + 1 < n) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp n F, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = x n F (Pi.single i 1) c) ∧
        ∀ c, φ (sl2Lower c) = x n F (-Pi.single i 1) c := by
  have hpq : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr i := Sum.inl_ne_inr
  set ψ := blockHom F hpq
  have hψU : ∀ c : F, ψ (sl2Upper c) = (elt (.positiveLong i) c : GL (Fin n ⊕ Fin n) F) :=
    fun c => Units.ext (by
      rw [blockHom_upper, TauCeti.coe_transvectionUnit, ← mat_apply, mat_elt_positiveLong])
  have hψL : ∀ c : F, ψ (sl2Lower c) = (elt (.negativeLong i) c : GL (Fin n ⊕ Fin n) F) :=
    fun c => Units.ext (by
      rw [blockHom_lower, TauCeti.coe_transvectionUnit, ← mat_apply, mat_elt_negativeLong])
  have hmem : ∀ A, ψ A ∈ StatedSp n F := by
    intro A
    have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (StatedSp n F).comap ψ := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change ψ (sl2Upper c) ∈ StatedSp n F
        rw [hψU]
        exact (elt _ c).2
      · change ψ (sl2Lower c) ∈ StatedSp n F
        rw [hψL]
        exact (elt _ c).2
    exact hle (mem_closure_sl2 A)
  refine ⟨ψ.codRestrict (StatedSp n F) hmem,
    fun A B h => blockHom_injective hpq (congrArg Subtype.val h), fun c => ?_, fun c => ?_⟩
  · rw [x_eq (stdVec_positiveLong_eq hk)]
    exact Subtype.ext (hψU c)
  · rw [x_eq (stdVec_negativeLong_eq hk)]
    exact Subtype.ext (hψL c)

theorem rankOne (i : Fin n) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp n F, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = x n F (Pi.single i 1) c) ∧
        ∀ c, φ (sl2Lower c) = x n F (-Pi.single i 1) c := by
  by_cases hk : i.val + 1 < n
  · exact rankOne_short hk
  · exact rankOne_long hk

end CFSG.LieType.Steinberg.Sp
