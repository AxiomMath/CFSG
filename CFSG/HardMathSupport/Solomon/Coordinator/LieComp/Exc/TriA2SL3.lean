module

public import CFSG.Timmesfeld.RankTwo.Positive
public import CFSG.LieType.Steinberg.PartB

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.LieType CFSG.LieType.Steinberg CFSG.Timmesfeld
open CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

local notation "W₂" => sl2Upper 1 * sl2Lower (-1) * sl2Upper 1

local notation "Φ" => Steinberg.RootSystem.ofCartan (isFiniteType_A 2) ∅

section SL2

variable {F : Type} [Field F]

private theorem coe_sl2Upper' (c : F) :
    (sl2Upper c : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := rfl

private theorem coe_sl2Lower' (c : F) :
    (sl2Lower c : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := rfl

private theorem sl2Upper_add (a b : F) : sl2Upper (a + b) = sl2Upper a * sl2Upper b := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper', coe_sl2Upper', coe_sl2Upper']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem coe_W₂ : ((W₂ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper', coe_sl2Lower']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem conj_upper_of_coe {w : SL(2, F)}
    (hw : (w : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0]) (c : F) :
    w * sl2Upper c * w⁻¹ = sl2Lower (-c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hw, coe_sl2Upper',
    coe_sl2Lower']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem conj_lower_of_coe {w : SL(2, F)}
    (hw : (w : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0]) (c : F) :
    w * sl2Lower c * w⁻¹ = sl2Upper (-c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hw, coe_sl2Upper',
    coe_sl2Lower']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem W₂_conj_upper (c : F) :
    (W₂ : SL(2, F)) * sl2Upper c * (W₂ : SL(2, F))⁻¹ = sl2Lower (-c) :=
  conj_upper_of_coe coe_W₂ c

private theorem W₂_conj_lower (c : F) :
    (W₂ : SL(2, F)) * sl2Lower c * (W₂ : SL(2, F))⁻¹ = sl2Upper (-c) :=
  conj_lower_of_coe coe_W₂ c

end SL2

section Frame

variable {F : Type} [Field F] {G : Type} [Group G]

private theorem map_zero_of_add {f : F → G} (hf : ∀ a b, f (a + b) = f a * f b) : f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

private theorem map_neg_of_add {f : F → G} (hf : ∀ a b, f (a + b) = f a * f b) (a : F) :
    f (-a) = (f a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hf, neg_add_cancel, map_zero_of_add hf]

private theorem heis_mul {P₁ P₂ P₃ : F → G} (h₁ : ∀ a b, P₁ (a + b) = P₁ a * P₁ b)
    (h₂ : ∀ a b, P₂ (a + b) = P₂ a * P₂ b) (h₃ : ∀ a b, P₃ (a + b) = P₃ a * P₃ b)
    (hcomm : ∀ u w, P₁ u * P₂ w * (P₁ u)⁻¹ * (P₂ w)⁻¹ = P₃ (u * w))
    (h13 : ∀ u w, P₁ u * P₃ w = P₃ w * P₁ u) (h23 : ∀ u w, P₂ u * P₃ w = P₃ w * P₂ u)
    (a e b a' e' b' : F) :
    P₁ a * P₃ (e - a * b) * P₂ b * (P₁ a' * P₃ (e' - a' * b') * P₂ b') =
      P₁ (a + a') * P₃ ((e + a * b' + e') - (a + a') * (b + b')) * P₂ (b + b') := by
  have hsw : P₂ b * P₁ a' = P₃ (-(a' * b)) * (P₁ a' * P₂ b) := by
    rw [map_neg_of_add h₃, ← hcomm a' b]
    group
  have e1 : (e + a * b' + e') - (a + a') * (b + b') =
      (e - a * b) + (-(a' * b)) + (e' - a' * b') := by ring
  have hc : P₃ (e - a * b) * P₃ (-(a' * b)) * P₁ a' =
      P₁ a' * (P₃ (e - a * b) * P₃ (-(a' * b))) := by
    rw [← h₃]
    exact (h13 a' _).symm
  rw [e1, h₁, h₂, h₃, h₃]
  calc P₁ a * P₃ (e - a * b) * P₂ b * (P₁ a' * P₃ (e' - a' * b') * P₂ b')
      = P₁ a * P₃ (e - a * b) * (P₂ b * P₁ a') * P₃ (e' - a' * b') * P₂ b' := by group
    _ = P₁ a * P₃ (e - a * b) * (P₃ (-(a' * b)) * (P₁ a' * P₂ b)) * P₃ (e' - a' * b') *
          P₂ b' := by rw [hsw]
    _ = P₁ a * (P₃ (e - a * b) * P₃ (-(a' * b))) * P₁ a' * (P₂ b * P₃ (e' - a' * b')) *
          P₂ b' := by group
    _ = P₁ a * (P₃ (e - a * b) * P₃ (-(a' * b))) * P₁ a' * (P₃ (e' - a' * b') * P₂ b) *
          P₂ b' := by rw [h23 b (e' - a' * b')]
    _ = P₁ a * ((P₃ (e - a * b) * P₃ (-(a' * b))) * P₁ a') * P₃ (e' - a' * b') *
          (P₂ b * P₂ b') := by group
    _ = P₁ a * (P₁ a' * (P₃ (e - a * b) * P₃ (-(a' * b)))) * P₃ (e' - a' * b') *
          (P₂ b * P₂ b') := by rw [hc]
    _ = P₁ a * P₁ a' * (P₃ (e - a * b) * P₃ (-(a' * b)) * P₃ (e' - a' * b')) *
          (P₂ b * P₂ b') := by group

end Frame

section Transvections

variable {F : Type} [Field F]

private abbrev T01 (c : F) : SL(3, F) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c

private abbrev T12 (c : F) : SL(3, F) :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c

private abbrev T02 (c : F) : SL(3, F) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c

private abbrev T10 (c : F) : SL(3, F) :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c

private abbrev T21 (c : F) : SL(3, F) :=
  Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c

private abbrev T20 (c : F) : SL(3, F) :=
  Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c

end Transvections

section Upper

variable (F : Type) [Field F]

private def utri : Subgroup SL(3, F) where
  carrier := {g | g 0 0 = 1 ∧ g 1 1 = 1 ∧ g 2 2 = 1 ∧ g 1 0 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0}
  mul_mem' := by
    rintro a b ⟨ha00, ha11, ha22, ha10, ha20, ha21⟩ ⟨hb00, hb11, hb22, hb10, hb20, hb21⟩
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, *]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha00, ha11, ha22, ha10, ha20, ha21⟩
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, *]

variable {F}

private theorem T01_mem_utri (c : F) : T01 c ∈ utri F := by
  simp [utri, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem T12_mem_utri (c : F) : T12 c ∈ utri F := by
  simp [utri, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem T02_mem_utri (c : F) : T02 c ∈ utri F := by
  simp [utri, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

variable {G : Type} [Group G]

private theorem exists_hom_upper {P₁ P₂ P₃ : F → G} (h₁ : ∀ a b, P₁ (a + b) = P₁ a * P₁ b)
    (h₂ : ∀ a b, P₂ (a + b) = P₂ a * P₂ b) (h₃ : ∀ a b, P₃ (a + b) = P₃ a * P₃ b)
    (hcomm : ∀ u w, P₁ u * P₂ w * (P₁ u)⁻¹ * (P₂ w)⁻¹ = P₃ (u * w))
    (h13 : ∀ u w, P₁ u * P₃ w = P₃ w * P₁ u) (h23 : ∀ u w, P₂ u * P₃ w = P₃ w * P₂ u) :
    ∃ θ : utri F →* G, (∀ c, θ ⟨T01 c, T01_mem_utri c⟩ = P₁ c) ∧
      (∀ c, θ ⟨T12 c, T12_mem_utri c⟩ = P₂ c) ∧ (∀ c, θ ⟨T02 c, T02_mem_utri c⟩ = P₃ c) := by
  have z₁ := map_zero_of_add h₁
  have z₂ := map_zero_of_add h₂
  have z₃ := map_zero_of_add h₃
  refine ⟨{ toFun := fun g => P₁ (g.1 0 1) * P₃ (g.1 0 2 - g.1 0 1 * g.1 1 2) * P₂ (g.1 1 2)
            map_one' := ?_
            map_mul' := ?_ }, ?_, ?_, ?_⟩
  · simp [z₁, z₂, z₃]
  · rintro ⟨a, ha00, ha11, ha22, ha10, ha20, ha21⟩ ⟨b, hb00, hb11, hb22, hb10, hb20, hb21⟩
    have e01 : (a * b : SL(3, F)) 0 1 = a 0 1 + b 0 1 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, *]
      ring
    have e12 : (a * b : SL(3, F)) 1 2 = a 1 2 + b 1 2 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, *]
      ring
    have e02 : (a * b : SL(3, F)) 0 2 = a 0 2 + a 0 1 * b 1 2 + b 0 2 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, *]
      ring
    change P₁ ((a * b : SL(3, F)) 0 1) * P₃ ((a * b : SL(3, F)) 0 2 -
        (a * b : SL(3, F)) 0 1 * (a * b : SL(3, F)) 1 2) * P₂ ((a * b : SL(3, F)) 1 2) =
      P₁ (a 0 1) * P₃ (a 0 2 - a 0 1 * a 1 2) * P₂ (a 1 2) *
        (P₁ (b 0 1) * P₃ (b 0 2 - b 0 1 * b 1 2) * P₂ (b 1 2))
    rw [e01, e02, e12]
    exact (heis_mul h₁ h₂ h₃ hcomm h13 h23 _ _ _ _ _ _).symm
  · intro c
    simp [T01, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, z₂, z₃]
  · intro c
    simp [T12, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, z₁, z₃]
  · intro c
    simp [T02, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, z₁, z₂]

end Upper

section RankOne

variable {F : Type} [Field F]

private def blkTop (A : SL(2, F)) : SL(3, F) :=
  ⟨!![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    simp [Matrix.det_fin_three]
    linear_combination h⟩

private theorem coe_blkTop (A : SL(2, F)) : (blkTop A : Matrix (Fin 3) (Fin 3) F) =
    !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := rfl

private def embTop : SL(2, F) →* SL(3, F) where
  toFun := blkTop
  map_one' := by
    ext i j
    rw [coe_blkTop, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_blkTop, coe_blkTop, coe_blkTop,
      Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

private def blkBot (A : SL(2, F)) : SL(3, F) :=
  ⟨!![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    simp [Matrix.det_fin_three]
    linear_combination h⟩

private theorem coe_blkBot (A : SL(2, F)) : (blkBot A : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1] := rfl

private def embBot : SL(2, F) →* SL(3, F) where
  toFun := blkBot
  map_one' := by
    ext i j
    rw [coe_blkBot, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_blkBot, coe_blkBot, coe_blkBot,
      Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

private theorem embTop_injective : Function.Injective (embTop (F := F)) := by
  intro A B h
  have h' := congrArg (fun X : SL(3, F) => (X : Matrix (Fin 3) (Fin 3) F)) h
  ext i j
  have := congrFun (congrFun h' (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [embTop, coe_blkTop] using this

private theorem embBot_injective : Function.Injective (embBot (F := F)) := by
  intro A B h
  have h' := congrArg (fun X : SL(3, F) => (X : Matrix (Fin 3) (Fin 3) F)) h
  ext i j
  have := congrFun (congrFun h' (Fin.succ i)) (Fin.succ j)
  fin_cases i <;> fin_cases j <;> simpa [embBot, coe_blkBot] using this

private theorem embTop_upper (c : F) : embTop (sl2Upper c) = T01 c := by
  ext i j
  show (blkTop (sl2Upper c) : Matrix (Fin 3) (Fin 3) F) i j = _
  rw [coe_blkTop]
  fin_cases i <;> fin_cases j <;>
    simp [coe_sl2Upper', Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem embTop_lower (c : F) : embTop (sl2Lower c) = T10 c := by
  ext i j
  show (blkTop (sl2Lower c) : Matrix (Fin 3) (Fin 3) F) i j = _
  rw [coe_blkTop]
  fin_cases i <;> fin_cases j <;>
    simp [coe_sl2Lower', Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem embBot_upper (c : F) : embBot (sl2Upper c) = T12 c := by
  ext i j
  show (blkBot (sl2Upper c) : Matrix (Fin 3) (Fin 3) F) i j = _
  rw [coe_blkBot]
  fin_cases i <;> fin_cases j <;>
    simp [coe_sl2Upper', Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem embBot_lower (c : F) : embBot (sl2Lower c) = T21 c := by
  ext i j
  show (blkBot (sl2Lower c) : Matrix (Fin 3) (Fin 3) F) i j = _
  rw [coe_blkBot]
  fin_cases i <;> fin_cases j <;>
    simp [coe_sl2Lower', Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem exists_hom_range {G H K : Type} [Group G] [Group H] [Group K] (e : H →* K)
    (he : Function.Injective e) (θ : H →* G) :
    ∃ θ' : e.range →* G, ∀ y (h : e y ∈ e.range), θ' ⟨e y, h⟩ = θ y := by
  refine ⟨θ.comp (MonoidHom.ofInjective he).symm.toMonoidHom, fun y h => ?_⟩
  have : (⟨e y, h⟩ : e.range) = MonoidHom.ofInjective he y := Subtype.ext rfl
  rw [this]
  simp

private theorem exists_hom_top {G : Type} [Group G] (θ : SL(2, F) →* G) :
    ∃ (S : Subgroup SL(3, F)) (θ' : S →* G),
      (∀ c, ∃ h : T01 c ∈ S, θ' ⟨T01 c, h⟩ = θ (sl2Upper c)) ∧
      (∀ c, ∃ h : T10 c ∈ S, θ' ⟨T10 c, h⟩ = θ (sl2Lower c)) := by
  obtain ⟨θ', hθ'⟩ := exists_hom_range embTop embTop_injective θ
  refine ⟨embTop.range, θ', fun c => ?_, fun c => ?_⟩
  · have h : T01 c ∈ embTop.range := ⟨sl2Upper c, embTop_upper c⟩
    refine ⟨h, ?_⟩
    have := hθ' (sl2Upper c) ⟨sl2Upper c, rfl⟩
    rw [← this]
    congr 1
    exact Subtype.ext (embTop_upper c).symm
  · have h : T10 c ∈ embTop.range := ⟨sl2Lower c, embTop_lower c⟩
    refine ⟨h, ?_⟩
    have := hθ' (sl2Lower c) ⟨sl2Lower c, rfl⟩
    rw [← this]
    congr 1
    exact Subtype.ext (embTop_lower c).symm

private theorem exists_hom_bot {G : Type} [Group G] (θ : SL(2, F) →* G) :
    ∃ (S : Subgroup SL(3, F)) (θ' : S →* G),
      (∀ c, ∃ h : T12 c ∈ S, θ' ⟨T12 c, h⟩ = θ (sl2Upper c)) ∧
      (∀ c, ∃ h : T21 c ∈ S, θ' ⟨T21 c, h⟩ = θ (sl2Lower c)) := by
  obtain ⟨θ', hθ'⟩ := exists_hom_range embBot embBot_injective θ
  refine ⟨embBot.range, θ', fun c => ?_, fun c => ?_⟩
  · have h : T12 c ∈ embBot.range := ⟨sl2Upper c, embBot_upper c⟩
    refine ⟨h, ?_⟩
    have := hθ' (sl2Upper c) ⟨sl2Upper c, rfl⟩
    rw [← this]
    congr 1
    exact Subtype.ext (embBot_upper c).symm
  · have h : T21 c ∈ embBot.range := ⟨sl2Lower c, embBot_lower c⟩
    refine ⟨h, ?_⟩
    have := hθ' (sl2Lower c) ⟨sl2Lower c, rfl⟩
    rw [← this]
    congr 1
    exact Subtype.ext (embBot_lower c).symm

end RankOne

section Weyl

variable {F : Type} [Field F]

private theorem coe_weylRep_zero :
    ((weylRep 2 F 0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylRep, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.SpecialLinearGroup.transvection_coe]

private theorem coe_weylRep_one :
    ((weylRep 2 F 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, 1; 0, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylRep, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.SpecialLinearGroup.transvection_coe]

private theorem conj_of_mul_eq {n g g' : SL(3, F)} (h : n * g = g' * n) : n * g * n⁻¹ = g' := by
  rw [mul_inv_eq_iff_eq_mul]
  exact h

private theorem n0_conj_T01 (c : F) : weylRep 2 F 0 * T01 c * (weylRep 2 F 0)⁻¹ = T10 (-c) := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_zero]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n0_conj_T12 (c : F) : weylRep 2 F 0 * T12 c * (weylRep 2 F 0)⁻¹ = T02 c := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_zero]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n0_conj_T02 (c : F) : weylRep 2 F 0 * T02 c * (weylRep 2 F 0)⁻¹ = T12 (-c) := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_zero]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n0_conj_T10 (c : F) : weylRep 2 F 0 * T10 c * (weylRep 2 F 0)⁻¹ = T01 (-c) := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_zero]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n0_conj_T21 (c : F) : weylRep 2 F 0 * T21 c * (weylRep 2 F 0)⁻¹ = T20 c := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_zero]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n0_conj_T20 (c : F) : weylRep 2 F 0 * T20 c * (weylRep 2 F 0)⁻¹ = T21 (-c) := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_zero]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n1_conj_T01 (c : F) : weylRep 2 F 1 * T01 c * (weylRep 2 F 1)⁻¹ = T02 (-c) := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n1_conj_T12 (c : F) : weylRep 2 F 1 * T12 c * (weylRep 2 F 1)⁻¹ = T21 (-c) := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n1_conj_T02 (c : F) : weylRep 2 F 1 * T02 c * (weylRep 2 F 1)⁻¹ = T01 c := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n1_conj_T10 (c : F) : weylRep 2 F 1 * T10 c * (weylRep 2 F 1)⁻¹ = T20 (-c) := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n1_conj_T21 (c : F) : weylRep 2 F 1 * T21 c * (weylRep 2 F 1)⁻¹ = T12 (-c) := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

private theorem n1_conj_T20 (c : F) : weylRep 2 F 1 * T20 c * (weylRep 2 F 1)⁻¹ = T10 c := by
  refine conj_of_mul_eq ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply]

end Weyl

section Roots

private theorem mem_roots_iff (γ : Fin 2 → ℤ) :
    γ ∈ (Φ).roots ↔ γ = ![1, 0] ∨ γ = ![0, 1] ∨ γ = ![1, 1] ∨ γ = ![-1, 0] ∨ γ = ![0, -1] ∨
      γ = ![-1, -1] := by
  change γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A 2) ∅ ↔ _
  rw [roots_eq]
  constructor
  · rintro ⟨i, j, hij, h⟩
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have hγ : γ = ![γ 0, γ 1] := by
      ext k
      fin_cases k <;> rfl
    rw [hγ]
    fin_cases i <;> fin_cases j <;> simp [toStd, Pi.single_apply] at h0 h1 h2 hij ⊢ <;> omega
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, by funext a; fin_cases a <;> simp [toStd]⟩
    · exact ⟨1, 2, by decide, by funext a; fin_cases a <;> simp [toStd]⟩
    · exact ⟨0, 2, by decide, by funext a; fin_cases a <;> simp [toStd]⟩
    · exact ⟨1, 0, by decide, by funext a; fin_cases a <;> simp [toStd]⟩
    · exact ⟨2, 1, by decide, by funext a; fin_cases a <;> simp [toStd]⟩
    · exact ⟨2, 0, by decide, by funext a; fin_cases a <;> simp [toStd]⟩

private theorem refl_apply (i : Fin 2) (v : Fin 2 → ℤ) :
    (Φ).refl i v = v - (∑ j, CartanMatrix.A 2 i j * v j) • (Pi.single i 1 : Fin 2 → ℤ) := by
  rw [RootSystem.ofCartan_refl_apply, CFSG.LieType.RootSystem.reflection_apply]

private theorem refl_table :
    (Φ).refl 0 ![1, 0] = ![-1, 0] ∧ (Φ).refl 0 ![0, 1] = ![1, 1] ∧ (Φ).refl 0 ![1, 1] = ![0, 1] ∧
    (Φ).refl 0 ![-1, 0] = ![1, 0] ∧ (Φ).refl 0 ![0, -1] = ![-1, -1] ∧
      (Φ).refl 0 ![-1, -1] = ![0, -1] ∧
    (Φ).refl 1 ![1, 0] = ![1, 1] ∧ (Φ).refl 1 ![0, 1] = ![0, -1] ∧ (Φ).refl 1 ![1, 1] = ![1, 0] ∧
    (Φ).refl 1 ![-1, 0] = ![-1, -1] ∧ (Φ).refl 1 ![0, -1] = ![0, 1] ∧
      (Φ).refl 1 ![-1, -1] = ![-1, 0] := by
  simp only [refl_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext k; fin_cases k <;> simp [CartanMatrix.A, Fin.sum_univ_two, Pi.single_apply])

private theorem pos_cases {γ : Fin 2 → ℤ} (h : γ ∈ (Φ).pos) :
    γ = ![1, 0] ∨ γ = ![0, 1] ∨ γ = ![1, 1] := by
  obtain ⟨h1, h2⟩ := h
  rcases (mem_roots_iff γ).1 h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  all_goals
    exfalso
    simp [ht, Fin.sum_univ_two] at h2

private theorem single_zero : (Pi.single (0 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) = ![1, 0] := by
  ext k
  fin_cases k <;> simp

private theorem single_one : (Pi.single (1 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) = ![0, 1] := by
  ext k
  fin_cases k <;> simp

private theorem neg_single_zero : (-Pi.single (0 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) = ![-1, 0] := by
  ext k
  fin_cases k <;> simp

private theorem neg_single_one : (-Pi.single (1 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) = ![0, -1] := by
  ext k
  fin_cases k <;> simp

end Roots

section RootGroups

variable (F : Type) [Field F]

private theorem rootGroup_a1 :
    rootGroup 2 F ![1, 0] = rootSubgroup 2 F (show (0 : Fin 3) ≠ 1 by decide) :=
  rootGroup_eq 2 F _ (by funext a; fin_cases a <;> simp [toStd])

private theorem rootGroup_a2 :
    rootGroup 2 F ![0, 1] = rootSubgroup 2 F (show (1 : Fin 3) ≠ 2 by decide) :=
  rootGroup_eq 2 F _ (by funext a; fin_cases a <;> simp [toStd])

private theorem rootGroup_a12 :
    rootGroup 2 F ![1, 1] = rootSubgroup 2 F (show (0 : Fin 3) ≠ 2 by decide) :=
  rootGroup_eq 2 F _ (by funext a; fin_cases a <;> simp [toStd])

private theorem rootGroup_m1 :
    rootGroup 2 F ![-1, 0] = rootSubgroup 2 F (show (1 : Fin 3) ≠ 0 by decide) :=
  rootGroup_eq 2 F _ (by funext a; fin_cases a <;> simp [toStd])

private theorem rootGroup_m2 :
    rootGroup 2 F ![0, -1] = rootSubgroup 2 F (show (2 : Fin 3) ≠ 1 by decide) :=
  rootGroup_eq 2 F _ (by funext a; fin_cases a <;> simp [toStd])

private theorem rootGroup_m12 :
    rootGroup 2 F ![-1, -1] = rootSubgroup 2 F (show (2 : Fin 3) ≠ 0 by decide) :=
  rootGroup_eq 2 F _ (by funext a; fin_cases a <;> simp [toStd])

variable {F}

private theorem mem_rootGroup_a1 {x : SL(3, F)} : x ∈ rootGroup 2 F ![1, 0] ↔ ∃ c, T01 c = x := by
  rw [rootGroup_a1, mem_rootSubgroup]

private theorem mem_rootGroup_a2 {x : SL(3, F)} : x ∈ rootGroup 2 F ![0, 1] ↔ ∃ c, T12 c = x := by
  rw [rootGroup_a2, mem_rootSubgroup]

private theorem mem_rootGroup_a12 {x : SL(3, F)} :
    x ∈ rootGroup 2 F ![1, 1] ↔ ∃ c, T02 c = x := by
  rw [rootGroup_a12, mem_rootSubgroup]

private theorem mem_rootGroup_m1 {x : SL(3, F)} :
    x ∈ rootGroup 2 F ![-1, 0] ↔ ∃ c, T10 c = x := by
  rw [rootGroup_m1, mem_rootSubgroup]

private theorem mem_rootGroup_m2 {x : SL(3, F)} :
    x ∈ rootGroup 2 F ![0, -1] ↔ ∃ c, T21 c = x := by
  rw [rootGroup_m2, mem_rootSubgroup]

private theorem mem_rootGroup_m12 {x : SL(3, F)} :
    x ∈ rootGroup 2 F ![-1, -1] ↔ ∃ c, T20 c = x := by
  rw [rootGroup_m12, mem_rootSubgroup]

end RootGroups

section Pf

variable {F : Type} [Field F] {G : Type} [Group G] (P₁ P₂ P₃ M₁ M₂ M₃ : F → G)

private def Pf (γ : Fin 2 → ℤ) (g : SL(3, F)) : G :=
  if γ = ![1, 0] then P₁ (g 0 1) else if γ = ![0, 1] then P₂ (g 1 2) else
  if γ = ![1, 1] then P₃ (g 0 2) else if γ = ![-1, 0] then M₁ (g 1 0) else
  if γ = ![0, -1] then M₂ (g 2 1) else if γ = ![-1, -1] then M₃ (g 2 0) else 1

variable {P₁ P₂ P₃ M₁ M₂ M₃}

private theorem Pf_T01 (c : F) : Pf P₁ P₂ P₃ M₁ M₂ M₃ ![1, 0] (T01 c) = P₁ c := by
  simp [Pf, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem Pf_T12 (c : F) : Pf P₁ P₂ P₃ M₁ M₂ M₃ ![0, 1] (T12 c) = P₂ c := by
  simp [Pf, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem Pf_T02 (c : F) : Pf P₁ P₂ P₃ M₁ M₂ M₃ ![1, 1] (T02 c) = P₃ c := by
  simp [Pf, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem Pf_T10 (c : F) : Pf P₁ P₂ P₃ M₁ M₂ M₃ ![-1, 0] (T10 c) = M₁ c := by
  simp [Pf, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem Pf_T21 (c : F) : Pf P₁ P₂ P₃ M₁ M₂ M₃ ![0, -1] (T21 c) = M₂ c := by
  simp [Pf, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem Pf_T20 (c : F) : Pf P₁ P₂ P₃ M₁ M₂ M₃ ![-1, -1] (T20 c) = M₃ c := by
  simp [Pf, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem Pf_weyl {ñ : Fin 2 → G}
    (w0P1 : ∀ c, ñ 0 * P₁ c * (ñ 0)⁻¹ = M₁ (-c)) (w0P2 : ∀ c, ñ 0 * P₂ c * (ñ 0)⁻¹ = P₃ c)
    (w0P3 : ∀ c, ñ 0 * P₃ c * (ñ 0)⁻¹ = P₂ (-c)) (w0M1 : ∀ c, ñ 0 * M₁ c * (ñ 0)⁻¹ = P₁ (-c))
    (w0M2 : ∀ c, ñ 0 * M₂ c * (ñ 0)⁻¹ = M₃ c) (w0M3 : ∀ c, ñ 0 * M₃ c * (ñ 0)⁻¹ = M₂ (-c))
    (w1P1 : ∀ c, ñ 1 * P₁ c * (ñ 1)⁻¹ = P₃ (-c)) (w1P2 : ∀ c, ñ 1 * P₂ c * (ñ 1)⁻¹ = M₂ (-c))
    (w1P3 : ∀ c, ñ 1 * P₃ c * (ñ 1)⁻¹ = P₁ c) (w1M1 : ∀ c, ñ 1 * M₁ c * (ñ 1)⁻¹ = M₃ (-c))
    (w1M2 : ∀ c, ñ 1 * M₂ c * (ñ 1)⁻¹ = P₂ (-c)) (w1M3 : ∀ c, ñ 1 * M₃ c * (ñ 1)⁻¹ = M₁ c)
    (i : Fin 2) {γ : Fin 2 → ℤ} (hγ : γ ∈ (Φ).roots) {g : SL(3, F)} (hg : g ∈ rootGroup 2 F γ) :
    ñ i * Pf P₁ P₂ P₃ M₁ M₂ M₃ γ g * (ñ i)⁻¹ =
      Pf P₁ P₂ P₃ M₁ M₂ M₃ ((Φ).refl i γ) (weylRep 2 F i * g * (weylRep 2 F i)⁻¹) := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  obtain ⟨r00, r01, r02, r03, r04, r05, r10, r11, r12, r13, r14, r15⟩ := refl_table
  rcases (mem_roots_iff γ).1 hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hi with rfl | rfl
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a1.1 hg
    rw [r00, n0_conj_T01, Pf_T01, Pf_T10]
    exact w0P1 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a1.1 hg
    rw [r10, n1_conj_T01, Pf_T01, Pf_T02]
    exact w1P1 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a2.1 hg
    rw [r01, n0_conj_T12, Pf_T12, Pf_T02]
    exact w0P2 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a2.1 hg
    rw [r11, n1_conj_T12, Pf_T12, Pf_T21]
    exact w1P2 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a12.1 hg
    rw [r02, n0_conj_T02, Pf_T02, Pf_T12]
    exact w0P3 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a12.1 hg
    rw [r12, n1_conj_T02, Pf_T02, Pf_T01]
    exact w1P3 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_m1.1 hg
    rw [r03, n0_conj_T10, Pf_T10, Pf_T01]
    exact w0M1 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_m1.1 hg
    rw [r13, n1_conj_T10, Pf_T10, Pf_T20]
    exact w1M1 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_m2.1 hg
    rw [r04, n0_conj_T21, Pf_T21, Pf_T20]
    exact w0M2 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_m2.1 hg
    rw [r14, n1_conj_T21, Pf_T21, Pf_T12]
    exact w1M2 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_m12.1 hg
    rw [r05, n0_conj_T20, Pf_T20, Pf_T21]
    exact w0M3 c
  · obtain ⟨c, rfl⟩ := mem_rootGroup_m12.1 hg
    rw [r15, n1_conj_T20, Pf_T20, Pf_T10]
    exact w1M3 c

end Pf

private theorem map_conj {F G : Type} [Field F] [Group G] (θ : SL(2, F) →* G) (a b : SL(2, F)) :
    θ a * θ b * (θ a)⁻¹ = θ (a * b * a⁻¹) := by
  rw [map_mul, map_mul, map_inv]

section Assembly

variable {F : Type} [Field F] {G : Type} [Group G] {P₁ P₂ P₃ M₁ M₂ M₃ : F → G}
  {φ : ∀ γ, rootGroup 2 F γ → G}

private theorem extendsToHom_pos
    (hφ : ∀ γ x, φ γ x = Pf P₁ P₂ P₃ M₁ M₂ M₃ γ x.1)
    (h₁ : ∀ a b, P₁ (a + b) = P₁ a * P₁ b) (h₂ : ∀ a b, P₂ (a + b) = P₂ a * P₂ b)
    (h₃ : ∀ a b, P₃ (a + b) = P₃ a * P₃ b)
    (hcomm : ∀ u w, P₁ u * P₂ w * (P₁ u)⁻¹ * (P₂ w)⁻¹ = P₃ (u * w))
    (h13 : ∀ u w, P₁ u * P₃ w = P₃ w * P₁ u) (h23 : ∀ u w, P₂ u * P₃ w = P₃ w * P₂ u) :
    ExtendsToHom (rootGroup 2 F) (Φ).pos φ := by
  obtain ⟨θ, h1, h2, h3⟩ := exists_hom_upper h₁ h₂ h₃ hcomm h13 h23
  refine ⟨utri F, θ, fun γ hγ x => ?_⟩
  obtain ⟨x, hx⟩ := x
  rw [hφ]
  rcases pos_cases hγ with rfl | rfl | rfl
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a1.1 hx
    exact ⟨T01_mem_utri c, (h1 c).trans (Pf_T01 c).symm⟩
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a2.1 hx
    exact ⟨T12_mem_utri c, (h2 c).trans (Pf_T12 c).symm⟩
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a12.1 hx
    exact ⟨T02_mem_utri c, (h3 c).trans (Pf_T02 c).symm⟩

private theorem extendsToHom_rank0 (θ₁ : SL(2, F) →* G)
    (hφ : ∀ γ x, φ γ x = Pf P₁ P₂ P₃ M₁ M₂ M₃ γ x.1)
    (hθ₁u : ∀ c, θ₁ (sl2Upper c) = P₁ c) (hθ₁l : ∀ c, θ₁ (sl2Lower c) = M₁ c) :
    ExtendsToHom (rootGroup 2 F) {![1, 0], ![-1, 0]} φ := by
  obtain ⟨S, θ, h1, h2⟩ := exists_hom_top θ₁
  refine ⟨S, θ, fun γ hγ x => ?_⟩
  obtain ⟨x, hx⟩ := x
  rw [hφ]
  rcases hγ with rfl | rfl
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a1.1 hx
    obtain ⟨h, hh⟩ := h1 c
    exact ⟨h, by rw [hh, hθ₁u, Pf_T01]⟩
  · obtain ⟨c, rfl⟩ := mem_rootGroup_m1.1 hx
    obtain ⟨h, hh⟩ := h2 c
    exact ⟨h, by rw [hh, hθ₁l, Pf_T10]⟩

private theorem extendsToHom_rank1 (θ₂ : SL(2, F) →* G)
    (hφ : ∀ γ x, φ γ x = Pf P₁ P₂ P₃ M₁ M₂ M₃ γ x.1)
    (hθ₂u : ∀ c, θ₂ (sl2Upper c) = P₂ c) (hθ₂l : ∀ c, θ₂ (sl2Lower c) = M₂ c) :
    ExtendsToHom (rootGroup 2 F) {![0, 1], ![0, -1]} φ := by
  obtain ⟨S, θ, h1, h2⟩ := exists_hom_bot θ₂
  refine ⟨S, θ, fun γ hγ x => ?_⟩
  obtain ⟨x, hx⟩ := x
  rw [hφ]
  rcases hγ with rfl | rfl
  · obtain ⟨c, rfl⟩ := mem_rootGroup_a2.1 hx
    obtain ⟨h, hh⟩ := h1 c
    exact ⟨h, by rw [hh, hθ₂u, Pf_T12]⟩
  · obtain ⟨c, rfl⟩ := mem_rootGroup_m2.1 hx
    obtain ⟨h, hh⟩ := h2 c
    exact ⟨h, by rw [hh, hθ₂l, Pf_T21]⟩

private theorem coneCompatible_frame {ñ : Fin 2 → G}
    (hφ : ∀ γ x, φ γ x = Pf P₁ P₂ P₃ M₁ M₂ M₃ γ x.1)
    (w0P1 : ∀ c, ñ 0 * P₁ c * (ñ 0)⁻¹ = M₁ (-c)) (w0P2 : ∀ c, ñ 0 * P₂ c * (ñ 0)⁻¹ = P₃ c)
    (w0P3 : ∀ c, ñ 0 * P₃ c * (ñ 0)⁻¹ = P₂ (-c)) (w0M1 : ∀ c, ñ 0 * M₁ c * (ñ 0)⁻¹ = P₁ (-c))
    (w0M2 : ∀ c, ñ 0 * M₂ c * (ñ 0)⁻¹ = M₃ c) (w0M3 : ∀ c, ñ 0 * M₃ c * (ñ 0)⁻¹ = M₂ (-c))
    (w1P1 : ∀ c, ñ 1 * P₁ c * (ñ 1)⁻¹ = P₃ (-c)) (w1P2 : ∀ c, ñ 1 * P₂ c * (ñ 1)⁻¹ = M₂ (-c))
    (w1P3 : ∀ c, ñ 1 * P₃ c * (ñ 1)⁻¹ = P₁ c) (w1M1 : ∀ c, ñ 1 * M₁ c * (ñ 1)⁻¹ = M₃ (-c))
    (w1M2 : ∀ c, ñ 1 * M₂ c * (ñ 1)⁻¹ = P₂ (-c)) (w1M3 : ∀ c, ñ 1 * M₃ c * (ñ 1)⁻¹ = M₁ c)
    (hpos : ExtendsToHom (rootGroup 2 F) (Φ).pos φ)
    (hrank0 : ExtendsToHom (rootGroup 2 F) {![1, 0], ![-1, 0]} φ)
    (hrank1 : ExtendsToHom (rootGroup 2 F) {![0, 1], ![0, -1]} φ) :
    ConeCompatible (Φ) (rootGroup 2 F) φ := by
  have hn : ∀ i, ∀ γ ∈ (Φ).roots, ∀ x ∈ rootGroup 2 F γ,
      weylRep 2 F i * x * (weylRep 2 F i)⁻¹ ∈ rootGroup 2 F ((Φ).refl i γ) :=
    fun i γ hγ x hx =>
      conj_mem_refl_of_isCTGroupDatum (D := rootDatum 2 F) (isCTGroupDatum 2 F) i hγ hx
  have hñ : ∀ i, ∀ γ ∈ (Φ).roots, ∀ (x : rootGroup 2 F γ) (y : rootGroup 2 F ((Φ).refl i γ)),
      (y : SL(3, F)) = weylRep 2 F i * x * (weylRep 2 F i)⁻¹ →
        ñ i * φ γ x * (ñ i)⁻¹ = φ ((Φ).refl i γ) y := by
    intro i γ hγ x y hy
    rw [hφ, hφ, hy]
    exact Pf_weyl w0P1 w0P2 w0P3 w0M1 w0M2 w0M3 w1P1 w1P2 w1P3 w1M1 w1M2 w1M3 i hγ x.2
  refine coneCompatible_of_pos (weylRep 2 F) hn ñ hñ hpos fun i => ?_
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [neg_single_zero, single_zero]
    exact hrank0
  · rw [neg_single_one, single_one]
    exact hrank1

end Assembly

theorem exists_hom_sl3_of_frame {F : Type} [Field F] {G : Type} [Group G]
    (P₁ P₂ P₃ M₁ M₂ M₃ : F → G) (θ₁ θ₂ : SL(2, F) →* G)
    (hθ₁u : ∀ c, θ₁ (sl2Upper c) = P₁ c) (hθ₁l : ∀ c, θ₁ (sl2Lower c) = M₁ c)
    (hθ₂u : ∀ c, θ₂ (sl2Upper c) = P₂ c) (hθ₂l : ∀ c, θ₂ (sl2Lower c) = M₂ c)
    (hP₃ : ∀ a b, P₃ (a + b) = P₃ a * P₃ b) (hM₃ : ∀ a b, M₃ (a + b) = M₃ a * M₃ b)
    (hcomm : ∀ u w, P₁ u * P₂ w * (P₁ u)⁻¹ * (P₂ w)⁻¹ = P₃ (u * w))
    (h13 : ∀ u w, P₁ u * P₃ w = P₃ w * P₁ u) (h23 : ∀ u w, P₂ u * P₃ w = P₃ w * P₂ u)
    (e1 : ∀ c, θ₁ W₂ * P₂ c * (θ₁ W₂)⁻¹ = P₃ c)
    (e2 : ∀ c, θ₁ W₂ * P₃ c * (θ₁ W₂)⁻¹ = P₂ (-c))
    (e3 : ∀ c, θ₁ W₂ * M₂ c * (θ₁ W₂)⁻¹ = M₃ c)
    (e4 : ∀ c, θ₁ W₂ * M₃ c * (θ₁ W₂)⁻¹ = M₂ (-c))
    (f1 : ∀ c, θ₂ W₂ * P₁ c * (θ₂ W₂)⁻¹ = P₃ (-c))
    (f2 : ∀ c, θ₂ W₂ * P₃ c * (θ₂ W₂)⁻¹ = P₁ c)
    (f3 : ∀ c, θ₂ W₂ * M₁ c * (θ₂ W₂)⁻¹ = M₃ (-c))
    (f4 : ∀ c, θ₂ W₂ * M₃ c * (θ₂ W₂)⁻¹ = M₁ c) :
    ∃ ψ : SL(3, F) →* G,
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c) = P₁ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c) = P₂ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c) = P₃ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c) = M₁ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c) = M₂ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c) =
        M₃ c) := by
  have hP₁ : ∀ a b, P₁ (a + b) = P₁ a * P₁ b := fun a b => by
    rw [← hθ₁u, sl2Upper_add, map_mul, hθ₁u, hθ₁u]
  have hP₂ : ∀ a b, P₂ (a + b) = P₂ a * P₂ b := fun a b => by
    rw [← hθ₂u, sl2Upper_add, map_mul, hθ₂u, hθ₂u]
  have w0P1 : ∀ c, θ₁ W₂ * P₁ c * (θ₁ W₂)⁻¹ = M₁ (-c) := fun c => by
    rw [← hθ₁u, ← hθ₁l, map_conj, W₂_conj_upper]
  have w0M1 : ∀ c, θ₁ W₂ * M₁ c * (θ₁ W₂)⁻¹ = P₁ (-c) := fun c => by
    rw [← hθ₁u, ← hθ₁l, map_conj, W₂_conj_lower]
  have w1P2 : ∀ c, θ₂ W₂ * P₂ c * (θ₂ W₂)⁻¹ = M₂ (-c) := fun c => by
    rw [← hθ₂u, ← hθ₂l, map_conj, W₂_conj_upper]
  have w1M2 : ∀ c, θ₂ W₂ * M₂ c * (θ₂ W₂)⁻¹ = P₂ (-c) := fun c => by
    rw [← hθ₂u, ← hθ₂l, map_conj, W₂_conj_lower]
  obtain ⟨φ, hφ⟩ : ∃ φ : ∀ γ, rootGroup 2 F γ → G,
      ∀ γ x, φ γ x = Pf P₁ P₂ P₃ M₁ M₂ M₃ γ x.1 :=
    ⟨fun γ x => Pf P₁ P₂ P₃ M₁ M₂ M₃ γ x.1, fun _ _ => rfl⟩
  have hcone : ConeCompatible (Φ) (rootGroup 2 F) φ :=
    coneCompatible_frame (ñ := ![θ₁ W₂, θ₂ W₂]) hφ w0P1 e1 e2 w0M1 e3 e4 f1 w1P2 f2 f3 w1M2 f4
      (extendsToHom_pos hφ hP₁ hP₂ hP₃ hcomm h13 h23) (extendsToHom_rank0 θ₁ hφ hθ₁u hθ₁l)
      (extendsToHom_rank1 θ₂ hφ hθ₂u hθ₂l)
  obtain ⟨ψ, hψ, -⟩ := existsUnique_hom_of_coneCompatible (presentationA_SL3 F) hcone
  refine ⟨ψ, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
  · exact (hψ ![1, 0] ((mem_roots_iff _).2 (Or.inl rfl))
      ⟨T01 c, mem_rootGroup_a1.2 ⟨c, rfl⟩⟩).trans ((hφ _ _).trans (Pf_T01 c))
  · exact (hψ ![0, 1] ((mem_roots_iff _).2 (Or.inr (Or.inl rfl)))
      ⟨T12 c, mem_rootGroup_a2.2 ⟨c, rfl⟩⟩).trans ((hφ _ _).trans (Pf_T12 c))
  · exact (hψ ![1, 1] ((mem_roots_iff _).2 (Or.inr (Or.inr (Or.inl rfl))))
      ⟨T02 c, mem_rootGroup_a12.2 ⟨c, rfl⟩⟩).trans ((hφ _ _).trans (Pf_T02 c))
  · exact (hψ ![-1, 0] ((mem_roots_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      ⟨T10 c, mem_rootGroup_m1.2 ⟨c, rfl⟩⟩).trans ((hφ _ _).trans (Pf_T10 c))
  · exact (hψ ![0, -1] ((mem_roots_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      ⟨T21 c, mem_rootGroup_m2.2 ⟨c, rfl⟩⟩).trans ((hφ _ _).trans (Pf_T21 c))
  · exact (hψ ![-1, -1] ((mem_roots_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      ⟨T20 c, mem_rootGroup_m12.2 ⟨c, rfl⟩⟩).trans ((hφ _ _).trans (Pf_T20 c))

theorem exists_hom_sl3_of_frame_of_eq {F : Type} [Field F] {G : Type} [Group G]
    (P₁ P₂ P₃ M₁ M₂ M₃ : F → G) (θ₁ θ₂ : SL(2, F) →* G) (W : SL(2, F))
    (hW : W = sl2Upper 1 * sl2Lower (-1) * sl2Upper 1)
    (hθ₁u : ∀ c, θ₁ (sl2Upper c) = P₁ c) (hθ₁l : ∀ c, θ₁ (sl2Lower c) = M₁ c)
    (hθ₂u : ∀ c, θ₂ (sl2Upper c) = P₂ c) (hθ₂l : ∀ c, θ₂ (sl2Lower c) = M₂ c)
    (hP₃ : ∀ a b, P₃ (a + b) = P₃ a * P₃ b) (hM₃ : ∀ a b, M₃ (a + b) = M₃ a * M₃ b)
    (hcomm : ∀ u w, P₁ u * P₂ w * (P₁ u)⁻¹ * (P₂ w)⁻¹ = P₃ (u * w))
    (h13 : ∀ u w, P₁ u * P₃ w = P₃ w * P₁ u) (h23 : ∀ u w, P₂ u * P₃ w = P₃ w * P₂ u)
    (e1 : ∀ c, θ₁ W * P₂ c * (θ₁ W)⁻¹ = P₃ c)
    (e2 : ∀ c, θ₁ W * P₃ c * (θ₁ W)⁻¹ = P₂ (-c))
    (e3 : ∀ c, θ₁ W * M₂ c * (θ₁ W)⁻¹ = M₃ c)
    (e4 : ∀ c, θ₁ W * M₃ c * (θ₁ W)⁻¹ = M₂ (-c))
    (f1 : ∀ c, θ₂ W * P₁ c * (θ₂ W)⁻¹ = P₃ (-c))
    (f2 : ∀ c, θ₂ W * P₃ c * (θ₂ W)⁻¹ = P₁ c)
    (f3 : ∀ c, θ₂ W * M₁ c * (θ₂ W)⁻¹ = M₃ (-c))
    (f4 : ∀ c, θ₂ W * M₃ c * (θ₂ W)⁻¹ = M₁ c) :
    ∃ ψ : SL(3, F) →* G,
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c) = P₁ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c) = P₂ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c) = P₃ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c) = M₁ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c) = M₂ c) ∧
      (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c) =
        M₃ c) := by
  subst hW
  exact exists_hom_sl3_of_frame P₁ P₂ P₃ M₁ M₂ M₃ θ₁ θ₂ hθ₁u hθ₁l hθ₂u hθ₂l hP₃ hM₃ hcomm h13 h23
    e1 e2 e3 e4 f1 f2 f3 f4

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
