module

public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.OddTranspositions.Width

public section

namespace CFSG.Fischer.Classification

open CFSG.Open CFSG.OddTranspositions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

local instance instInvertibleTwoZModThree : Invertible (2 : ZMod 3) :=
  invertibleOfNonzero (by decide)

private def e4 (i : Fin 4) : Fin 4 → ZMod 3 :=
  Pi.single i 1

private structure F3TripleData where
  v1 : Fin 4 → ZMod 3
  v2 : Fin 4 → ZMod 3
  v3 : Fin 4 → ZMod 3

private def f3Triple (d : Fin 4 → ZMod 3) : F3TripleData :=
  if d 0 = 1 then
    if d 1 = 1 then
      if d 2 = 1 then
        if d 3 = 1 then
          ⟨e4 3, e4 2, e4 1⟩
        else
          ⟨e4 2, e4 1, e4 0⟩
      else
        if d 3 = 1 then
          ⟨e4 3, e4 1, e4 0⟩
        else
          ⟨e4 2 + e4 3, e4 2 + 2 • e4 3, e4 1⟩
    else
      if d 2 = 1 then
        if d 3 = 1 then
          ⟨e4 3, e4 2, e4 0⟩
        else
          ⟨e4 2, e4 1 + e4 3, e4 1 + 2 • e4 3⟩
      else
        if d 3 = 1 then
          ⟨e4 3, e4 1 + e4 2, e4 1 + 2 • e4 2⟩
        else
          ⟨e4 2 + e4 3, e4 2 + 2 • e4 3, e4 0⟩
  else
    if d 1 = 1 then
      if d 2 = 1 then
        if d 3 = 1 then
          ⟨e4 3, e4 2, e4 1⟩
        else
          ⟨e4 2, e4 1, e4 0 + e4 3⟩
      else
        if d 3 = 1 then
          ⟨e4 3, e4 1, e4 0 + e4 2⟩
        else
          ⟨e4 2 + e4 3, e4 2 + 2 • e4 3, e4 1⟩
    else
      if d 2 = 1 then
        if d 3 = 1 then
          ⟨e4 3, e4 2, e4 0 + e4 1⟩
        else
          ⟨e4 2, e4 1 + e4 3, e4 1 + 2 • e4 3⟩
      else
        if d 3 = 1 then
          ⟨e4 3, e4 1 + e4 2, e4 1 + 2 • e4 2⟩
        else
          ⟨e4 2 + e4 3, e4 2 + 2 • e4 3, e4 0 + e4 1⟩

theorem f3_four_dim_triple (d : Fin 4 → ZMod 3) (hd : ∀ i, d i ≠ 0) :
    ∃ v1 v2 v3 : Fin 4 → ZMod 3,
      v1 ≠ 0 ∧ v2 ≠ 0 ∧ v3 ≠ 0 ∧
      (∑ i, d i * (v1 i) ^ 2 = 1) ∧
      (∑ i, d i * (v2 i) ^ 2 = 1) ∧
      (∑ i, d i * (v3 i) ^ 2 = 1) ∧
      (∑ i, d i * v1 i * v2 i = 0) ∧
      (∑ i, d i * v1 i * v3 i = 0) ∧
      (∑ i, d i * v2 i * v3 i = 0) := by
  have hcheck : ∀ d : Fin 4 → ZMod 3, (∀ i, d i ≠ 0) →
      (f3Triple d).v1 ≠ 0 ∧ (f3Triple d).v2 ≠ 0 ∧ (f3Triple d).v3 ≠ 0 ∧
      (∑ i, d i * ((f3Triple d).v1 i) ^ 2 = 1) ∧
      (∑ i, d i * ((f3Triple d).v2 i) ^ 2 = 1) ∧
      (∑ i, d i * ((f3Triple d).v3 i) ^ 2 = 1) ∧
      (∑ i, d i * (f3Triple d).v1 i * (f3Triple d).v2 i = 0) ∧
      (∑ i, d i * (f3Triple d).v1 i * (f3Triple d).v3 i = 0) ∧
      (∑ i, d i * (f3Triple d).v2 i * (f3Triple d).v3 i = 0) := by
    decide
  exact ⟨(f3Triple d).v1, (f3Triple d).v2, (f3Triple d).v3, hcheck d hd⟩

theorem f3_orthogonal_triple {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hm : 5 ≤ m) (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0) :
    ∃ v1 v2 v3 : Fin m → ZMod 3,
      f v1 v1 = 1 ∧ f v2 v2 = 1 ∧ f v3 v3 = 1 ∧
      f v1 v2 = 0 ∧ f v1 v3 = 0 ∧ f v2 v3 = 0 ∧
      v1 ≠ 0 ∧ v2 ≠ 0 ∧ v3 ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (K := ZMod 3) (V := Fin m → ZMod 3) (B := f) ⟨hsymm⟩
  have hfr : Module.finrank (ZMod 3) (Fin m → ZMod 3) = m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h4 : 4 ≤ Module.finrank (ZMod 3) (Fin m → ZMod 3) := by
    rw [hfr]
    omega
  let idx : Fin 4 → Fin (Module.finrank (ZMod 3) (Fin m → ZMod 3)) := Fin.castLE h4
  let d : Fin 4 → ZMod 3 := fun i => f (b (idx i)) (b (idx i))
  have hd : ∀ i, d i ≠ 0 := fun i =>
    hb.not_isOrtho_basis_self_of_separatingLeft (show f.SeparatingLeft from hnd) (idx i)
  obtain ⟨v1, v2, v3, _, _, _, h11, h22, h33, h12, h13, h23⟩ :=
    f3_four_dim_triple d hd
  have hsum : ∀ w z : Fin 4 → ZMod 3,
      f (∑ i, w i • b (idx i)) (∑ j, z j • b (idx j)) = ∑ i, d i * w i * z i := by
    intro w z
    simp only [map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
      simp only [d]
      ring
    · intro j _ hji
      have hji' : idx j ≠ idx i := fun h => hji (Fin.castLE_injective h4 h)
      rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hb hji']
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  let u1 : Fin m → ZMod 3 := ∑ i, v1 i • b (idx i)
  let u2 : Fin m → ZMod 3 := ∑ i, v2 i • b (idx i)
  let u3 : Fin m → ZMod 3 := ∑ i, v3 i • b (idx i)
  have hu1 : f u1 u1 = 1 := by
    show f (∑ i, v1 i • b (idx i)) (∑ i, v1 i • b (idx i)) = 1
    rw [hsum v1 v1]
    simpa [pow_two, mul_assoc] using h11
  have hu2 : f u2 u2 = 1 := by
    show f (∑ i, v2 i • b (idx i)) (∑ i, v2 i • b (idx i)) = 1
    rw [hsum v2 v2]
    simpa [pow_two, mul_assoc] using h22
  have hu3 : f u3 u3 = 1 := by
    show f (∑ i, v3 i • b (idx i)) (∑ i, v3 i • b (idx i)) = 1
    rw [hsum v3 v3]
    simpa [pow_two, mul_assoc] using h33
  have hu12 : f u1 u2 = 0 := by
    show f (∑ i, v1 i • b (idx i)) (∑ i, v2 i • b (idx i)) = 0
    rw [hsum v1 v2]
    exact h12
  have hu13 : f u1 u3 = 0 := by
    show f (∑ i, v1 i • b (idx i)) (∑ i, v3 i • b (idx i)) = 0
    rw [hsum v1 v3]
    exact h13
  have hu23 : f u2 u3 = 0 := by
    show f (∑ i, v2 i • b (idx i)) (∑ i, v3 i • b (idx i)) = 0
    rw [hsum v2 v3]
    exact h23
  exact ⟨u1, u2, u3, hu1, hu2, hu3, hu12, hu13, hu23,
    F3.ne_zero_of_norm_one hu1, F3.ne_zero_of_norm_one hu2, F3.ne_zero_of_norm_one hu3⟩

theorem width_two_false_of_f3_case {G : Type*} [Group G] {D : Set G} {m : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hm : 5 ≤ m) (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmodel : fischerCentralQuotientModel D
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    ¬ WidthLe D 2 := by
  classical
  obtain ⟨φ, hφ⟩ := (fischerCentralQuotientModel_iff (f := f) D).1 hmodel
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨v1, v2, v3, h11, h22, h33, h12, h13, h23, _, _, _⟩ :=
    f3_orthogonal_triple hm hsymm hnd
  let y1 : G := φ.symm (reflBar f v1)
  let y2 : G := φ.symm (reflBar f v2)
  let y3 : G := φ.symm (reflBar f v3)
  have hy1 : φ y1 = reflBar f v1 := by simp [y1]
  have hy2 : φ y2 = reflBar f v2 := by simp [y2]
  have hy3 : φ y3 = reflBar f v3 := by simp [y3]
  have hy1D : y1 ∈ D := by
    rw [hφ y1, hy1]
    exact reflBar_mem_D3 h11
  have hy2D : y2 ∈ D := by
    rw [hφ y2, hy2]
    exact reflBar_mem_D3 h22
  have hy3D : y3 ∈ D := by
    rw [hφ y3, hy3]
    exact reflBar_mem_D3 h33
  have hq_ne : ∀ {a b : Fin m → ZMod 3}, f a a = 1 → f b b = 1 → f a b = 0 →
      reflBar f a ≠ reflBar f b := by
    intro a b ha hb hab h
    rcases (reflBar_eq_reflBar_iff hf (by omega) ha hb).1 h with h' | h'
    · rw [h'] at hab
      rw [ha] at hab
      exact one_ne_zero hab
    · rw [h'] at hab
      rw [show f a (-a) = - f a a by simp, ha] at hab
      exact (by decide : (-1 : ZMod 3) ≠ 0) hab
  have hq12 : reflBar f v1 ≠ reflBar f v2 := hq_ne h11 h22 h12
  have hq13 : reflBar f v1 ≠ reflBar f v3 := hq_ne h11 h33 h13
  have hq23 : reflBar f v2 ≠ reflBar f v3 := hq_ne h22 h33 h23
  have hne12 : y1 ≠ y2 := by
    intro h
    apply hq12
    rw [← hy1, ← hy2, h]
  have hne13 : y1 ≠ y3 := by
    intro h
    apply hq13
    rw [← hy1, ← hy3, h]
  have hne23 : y2 ≠ y3 := by
    intro h
    apply hq23
    rw [← hy2, ← hy3, h]
  have hcomm12 : Commute y1 y2 := by
    have hq : Commute (reflBar f v1) (reflBar f v2) :=
      (commute_iff_eq _ _).2 ((reflBar_commute_iff hf (by omega) h11 h22).2 (Or.inl h12))
    simpa [y1, y2] using hq.map φ.symm
  have hcomm13 : Commute y1 y3 := by
    have hq : Commute (reflBar f v1) (reflBar f v3) :=
      (commute_iff_eq _ _).2 ((reflBar_commute_iff hf (by omega) h11 h33).2 (Or.inl h13))
    simpa [y1, y3] using hq.map φ.symm
  have hcomm23 : Commute y2 y3 := by
    have hq : Commute (reflBar f v2) (reflBar f v3) :=
      (commute_iff_eq _ _).2 ((reflBar_commute_iff hf (by omega) h22 h33).2 (Or.inl h23))
    simpa [y2, y3] using hq.map φ.symm
  intro hW
  rw [CFSG.OddTranspositions.widthLe_two_iff] at hW
  exact hW y1 hy1D y2 hy2D y3 hy3D hne12 hne13 hne23 ⟨hcomm12, hcomm13, hcomm23⟩

end CFSG.Fischer.Classification
