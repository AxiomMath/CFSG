module

public import CFSG.Fischer.Classification.Symplectic.Stars
public import CFSG.GroupTheory.ThreeTranspositions.FormLinearAlgebra

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Fischer.Classification.Symplectic

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def HasOrthHypPairs (C : SympConfig V) : Prop :=
  ∃ d ∈ C.D, ∃ e ∈ C.D, ∃ u ∈ C.D, ∃ w ∈ C.D, C.b d e = 1 ∧ C.b u w = 1 ∧
    C.b d u = 0 ∧ C.b d w = 0 ∧ C.b e u = 0 ∧ C.b e w = 0

theorem hasOrthHypPairs_of_forall_ne_zero [FiniteDimensional (ZMod 2) V] (C : SympConfig V)
    (hD : ∀ v, v ∈ C.D ↔ v ≠ 0) (hpair : ∃ x ∈ C.D, ∃ y ∈ C.D, x ≠ y ∧ C.b x y = 0) :
    HasOrthHypPairs C := by
  obtain ⟨x, hx, y, hy, hxy, hxy0⟩ := hpair
  have hx0 : x ≠ 0 := C.ne_zero_of_mem hx
  have hy0 : y ≠ 0 := C.ne_zero_of_mem hy
  obtain ⟨e, hxe, hye⟩ :=
    exists_form_eq_pair C.b C.comm C.nondeg hx0 hy0 hxy 1 0
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero] at hxe
    exact zero_ne_one hxe
  have heD : e ∈ C.D := (hD e).2 he0
  obtain ⟨w₀, hyw₀, hxw₀⟩ :=
    exists_form_eq_pair C.b C.comm C.nondeg hy0 hx0 (Ne.symm hxy) 1 0
  have hey : C.b e y = 0 := by rw [C.comm]; exact hye
  rcases C.b_cases e w₀ with h | h
  · refine ⟨x, hx, e, heD, y, hy, w₀, ?_, hxe, hyw₀, hxy0, hxw₀, hey, h⟩
    rw [hD]
    intro hw
    rw [hw, map_zero] at hyw₀
    exact zero_ne_one hyw₀
  · have hxw : C.b x (w₀ + x) = 0 := by
      rw [C.b_add_right, hxw₀, C.self_eq_zero, add_zero]
    have hew : C.b e (w₀ + x) = 0 := by
      rw [C.b_add_right, h, C.comm e x, hxe, zmod_two_one_add_one]
    have hyw : C.b y (w₀ + x) = 1 := by
      rw [C.b_add_right, hyw₀, C.comm y x, hxy0, add_zero]
    refine ⟨x, hx, e, heD, y, hy, w₀ + x, ?_, hxe, hyw, hxy0, hxw, hey, hew⟩
    rw [hD]
    intro hw
    rw [hw, map_zero] at hyw
    exact zero_ne_one hyw

private lemma exists_triple_of_not_tN (C : SympConfig V) (hTN : ¬ C.TN) :
    ∃ x ∈ C.D, ∃ y ∈ C.D, ∃ z ∈ C.D, x ≠ y ∧ C.b x y = 0 ∧ C.b z x = 0 ∧
      C.b z y = 0 ∧ z ≠ x ∧ z ≠ y ∧ x + y + z ∈ C.D := by
  unfold SympConfig.TN at hTN
  obtain ⟨x, hx⟩ := Classical.not_forall.mp hTN
  obtain ⟨hxD, hx⟩ := Classical.not_imp.mp hx
  obtain ⟨y, hy⟩ := Classical.not_forall.mp hx
  obtain ⟨hyD, hy⟩ := Classical.not_imp.mp hy
  obtain ⟨z, hz⟩ := Classical.not_forall.mp hy
  obtain ⟨hzD, hz⟩ := Classical.not_imp.mp hz
  obtain ⟨hxy, hz⟩ := Classical.not_imp.mp hz
  obtain ⟨hbxy, hz⟩ := Classical.not_imp.mp hz
  obtain ⟨hbzx, hz⟩ := Classical.not_imp.mp hz
  obtain ⟨hbzy, hz⟩ := Classical.not_imp.mp hz
  obtain ⟨hzx, hz⟩ := Classical.not_imp.mp hz
  obtain ⟨hzy, hz⟩ := Classical.not_imp.mp hz
  exact ⟨x, hxD, y, hyD, z, hzD, hxy, hbxy, hbzx, hbzy, hzx, hzy,
    Classical.not_not.mp hz⟩

theorem hasOrthHypPairs_of_quadraticForm [FiniteDimensional (ZMod 2) V] (C : SympConfig V)
    (Q : QuadraticForm (ZMod 2) V) (hpol : ∀ u v, QuadraticMap.polar Q u v = C.b u v)
    (hQ : ∀ v, v ∈ C.D ↔ Q v = 1) (hTN : ¬ C.TN) : HasOrthHypPairs C := by
  obtain ⟨x, hx, y, hy, z, hz, hxy, hbxy, hbzx, hbzy, hzx, hzy, hsumD⟩ :=
    exists_triple_of_not_tN C hTN
  have hx0 : x ≠ 0 := C.ne_zero_of_mem hx
  have hy0 : y ≠ 0 := C.ne_zero_of_mem hy
  have hz0 : z ≠ 0 := C.ne_zero_of_mem hz
  have hxz : x ≠ z := Ne.symm hzx
  have hyz : y ≠ z := Ne.symm hzy
  have hs0 : x + y + z ≠ 0 := C.ne_zero_of_mem hsumD
  have hQx : Q x = 1 := (hQ x).1 hx
  have hQy : Q y = 1 := (hQ y).1 hy
  have hQz : Q z = 1 := (hQ z).1 hz
  have hbxz : C.b x z = 0 := by rw [C.comm]; exact hbzx
  have hbyz : C.b y z = 0 := by rw [C.comm]; exact hbzy
  have hP : ∀ u v : V, Q (u + v) = Q u + Q v + C.b u v := by
    intro u v
    simpa only [hpol] using QuadraticMap.map_add Q u v
  obtain ⟨e₀, hxe₀, hye₀, hze₀⟩ :=
    exists_form_eq_triple C.b C.comm C.nondeg hx0 hy0 hz0 hxy hxz hyz hs0 1 0 0
  have hbe₀y : C.b e₀ y = 0 := by rw [C.comm]; exact hye₀
  have hex : ∃ e ∈ C.D, C.b x e = 1 ∧ C.b y e = 0 ∧ C.b z e = 0 := by
    rcases zmod_two_cases (Q e₀) with hQe | hQe
    · refine ⟨e₀ + y, (hQ (e₀ + y)).2 ?_, ?_, ?_, ?_⟩
      · rw [hP e₀ y, hQe, hQy, hbe₀y]
        norm_num
      · rw [C.b_add_right, hxe₀, hbxy, add_zero]
      · rw [C.b_add_right, hye₀, C.self_eq_zero, add_zero]
      · rw [C.b_add_right, hze₀, hbzy, add_zero]
    · exact ⟨e₀, (hQ e₀).2 hQe, hxe₀, hye₀, hze₀⟩
  obtain ⟨e, heD, hxe, hye, hze⟩ := hex
  have hey : C.b e y = 0 := by rw [C.comm]; exact hye
  have hez : C.b e z = 0 := by rw [C.comm]; exact hze
  have hex' : C.b e x = 1 := by rw [C.comm]; exact hxe
  have hs' : y + x + z ≠ 0 := by
    rw [show y + x + z = x + y + z by zmod_two_abel]
    exact hs0
  obtain ⟨w₀, hyw₀, hxw₀, hzw₀⟩ :=
    exists_form_eq_triple C.b C.comm C.nondeg hy0 hx0 hz0 (Ne.symm hxy) (Ne.symm hzy) hxz hs' 1 0 0
  have hwx : ∃ w₁ : V, C.b e w₁ = 0 ∧ C.b x w₁ = 0 ∧ C.b y w₁ = 1 ∧ C.b z w₁ = 0 := by
    rcases C.b_cases e w₀ with h | h
    · exact ⟨w₀, h, hxw₀, hyw₀, hzw₀⟩
    · refine ⟨w₀ + x, ?_, ?_, ?_, ?_⟩
      · rw [C.b_add_right, h, hex', zmod_two_one_add_one]
      · rw [C.b_add_right, hxw₀, C.self_eq_zero, add_zero]
      · rw [C.b_add_right, hyw₀, C.comm y x, hbxy, add_zero]
      · rw [C.b_add_right, hzw₀, hbzx, add_zero]
  obtain ⟨w₁, hew₁, hxw₁, hyw₁, hzw₁⟩ := hwx
  have hwz : C.b w₁ z = 0 := by rw [C.comm]; exact hzw₁
  have hwy : ∃ w ∈ C.D, C.b x w = 0 ∧ C.b e w = 0 ∧ C.b y w = 1 := by
    rcases zmod_two_cases (Q w₁) with hQw | hQw
    · refine ⟨w₁ + z, (hQ (w₁ + z)).2 ?_, ?_, ?_, ?_⟩
      · rw [hP w₁ z, hQw, hQz, hwz]
        norm_num
      · rw [C.b_add_right, hxw₁, hbxz, add_zero]
      · rw [C.b_add_right, hew₁, hez, add_zero]
      · rw [C.b_add_right, hyw₁, hbyz, add_zero]
    · exact ⟨w₁, (hQ w₁).2 hQw, hxw₁, hew₁, hyw₁⟩
  obtain ⟨w, hwD, hxw, hew, hyw⟩ := hwy
  exact ⟨x, hx, e, heD, y, hy, w, hwD, hxe, hyw, hbxy, hxw, hey, hew⟩

theorem tn_or_hasOrthHypPairs [FiniteDimensional (ZMod 2) V] (C : SympConfig V) :
    C.TN ∨ HasOrthHypPairs C := by
  rcases C.trichotomy with ⟨hD, hpair⟩ | ⟨⟨Q, hpol, hQ⟩, -⟩ | hTN
  · exact Or.inr (hasOrthHypPairs_of_forall_ne_zero C hD hpair)
  · by_cases hT : C.TN
    · exact Or.inl hT
    · exact Or.inr (hasOrthHypPairs_of_quadraticForm C Q hpol hQ hT)
  · exact Or.inl hTN

end CFSG.GroupTheory.ThreeTranspositions
