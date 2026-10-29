module

public import CFSG.GH74.QTGen4.Recog.Ku.A6ModelB
public import CFSG.GH74.QTGen4.Recog.Ku.A6Model
public import CFSG.Quasithin.Recognition.HSType15a

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku.A6

open CFSG.Quasithin.HSType

variable {A : Type} [CommGroup A]

@[expose] def sympGram : Fin 4 → Fin 4 → ZMod 2 :=
  ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]]

theorem zmod2_zero_add_comm : ∀ a b : ZMod 2, 0 = (0 + a) + (b + 0) → a = b := by decide

theorem IsPolarForm.symm' {ω : A → A → ZMod 2} (hω : IsPolarForm ω) (x y : A) :
    ω x y = ω y x := by
  have h1 := hω.mul_left x y (x * y)
  have h2 := hω.mul_right x x y
  have h3 := hω.mul_right y x y
  rw [hω.alt, h2, h3, hω.alt x, hω.alt y] at h1
  exact zmod2_zero_add_comm _ _ h1

theorem zp_zero (b : A) : zp b 0 = 1 := by
  unfold zp
  exact if_neg (by decide)

theorem zp_one (b : A) : zp b 1 = b := by
  unfold zp
  exact if_pos rfl

theorem zp_form {ω : A → A → ZMod 2} (hω : IsPolarForm ω) (b c : A) (s t : ZMod 2) :
    ω (zp b s) (zp c t) = s * t * ω b c := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl <;>
    simp [zp_zero, zp_one, hω.one_left, hω.one_right]

theorem coordMap_gram {ω : A → A → ZMod 2} (hω : IsPolarForm ω) {b : Fin 4 → A}
    (hG : ∀ i j, ω (b i) (b j) = sympGram i j) (u v : SpV) :
    ω (coordMap b u) (coordMap b v) = spForm u v := by
  simp only [coordMap, hω.mul_left, hω.mul_right, zp_form hω, hG]
  simp [sympGram, spForm]

theorem zmod2_eq_zero_of_ne_one : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
theorem zmod2_eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
theorem zmod2_add_eq_zero_iff : ∀ a c : ZMod 2, a + c = 0 → a = c := by decide
theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide
theorem zmod2_add_self_zero : ∀ a : ZMod 2, a + a = 0 := by decide

theorem exists_form_one {ω : A → A → ZMod 2} (hnd : ∀ x : A, (∀ w, ω x w = 0) → x = 1)
    {z : A} (hz : z ≠ 1) : ∃ x, ω z x = 1 := by
  by_contra h
  push Not at h
  exact hz (hnd z fun w => zmod2_eq_zero_of_ne_one _ (h w))

theorem exists_form_on_kernel {ω : A → A → ZMod 2} (hω : IsPolarForm ω)
    (hsq : ∀ x : A, x * x = 1) (hnd : ∀ x : A, (∀ w, ω x w = 0) → x = 1)
    {z z' : A} (hz1 : z ≠ 1) (hz'1 : z' ≠ 1) (hzz : z' ≠ z) :
    ∃ w, ω z w = 0 ∧ ω z' w = 1 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_form_one hnd hz1
  have hker : ∀ v, ω z v = 0 → ω z' v = 0 := fun v hv =>
    zmod2_eq_zero_of_ne_one _ (h v hv)
  have claim : ∀ v, ω z' v = ω z v * ω z' x := by
    intro v
    rcases zmod2_cases (ω z v) with h0 | h1
    · rw [h0, zero_mul]
      exact hker v h0
    · have hv' : ω z (v * x) = 0 := by
        rw [hω.mul_right z v x, h1, hx]
        exact zmod2_one_add_one
      have h3 := hker _ hv'
      rw [hω.mul_right z' v x] at h3
      rw [h1, one_mul]
      exact zmod2_add_eq_zero_iff _ _ h3
  rcases zmod2_cases (ω z' x) with hc | hc
  · apply hz'1
    apply hnd
    intro w
    rw [claim w, hc, mul_zero]
  · have hz'z : z' * z = 1 := by
      apply hnd
      intro w
      rw [hω.mul_left z' z w, claim w, hc, mul_one]
      exact zmod2_add_self_zero _
    apply hzz
    calc z' = z' * (z * z) := by rw [hsq z, mul_one]
      _ = z' * z * z := (mul_assoc _ _ _).symm
      _ = z := by rw [hz'z, one_mul]

theorem exists_pair {ω : A → A → ZMod 2} (hω : IsPolarForm ω)
    (hsq : ∀ x : A, x * x = 1) (hnd : ∀ x : A, (∀ w, ω x w = 0) → x = 1)
    {z z' : A} (hz1 : z ≠ 1) (hz'1 : z' ≠ 1) (hzz : z' ≠ z) (hzz' : ω z z' = 0) :
    ∃ b1 b2 : A, ω z b1 = 1 ∧ ω z' b1 = 0 ∧ ω z b2 = 0 ∧ ω z' b2 = 1 ∧ ω b1 b2 = 0 := by
  obtain ⟨x, hx⟩ := exists_form_one hnd hz1
  obtain ⟨w, hw0, hw1⟩ := exists_form_on_kernel hω hsq hnd hz1 hz'1 hzz
  obtain ⟨b1, hb1z, hb1z'⟩ : ∃ b1, ω z b1 = 1 ∧ ω z' b1 = 0 := by
    by_cases hc : ω z' x = 0
    · exact ⟨x, hx, hc⟩
    · refine ⟨x * w, ?_, ?_⟩
      · rw [hω.mul_right z x w, hx, hw0, add_zero]
      · rw [hω.mul_right z' x w, zmod2_eq_one_of_ne_zero _ hc, hw1]
        exact zmod2_one_add_one
  by_cases hb : ω b1 w = 0
  · exact ⟨b1, w, hb1z, hb1z', hw0, hw1, hb⟩
  · refine ⟨b1, w * z, hb1z, hb1z', ?_, ?_, ?_⟩
    · simp [hω.mul_right z w z, hw0, hω.alt]
    · rw [hω.mul_right z' w z, hw1, hω.symm' z' z, hzz', add_zero]
    · rw [hω.mul_right b1 w z, zmod2_eq_one_of_ne_zero _ hb, hω.symm' b1 z, hb1z]
      exact zmod2_one_add_one

theorem symp_basis {ω : A → A → ZMod 2} (hω : IsPolarForm ω)
    (hsq : ∀ x : A, x * x = 1) (hnd : ∀ x : A, (∀ w, ω x w = 0) → x = 1)
    {z z' : A} (hz1 : z ≠ 1) (hz'1 : z' ≠ 1) (hzz : z' ≠ z) (hzz' : ω z z' = 0) :
    ∃ b : Fin 4 → A, b 0 = z ∧ b 3 = z' ∧ ∀ i j, ω (b i) (b j) = sympGram i j := by
  obtain ⟨b1, b2, h1, h2, h3, h4, h5⟩ := exists_pair hω hsq hnd hz1 hz'1 hzz hzz'
  refine ⟨![z, b1, b2, z'], rfl, rfl, ?_⟩
  have s1 : ω b1 z = 1 := by rw [hω.symm']; exact h1
  have s2 : ω b2 z = 0 := by rw [hω.symm']; exact h3
  have s3 : ω b1 z' = 0 := by rw [hω.symm']; exact h2
  have s4 : ω b2 z' = 1 := by rw [hω.symm']; exact h4
  have s5 : ω b2 b1 = 0 := by rw [hω.symm']; exact h5
  have s6 : ω z' z = 0 := by rw [hω.symm']; exact hzz'
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sympGram, hω.alt, h1, h2, h3, h4, h5, hzz', s1, s2, s3, s4, s5, s6]

theorem coordMap_inj_of_gram {ω : A → A → ZMod 2} (hω : IsPolarForm ω) {b : Fin 4 → A}
    (hG : ∀ i j, ω (b i) (b j) = sympGram i j) : Function.Injective (coordMap b) := by
  intro u v h
  have hk : ∀ (u' : SpV) (k : Fin 4), ω (coordMap b u') (b k) = spForm u' (spE k) := by
    intro u' k
    rw [← coordMap_spE b k]
    exact coordMap_gram hω hG u' (spE k)
  have key : ∀ k, spForm (u + v) (spE k) = 0 := by
    intro k
    rw [spForm_add_left, ← hk u k, ← hk v k, h, zmod2_add_self_zero]
  have h0 : u + v = 0 := spForm_nondeg (u + v) key
  calc u = (u + v) + v := by rw [add_assoc, add_self_sp, add_zero]
    _ = 0 + v := by rw [h0]
    _ = v := zero_add v

theorem coordMap_bijective {ω : A → A → ZMod 2} (hω : IsPolarForm ω) (hcard : Nat.card A = 16)
    {b : Fin 4 → A} (hG : ∀ i j, ω (b i) (b j) = sympGram i j) :
    Function.Bijective (coordMap b) := by
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : Fintype A := Fintype.ofFinite A
  have hA : Fintype.card A = 16 := by rw [← Nat.card_eq_fintype_card, hcard]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨coordMap_inj_of_gram hω hG, ?_⟩
  rw [hA]
  simp

theorem coordMap_polar {ω : A → A → ZMod 2} (hω : IsPolarForm ω) {b : Fin 4 → A}
    (hG : ∀ i j, ω (b i) (b j) = sympGram i j) {z : A} (hb0 : b 0 = z) (W : Set A)
    (hW : ∀ x, x ∈ W ↔ ω z x = 0) (v : SpV) :
    coordMap b v ∈ W ↔ spForm (spE 0) v = 0 := by
  have h := coordMap_gram hω hG (spE 0) v
  rw [coordMap_spE, hb0] at h
  rw [hW, h]

theorem coordMap_v2 {ω : A → A → ZMod 2} (hω : IsPolarForm ω) {b : Fin 4 → A}
    (hG : ∀ i j, ω (b i) (b j) = sympGram i j) {z z' : A} (hb0 : b 0 = z) (hb3 : b 3 = z')
    (V2 : Set A) (hV : ∀ x, x ∈ V2 ↔ ∃ a c : ZMod 2, x = zp z a * zp z' c) (v : SpV) :
    coordMap b v ∈ V2 ↔ InV2m v := by
  have hinj := coordMap_inj_of_gram hω hG
  rw [hV]
  constructor
  · rintro ⟨a, c, hac⟩
    have hw : coordMap b ![a, 0, 0, c] = coordMap b v := by
      rw [hac]
      simp [coordMap, zp_zero, hb0, hb3]
    have hv := hinj hw
    rw [← hv]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨v 0, v 3, ?_⟩
    simp [coordMap, zp_zero, hb0, hb3, h1, h2]

theorem coordinates_of_polar {ω : A → A → ZMod 2} (hω : IsPolarForm ω)
    (hsq : ∀ x : A, x * x = 1) (hnd : ∀ x : A, (∀ w, ω x w = 0) → x = 1)
    (hcard : Nat.card A = 16) {z z' : A} (hz1 : z ≠ 1) (hz'1 : z' ≠ 1) (hzz : z' ≠ z)
    (hzz' : ω z z' = 0) (W V2 : Set A) (hW : ∀ x, x ∈ W ↔ ω z x = 0)
    (hV : ∀ x, x ∈ V2 ↔ ∃ a c : ZMod 2, x = zp z a * zp z' c) :
    ∃ b : Fin 4 → A, b 0 = z ∧ b 3 = z' ∧ (∀ i j, ω (b i) (b j) = sympGram i j) ∧
      Function.Bijective (coordMap b) ∧
      (∀ v, coordMap b v ∈ W ↔ spForm (spE 0) v = 0) ∧
      (∀ v, coordMap b v ∈ V2 ↔ InV2m v) := by
  obtain ⟨b, hb0, hb3, hG⟩ := symp_basis hω hsq hnd hz1 hz'1 hzz hzz'
  exact ⟨b, hb0, hb3, hG, coordMap_bijective hω hcard hG,
    fun v => coordMap_polar hω hG hb0 W hW v, fun v => coordMap_v2 hω hG hb0 hb3 V2 hV v⟩

end CFSG.GH74.QTGen4.Ku.A6

end
