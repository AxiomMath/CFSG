module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndConj
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2F4

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaEnd

@[expose] def uMat (a b c : F4) : M3 := !![1, a, b; 0, 1, c; 0, 0, 1]

theorem det_uMat (a b c : F4) : (uMat a b c).det = 1 := by
  simp [uMat, Matrix.det_fin_three]

@[expose] def uEl (a b c : F4) : SL3 := ⟨uMat a b c, det_uMat a b c⟩

theorem coe_uEl (a b c : F4) : ((uEl a b c : SL3) : M3) = uMat a b c := rfl

theorem uEl_mul (a b c a' b' c' : F4) :
    uEl a b c * uEl a' b' c' = uEl (a + a') (b' + a * c' + b) (c + c') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uEl, coe_uEl, coe_uEl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uEl_zero : uEl 0 0 0 = 1 := by
  apply Subtype.ext
  rw [coe_uEl, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem add_self_F4 (x : F4) : x + x = 0 := CharTwo.add_self_eq_zero x

theorem uEl_mul_inv (a b c : F4) : uEl a b c * uEl a (a * c + b) c = 1 := by
  rw [uEl_mul, add_self_F4, add_self_F4, ← uEl_zero]
  congr 1
  calc a * c + b + a * c + b = (a * c + a * c) + (b + b) := by ring
    _ = 0 := by rw [add_self_F4, add_self_F4, add_zero]

theorem uEl_inj {a b c a' b' c' : F4} (h : uEl a b c = uEl a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg (fun g : SL3 => (g : M3)) h
  simp only [coe_uEl] at h'
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun (congrFun h' 0) 1; simpa [uMat] using this
  · have := congrFun (congrFun h' 0) 2; simpa [uMat] using this
  · have := congrFun (congrFun h' 1) 2; simpa [uMat] using this

@[expose] def U3 : Subgroup SL3 where
  carrier := Set.range fun p : F4 × F4 × F4 => uEl p.1 p.2.1 p.2.2
  mul_mem' := by
    rintro _ _ ⟨⟨a, b, c⟩, rfl⟩ ⟨⟨a', b', c'⟩, rfl⟩
    exact ⟨⟨a + a', b' + a * c' + b, c + c'⟩, (uEl_mul a b c a' b' c').symm⟩
  one_mem' := ⟨⟨0, 0, 0⟩, uEl_zero⟩
  inv_mem' := by
    rintro _ ⟨⟨a, b, c⟩, rfl⟩
    refine ⟨⟨a, a * c + b, c⟩, ?_⟩
    exact eq_inv_of_mul_eq_one_right (uEl_mul_inv a b c)

theorem mem_U3 {g : SL3} : g ∈ U3 ↔ ∃ a b c, uEl a b c = g := by
  constructor
  · rintro ⟨⟨a, b, c⟩, rfl⟩; exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c, rfl⟩; exact ⟨⟨a, b, c⟩, rfl⟩

theorem card_U3 : Nat.card U3 = 2 ^ 6 := by
  have hb : Function.Bijective
      (fun p : F4 × F4 × F4 => (⟨uEl p.1 p.2.1 p.2.2, ⟨p, rfl⟩⟩ : U3)) := by
    refine ⟨fun p q hpq => ?_, fun ⟨g, hg⟩ => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := uEl_inj (congrArg Subtype.val hpq)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨p, rfl⟩ := hg
      exact ⟨p, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card, F4.card]
  norm_num

theorem uEl_sq (a b c : F4) : uEl a b c * uEl a b c = uEl 0 (a * c) 0 := by
  rw [uEl_mul, add_self_F4, add_self_F4]
  congr 1
  calc b + a * c + b = a * c + (b + b) := by ring
    _ = a * c := by rw [add_self_F4, add_zero]

theorem pow_four_of_mem_U3 {g : SL3} (hg : g ∈ U3) : g ^ 4 = 1 := by
  obtain ⟨a, b, c, rfl⟩ := mem_U3.mp hg
  have e : uEl a b c ^ 4 = (uEl a b c * uEl a b c) * (uEl a b c * uEl a b c) := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, sq, sq]
  rw [e, uEl_sq, uEl_mul, add_self_F4, mul_zero, add_zero, add_self_F4, uEl_zero]

@[expose] def s01Mat : M3 := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem det_s01Mat : s01Mat.det = 1 := by
  simp [s01Mat, Matrix.det_fin_three]
  exact CharTwo.neg_eq 1

@[expose] def s01 : SL3 := ⟨s01Mat, det_s01Mat⟩

theorem s01_mul_self : s01 * s01 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s01, s01Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s01_inv : s01⁻¹ = s01 := inv_eq_of_mul_eq_one_right s01_mul_self

theorem coe_s01_conj (a b c : F4) :
    ((s01 * uEl a b c * s01⁻¹ : SL3) : M3) = !![1, 0, c; a, 1, b; 0, 0, 1] := by
  rw [s01_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uEl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s01, s01Mat, uMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s01_conj_zero (b c : F4) : s01 * uEl 0 b c * s01⁻¹ = uEl 0 c b := by
  apply Subtype.ext
  rw [coe_s01_conj, coe_uEl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem mem_inf_s01 {g : SL3} : g ∈ U3 ⊓ conjR U3 s01 ↔ ∃ b c, uEl 0 b c = g := by
  constructor
  · intro hg
    obtain ⟨hg, hg'⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨a, b, c, rfl⟩ := mem_U3.mp hg
    rw [mem_conjR] at hg'
    obtain ⟨a', b', c', h⟩ := mem_U3.mp hg'
    have h' := congrArg (fun g : SL3 => (g : M3) 1 0) h
    simp only [coe_s01_conj, coe_uEl] at h'
    have ha : a = 0 := by simpa [uMat] using h'.symm
    exact ⟨b, c, by rw [ha]⟩
  · rintro ⟨b, c, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨mem_U3.mpr ⟨0, b, c, rfl⟩, ?_⟩
    rw [mem_conjR, s01_conj_zero]
    exact mem_U3.mpr ⟨0, c, b, rfl⟩

theorem card_U3_inf_s01 : Nat.card (U3 ⊓ conjR U3 s01 : Subgroup SL3) = 2 ^ 4 := by
  have hb : Function.Bijective (fun p : F4 × F4 =>
      (⟨uEl 0 p.1 p.2, mem_inf_s01.mpr ⟨p.1, p.2, rfl⟩⟩ : (U3 ⊓ conjR U3 s01 : Subgroup SL3))) := by
    refine ⟨fun p q hpq => ?_, fun ⟨g, hg⟩ => ?_⟩
    · obtain ⟨-, h2, h3⟩ := uEl_inj (congrArg Subtype.val hpq)
      exact Prod.ext h2 h3
    · obtain ⟨b, c, rfl⟩ := mem_inf_s01.mp hg
      exact ⟨⟨b, c⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_prod, Nat.card_eq_fintype_card, F4.card]
  norm_num

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
