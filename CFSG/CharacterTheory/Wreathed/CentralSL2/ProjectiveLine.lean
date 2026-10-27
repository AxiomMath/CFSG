module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Counting

variable {F : Type} [Field F]

@[expose] noncomputable def sqrtCount (D : F) : ℕ := Nat.card {s : F // s ^ 2 = D}

theorem sqrtCount_eq [Finite F] (h2 : (2 : F) ≠ 0) (D : F) :
    sqrtCount D = if D = 0 then 1 else if IsSquare D then 2 else 0 := by
  have : Fintype F := Fintype.ofFinite F
  unfold sqrtCount
  by_cases hD : D = 0
  · rw [ite_eq_left hD]
    subst hD
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨0, by ring⟩⟩⟩
    rw [pow_eq_zero_iff two_ne_zero |>.mp x.2, pow_eq_zero_iff two_ne_zero |>.mp y.2]
  · rw [ite_eq_right hD]
    by_cases hsq : IsSquare D
    · rw [ite_eq_left hsq]
      obtain ⟨c, rfl⟩ := hsq
      have hc : c ≠ 0 := by rintro rfl; exact hD (mul_zero 0)
      have hcne : c ≠ -c := by
        intro h
        apply hc
        have : (2 : F) * c = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_left h2
      have heq : {s : F // s ^ 2 = c * c} = {s : F // s ∈ ({c, -c} : Finset F)} := by
        congr 1
        funext s
        rw [Finset.mem_insert, Finset.mem_singleton, eq_iff_iff]
        constructor
        · intro hs
          have : (s - c) * (s + c) = 0 := by linear_combination hs
          rcases mul_eq_zero.mp this with h | h
          · left; linear_combination h
          · right; linear_combination h
        · rintro (rfl | rfl) <;> ring
      rw [heq, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_pair hcne]
    · rw [ite_eq_right hsq]
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun ⟨s, hs⟩ => hsq ⟨s, by rw [← hs, sq]⟩⟩

theorem card_quadratic_roots [Finite F] (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (b c : F) :
    Nat.card {y : F // a * (y * y) + b * y + c = 0} = sqrtCount (discrim a b c) := by
  have : NeZero (2 : F) := ⟨h2⟩
  unfold sqrtCount
  have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
  let e : F ≃ F :=
    { toFun := fun y => 2 * a * y + b
      invFun := fun s => (s - b) / (2 * a)
      left_inv := fun y => by field_simp; ring
      right_inv := fun s => by field_simp; ring }
  refine Nat.card_congr (e.subtypeEquiv fun y => ?_)
  rw [quadratic_eq_zero_iff_discrim_eq_sq ha]
  exact eq_comm

omit [Field F] in
theorem card_fixed_option [Finite F] (f : Equiv.Perm (Omega F)) :
    Nat.card {x // f x = x} =
      (if f none = none then 1 else 0) + Nat.card {y : F // f (some y) = some y} := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fintype.sum_option]

end Counting

section Moebius

variable {F : Type} [Field F]

theorem coordinateGLAction_none_eq_none_iff (C : GeneralLinearGroup (Fin 2) F) :
    coordinateGLAction F C none = none ↔ C.val 1 0 = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [coordinateGLAction_infinity F C hc] at h
    exact Option.some_ne_none _ h
  · exact coordinateGLAction_infinity_lower_left_zero F C

theorem coordinateGLAction_some_eq_some_iff (C : GeneralLinearGroup (Fin 2) F) (y : F) :
    coordinateGLAction F C (some y) = some y ↔
      C.val 1 0 * (y * y) + (C.val 1 1 - C.val 0 0) * y + -C.val 0 1 = 0 := by
  by_cases hd : C.val 1 0 * y + C.val 1 1 = 0
  · rw [coordinateGLAction_finite_denominator_zero F C y hd]
    simp only [reduceCtorEq, false_iff]
    intro hq
    have hdet := C.det_ne_zero
    rw [det_fin_two] at hdet
    apply hdet
    have h11 : C.val 1 1 = -(C.val 1 0 * y) := by linear_combination hd
    have h01 : C.val 0 1 = -(C.val 0 0 * y) := by
      linear_combination -hq + y * hd
    rw [h11, h01]
    ring
  · rw [coordinateGLAction_finite F C y hd, Option.some.injEq, div_eq_iff hd]
    constructor
    · intro h
      linear_combination -h
    · intro h
      linear_combination -h

theorem card_fixed_coordinateGLAction [Finite F] (h2 : (2 : F) ≠ 0)
    (C : GeneralLinearGroup (Fin 2) F)
    (hC : ¬ ∃ c : Fˣ, C = GeneralLinearGroup.scalar (Fin 2) c) :
    Nat.card {x // coordinateGLAction F C x = x} =
      sqrtCount (Matrix.trace C.val ^ 2 - 4 * Matrix.det C.val) := by
  have hdisc : Matrix.trace C.val ^ 2 - 4 * Matrix.det C.val =
      discrim (C.val 1 0) (C.val 1 1 - C.val 0 0) (-C.val 0 1) := by
    rw [discrim, trace_fin_two, det_fin_two]
    ring
  rw [card_fixed_option, hdisc]
  simp_rw [coordinateGLAction_some_eq_some_iff]
  by_cases hc : C.val 1 0 = 0
  · rw [ite_eq_left ((coordinateGLAction_none_eq_none_iff C).mpr hc)]
    by_cases hd : C.val 1 1 = C.val 0 0
    ·
      have h01 : C.val 0 1 ≠ 0 := by
        intro h01
        apply hC
        have h00 : C.val 0 0 ≠ 0 := by
          intro h00
          have hdet := C.det_ne_zero
          rw [det_fin_two, hc, h01, h00] at hdet
          simp at hdet
        refine ⟨Units.mk0 (C.val 0 0) h00, Units.ext ?_⟩
        rw [GeneralLinearGroup.coe_scalar]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hc, h01, hd]
      have hempty : Nat.card {y : F // C.val 1 0 * (y * y) + (C.val 1 1 - C.val 0 0) * y +
          -C.val 0 1 = 0} = 0 := by
        rw [Nat.card_eq_zero]
        left
        refine ⟨fun ⟨y, hy⟩ => h01 ?_⟩
        rw [hc, hd] at hy
        linear_combination -hy
      rw [hempty, hc, hd, sqrtCount_eq h2]
      simp [discrim]
    ·
      have hne : C.val 1 1 - C.val 0 0 ≠ 0 := sub_ne_zero.mpr hd
      have hone : Nat.card {y : F // C.val 1 0 * (y * y) + (C.val 1 1 - C.val 0 0) * y +
          -C.val 0 1 = 0} = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => Subtype.ext ?_⟩,
          ⟨⟨C.val 0 1 / (C.val 1 1 - C.val 0 0), by rw [hc]; field_simp; ring⟩⟩⟩
        rw [hc] at hx hy
        have : (C.val 1 1 - C.val 0 0) * (x - y) = 0 := by linear_combination hx - hy
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
      rw [hone, sqrtCount_eq h2, hc]
      have hsq : IsSquare (discrim 0 (C.val 1 1 - C.val 0 0) (-C.val 0 1)) :=
        ⟨C.val 1 1 - C.val 0 0, by rw [discrim]; ring⟩
      have hnz : discrim 0 (C.val 1 1 - C.val 0 0) (-C.val 0 1) ≠ 0 := by
        rw [discrim]
        simpa [sq] using hne
      rw [ite_eq_right hnz, ite_eq_left hsq]
  · rw [ite_eq_right (fun h => hc ((coordinateGLAction_none_eq_none_iff C).mp h)), zero_add]
    exact card_quadratic_roots h2 hc _ _

end Moebius

end CFSG.Wreathed.CentralSL2
