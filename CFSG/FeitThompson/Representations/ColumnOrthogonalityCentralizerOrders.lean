module

import CFSG.FeitThompson.Representations.IrreducibleCharactersOrthonormalBasis
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

noncomputable section

variable {G : Type*} [Group G]

private def classIndicator (y : G) : classFun G :=
  ⟨Set.indicator {g : G | IsConj g y} 1, mem_classFun.2 fun a b hab => by
    by_cases h : IsConj a y
    · rw [Set.indicator_of_mem (show a ∈ {g : G | IsConj g y} from h),
        Set.indicator_of_mem (show b ∈ {g : G | IsConj g y} from hab.symm.trans h)]
      rfl
    · rw [Set.indicator_of_notMem (show a ∉ {g : G | IsConj g y} from h),
        Set.indicator_of_notMem (show b ∉ {g : G | IsConj g y} from fun h' => h (hab.trans h'))]⟩

private theorem coe_classIndicator_of_isConj {y g : G} (h : IsConj g y) :
    ((classIndicator y : classFun G) : G → ℂ) g = 1 :=
  Set.indicator_of_mem (show g ∈ {a : G | IsConj a y} from h) 1

private theorem coe_classIndicator_of_not_isConj {y g : G} (h : ¬ IsConj g y) :
    ((classIndicator y : classFun G) : G → ℂ) g = 0 :=
  Set.indicator_of_notMem (show g ∉ {a : G | IsConj a y} from h) 1

private theorem cfInner_classIndicator [Fintype G] (y : G) {χ : G → ℂ} (hχ : χ ∈ classFun G) :
    cfInner ((classIndicator y : classFun G) : G → ℂ) χ
      = (Nat.card G : ℂ)⁻¹ * (Nat.card {g : G | IsConj g y} * (starRingEnd ℂ) (χ y)) := by
  classical
  rw [cfInner_def]
  congr 1
  have h1 : ∀ g : G, ((classIndicator y : classFun G) : G → ℂ) g * (starRingEnd ℂ) (χ g)
      = if IsConj g y then (starRingEnd ℂ) (χ y) else 0 := by
    intro g
    by_cases h : IsConj g y
    · rw [coe_classIndicator_of_isConj h, one_mul, if_pos h, classFun.apply_eq_of_isConj hχ h]
    · rw [coe_classIndicator_of_not_isConj h, zero_mul, if_neg h]
  have hc : (Finset.univ.filter fun g : G => IsConj g y).card
      = Nat.card {g : G | IsConj g y} := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_ofPred]
  rw [Finset.sum_congr rfl fun g _ => h1 g, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    hc]

theorem natCard_centralizer_eq_of_isConj [Finite G] {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G))
      = Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  have hset : {g : G | IsConj g x} = {g : G | IsConj g y} := by
    ext g; exact ⟨fun hg => hg.trans h, fun hg => hg.trans h.symm⟩
  have h1 := card_setOf_isConj_mul_card_centralizer x
  have h2 := card_setOf_isConj_mul_card_centralizer y
  rw [hset] at h1
  have : Nonempty {g : G | IsConj g y} := ⟨⟨y, IsConj.refl y⟩⟩
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

theorem sum_Irr_mul_conj_eq_ite [Finite G] [Fintype (Irr G)] (x y : G)
    [Decidable (IsConj x y)] :
    ∑ χ : Irr G, ((χ : Irr G) : G → ℂ) x * (starRingEnd ℂ) (((χ : Irr G) : G → ℂ) y)
      = if IsConj x y then (Nat.card (Subgroup.centralizer ({x} : Set G)) : ℂ) else 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set c : ℕ := Nat.card {g : G | IsConj g y} with hcdef
  set z : ℕ := Nat.card (Subgroup.centralizer ({y} : Set G)) with hzdef
  have hczG : c * z = Nat.card G := card_setOf_isConj_mul_card_centralizer y
  have hnat : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hcz : c ≠ 0 ∧ z ≠ 0 := by
    rw [← Nat.mul_ne_zero_iff, hczG]; exact hnat
  have hc0 : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hcz.1
  have hz0 : (z : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hcz.2
  have hfx := congrFun (classFun.coe_eq_sum_cfInner_smul (classIndicator y)) x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hfx
  have hfx2 : ((classIndicator y : classFun G) : G → ℂ)  x
      = (Nat.card G : ℂ)⁻¹ * c *
        ∑ χ : Irr G, (((χ : Irr G) : G → ℂ) x * (starRingEnd ℂ) (((χ : Irr G) : G → ℂ) y)) := by
    rw [hfx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [cfInner_classIndicator y (Irr_subset_classFun χ.2)]
    ring
  have hGcz : (Nat.card G : ℂ) = (c : ℂ) * z := by exact_mod_cast hczG.symm
  have hkey : ∑ χ : Irr G, (((χ : Irr G) : G → ℂ) x * (starRingEnd ℂ) (((χ : Irr G) : G → ℂ) y))
      = z * ((classIndicator y : classFun G) : G → ℂ) x := by
    rw [hfx2, hGcz]
    field_simp
  by_cases h : IsConj x y
  · rw [if_pos h, hkey, coe_classIndicator_of_isConj h, mul_one, hzdef,
      ← natCard_centralizer_eq_of_isConj h]
  · rw [if_neg h, hkey, coe_classIndicator_of_not_isConj h, mul_zero]

theorem sum_Irr_mul_conj_of_not_isConj [Finite G] [Fintype (Irr G)] {x y : G}
    (h : ¬ IsConj x y) :
    ∑ χ : Irr G, ((χ : Irr G) : G → ℂ) x * (starRingEnd ℂ) (((χ : Irr G) : G → ℂ) y) = 0 := by
  classical
  rw [sum_Irr_mul_conj_eq_ite x y, if_neg h]

theorem sum_Irr_mul_conj_of_isConj [Finite G] [Fintype (Irr G)] {x y : G} (h : IsConj x y) :
    ∑ χ : Irr G, ((χ : Irr G) : G → ℂ) x * (starRingEnd ℂ) (((χ : Irr G) : G → ℂ) y)
      = (Nat.card (Subgroup.centralizer ({x} : Set G)) : ℂ) := by
  classical
  rw [sum_Irr_mul_conj_eq_ite x y, if_pos h]

theorem sum_Irr_normSq_eq_natCard_centralizer [Finite G] [Fintype (Irr G)] (x : G) :
    ∑ χ : Irr G, ‖((χ : Irr G) : G → ℂ) x‖ ^ 2
      = (Nat.card (Subgroup.centralizer ({x} : Set G)) : ℝ) := by
  classical
  have h := sum_Irr_mul_conj_of_isConj (IsConj.refl x)
  have h2 : ∑ χ : Irr G, ((‖((χ : Irr G) : G → ℂ) x‖ ^ 2 : ℝ) : ℂ)
      = ((Nat.card (Subgroup.centralizer ({x} : Set G)) : ℝ) : ℂ) := by
    push_cast
    rw [← h]
    exact Finset.sum_congr rfl fun χ _ => by rw [Complex.mul_conj']
  rw [← Complex.ofReal_inj]
  push_cast
  simpa using h2

end

end CFSG.FeitThompson
