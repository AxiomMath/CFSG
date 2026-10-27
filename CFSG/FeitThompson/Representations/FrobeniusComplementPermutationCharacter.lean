module

public import Mathlib.RepresentationTheory.Induced
public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues
import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
import CFSG.FeitThompson.Representations.InducedCharacterTraceFormula
import CFSG.FeitThompson.Local.FrobeniusKernelComplementPartition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate Pointwise

variable {Q : Type*} [Group Q] [Fintype Q] {U C : Subgroup Q}

noncomputable def frobeniusComplementChar (C : Subgroup Q) : Q → ℂ := indClassFun C 1

theorem frobeniusComplementChar_apply (C : Subgroup Q) (x : Q) :
    frobeniusComplementChar C x
      = (Nat.card C : ℂ)⁻¹ * (Nat.card {t : Q // t⁻¹ * x * t ∈ C} : ℂ) := by
  classical
  rw [frobeniusComplementChar, indClassFun_apply]
  congr 1
  simp only [Pi.one_apply, dite_eq_ite]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem frobeniusComplementChar_conj (C : Subgroup Q) (a x : Q) :
    frobeniusComplementChar C (a * x * a⁻¹) = frobeniusComplementChar C x :=
  indClassFun_conj C 1 a x

theorem frobeniusComplementChar_mem_classFun (C : Subgroup Q) :
    frobeniusComplementChar C ∈ classFun Q := by
  rw [mem_classFun]
  intro x y hxy
  obtain ⟨a, rfl⟩ := isConj_iff.mp hxy
  rw [frobeniusComplementChar_conj]

theorem frobeniusComplementChar_eq_character (C : Subgroup Q) :
    frobeniusComplementChar C
      = (Representation.ind C.subtype (Representation.trivial ℂ C ℂ)).character := by
  classical
  have hchar : (Representation.trivial ℂ C ℂ).character = 1 := by
    funext g
    have h : (Representation.trivial ℂ C ℂ) g = LinearMap.id := by ext; simp
    simp [Representation.character, h]
  rw [InducedCharacterConstruction.character_ind_eq_indClassFun, hchar, frobeniusComplementChar]
  funext x
  rw [indClassFun_apply, InducedCharacterConstruction.indClassFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : t⁻¹ * x * t ∈ C
  · rw [dif_pos h, ← InducedCharacterConstruction.subgroupExtend_coe C 1 ⟨_, h⟩]
  · rw [dif_neg h, InducedCharacterConstruction.subgroupExtend_of_notMem C 1 h]

theorem cfInner_frobeniusComplementChar_one (C : Subgroup Q) :
    cfInner (frobeniusComplementChar C) (1 : Q → ℂ) = 1 := by
  classical
  have _ : Fintype C := Fintype.ofFinite _
  rw [frobeniusComplementChar, cfInner_indClassFun C (1 : C → ℂ) (one_mem_classFun Q),
    cfInner_def]
  have h : ∀ s : C, (1 : C → ℂ) s * conj (resClassFun C (1 : Q → ℂ) s) = 1 := by
    intro s; rw [resClassFun_apply]; simp
  rw [Finset.sum_congr rfl fun s _ => h s]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')

section Frobenius

variable [U.Normal] (hUC : U.IsComplement' C)
  (hfree : ∀ c ∈ C, c ≠ 1 → U ⊓ Subgroup.centralizer {c} = ⊥)

noncomputable def conjAutOn (U C : Subgroup Q) [U.Normal] : C →* MulAut U :=
  (MulAut.conjNormal (H := U)).comp C.subtype

omit [Fintype Q] in
theorem conjAutOn_apply_coe [U.Normal] (c : C) (v : U) :
    ((conjAutOn U C c v : U) : Q) = (c : Q) * (v : Q) * (c : Q)⁻¹ :=
  MulAut.conjNormal_apply _ _

omit [Fintype Q] in
include hfree in
theorem fixedPointFree_conjAutOn (c : C) (hc : c ≠ 1) :
    MonoidHom.FixedPointFree (conjAutOn U C c : U → U) := by
  intro v hv
  have hvc : (v : Q) ∈ U ⊓ Subgroup.centralizer ({(c : Q)} : Set Q) := by
    refine Subgroup.mem_inf.2 ⟨v.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h : (c : Q) * (v : Q) * (c : Q)⁻¹ = (v : Q) := by
      rw [← conjAutOn_apply_coe c v, hv]
    calc (v : Q) * (c : Q) = ((c : Q) * (v : Q) * (c : Q)⁻¹) * (c : Q) := by rw [h]
      _ = (c : Q) * (v : Q) := by group
  rw [hfree (c : Q) c.2 (fun h => hc (Subtype.ext h))] at hvc
  exact Subtype.ext (by simpa using hvc)

include hfree in
theorem card_dvd_card_sub_one_of_frobenius : Nat.card C ∣ Nat.card U - 1 :=
  card_dvd_card_sub_one_of_fixedPointFree (φ := conjAutOn U C)
    fun c hc => fixedPointFree_conjAutOn hfree c hc

omit [Fintype Q] in
include hUC hfree in
theorem eq_one_of_mem_of_conj_mem {c v : Q} (hc : c ∈ C) (hc1 : c ≠ 1) (hv : v ∈ U)
    (hvc : v⁻¹ * c * v ∈ C) : v = 1 := by
  have hd : c⁻¹ * (v⁻¹ * c * v) ∈ U ⊓ C := by
    refine Subgroup.mem_inf.2 ⟨?_, C.mul_mem (C.inv_mem hc) hvc⟩
    rw [show c⁻¹ * (v⁻¹ * c * v) = (c⁻¹ * v⁻¹ * c) * v from by group]
    exact U.mul_mem (by simpa [mul_assoc] using ‹U.Normal›.conj_mem _ (U.inv_mem hv) c⁻¹) hv
  have hfix : v⁻¹ * c * v = c :=
    (inv_mul_eq_one.mp ((Subgroup.eq_bot_iff_forall _).mp hUC.disjoint.eq_bot _ hd)).symm
  have hcomm : v ∈ U ⊓ Subgroup.centralizer ({c} : Set Q) := by
    refine Subgroup.mem_inf.2 ⟨hv, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc v * c = v * (v⁻¹ * c * v) := by rw [hfix]
      _ = c * v := by group
  rw [hfree c hc hc1] at hcomm
  simpa using hcomm

omit [Fintype Q] in
include hUC hfree in
theorem mem_iff_conj_mem {c : Q} (hc : c ∈ C) (hc1 : c ≠ 1) (t : Q) :
    t⁻¹ * c * t ∈ C ↔ t ∈ C := by
  refine ⟨fun h => ?_, fun h => C.mul_mem (C.mul_mem (C.inv_mem h) hc) h⟩
  have hmem : t ∈ ((U : Set Q) * (C : Set Q) : Set Q) := by
    rw [← Subgroup.normal_mul U C, hUC.sup_eq_top]; trivial
  obtain ⟨v, hv, b, hb, rfl⟩ := Set.mem_mul.mp hmem
  have hv' : v ∈ U := hv
  have hb' : b ∈ C := hb
  have hvc : v⁻¹ * c * v ∈ C := by
    rw [show v⁻¹ * c * v = b * ((v * b)⁻¹ * c * (v * b)) * b⁻¹ from by group]
    exact C.mul_mem (C.mul_mem hb' h) (C.inv_mem hb')
  simpa [eq_one_of_mem_of_conj_mem hUC hfree hc hc1 hv' hvc] using hb'

include hUC in
theorem frobeniusComplementChar_one : frobeniusComplementChar C 1 = (Nat.card U : ℂ) := by
  have hC : (Nat.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [frobeniusComplementChar, indClassFun_one, Pi.one_apply, mul_one, ← hUC.card_mul_card]
  push_cast
  field_simp

include hUC in
theorem frobeniusComplementChar_eq_zero {x : Q} (hx : x ∈ U) (hx1 : x ≠ 1) :
    frobeniusComplementChar C x = 0 := by
  have hempty : IsEmpty {t : Q // t⁻¹ * x * t ∈ C} := by
    refine ⟨fun t => hx1 ?_⟩
    have h1 : (t : Q)⁻¹ * x * t ∈ U := by
      simpa [mul_assoc] using ‹U.Normal›.conj_mem _ hx (t : Q)⁻¹
    have h3 := Subgroup.disjoint_def.mp hUC.disjoint h1 t.2
    rw [show x = (t : Q) * ((t : Q)⁻¹ * x * t) * (t : Q)⁻¹ from by group, h3]
    group
  rw [frobeniusComplementChar_apply, Nat.card_eq_zero.2 (Or.inl hempty)]
  simp

include hUC hfree in
theorem frobeniusComplementChar_eq_one {c : Q} (hc : c ∈ C) (hc1 : c ≠ 1) :
    frobeniusComplementChar C c = 1 := by
  rw [frobeniusComplementChar_apply,
    Nat.card_congr (Equiv.subtypeEquivRight (mem_iff_conj_mem hUC hfree hc hc1))]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')

include hUC hfree in
theorem exists_conj_mem_of_notMem {x : Q} (hx : x ∉ U) :
    ∃ t : Q, ∃ c ∈ C, c ≠ 1 ∧ x = t⁻¹ * c * t := by
  obtain ⟨v, ⟨-, hxv⟩, -⟩ := existsUnique_mem_conj_inv_smul ‹U.Normal› hUC hfree hx
  have hmem : v * x * v⁻¹ ∈ C := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxv
    simpa using hxv
  refine ⟨v, v * x * v⁻¹, hmem, ?_, by group⟩
  intro h
  exact hx (by rw [show x = v⁻¹ * (v * x * v⁻¹) * v from by group, h]; simp)

include hUC hfree in
theorem frobeniusComplementChar_eq_one_of_notMem {x : Q} (hx : x ∉ U) :
    frobeniusComplementChar C x = 1 := by
  obtain ⟨t, c, hc, hc1, rfl⟩ := exists_conj_mem_of_notMem hUC hfree hx
  rw [show t⁻¹ * c * t = t⁻¹ * c * t⁻¹⁻¹ from by group, frobeniusComplementChar_conj]
  exact frobeniusComplementChar_eq_one hUC hfree hc hc1

include hUC hfree in
theorem frobeniusComplementChar_natCast_values (x : Q) :
    ∃ n : ℕ, frobeniusComplementChar C x = (n : ℂ) := by
  by_cases hx : x ∈ U
  · by_cases hx1 : x = 1
    · exact ⟨Nat.card U, by rw [hx1, frobeniusComplementChar_one hUC]⟩
    · exact ⟨0, by rw [frobeniusComplementChar_eq_zero hUC hx hx1]; simp⟩
  · exact ⟨1, by rw [frobeniusComplementChar_eq_one_of_notMem hUC hfree hx]; simp⟩

include hUC hfree in
theorem cfInner_frobeniusComplementChar_self :
    cfInner (frobeniusComplementChar C) (frobeniusComplementChar C)
      = 1 + ((Nat.card U : ℂ) - 1) / (Nat.card C : ℂ) := by
  classical
  have hum : Nat.card U * Nat.card C = Nat.card Q := hUC.card_mul_card
  have hu0 : ((Nat.card U : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hm0 : ((Nat.card C : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hval : ∀ x : Q, (‖frobeniusComplementChar C x‖ : ℂ) ^ 2
      = if x ∈ U then (if x = 1 then (Nat.card U : ℂ) ^ 2 else 0) else 1 := by
    intro x
    by_cases hx : x ∈ U
    · rw [if_pos hx]
      by_cases hx1 : x = 1
      · rw [if_pos hx1, hx1, frobeniusComplementChar_one hUC]; norm_num
      · rw [if_neg hx1, frobeniusComplementChar_eq_zero hUC hx hx1]; norm_num
    · rw [if_neg hx, frobeniusComplementChar_eq_one_of_notMem hUC hfree hx]; norm_num
  rw [cfInner_self_eq_sum_norm_sq, Finset.sum_congr rfl fun x _ => hval x,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Q => x ∈ U)]
  have hA : ∑ x ∈ Finset.univ.filter (fun x : Q => x ∈ U),
      (if x ∈ U then (if x = 1 then (Nat.card U : ℂ) ^ 2 else 0) else 1)
      = (Nat.card U : ℂ) ^ 2 := by
    rw [Finset.sum_congr rfl fun x hx => by rw [if_pos (Finset.mem_filter.mp hx).2],
      Finset.sum_ite_eq' (Finset.univ.filter (fun x : Q => x ∈ U)) (1 : Q)
        (fun _ => (Nat.card U : ℂ) ^ 2)]
    simp
  have hB : ∑ x ∈ Finset.univ.filter (fun x : Q => ¬ x ∈ U),
      (if x ∈ U then (if x = 1 then (Nat.card U : ℂ) ^ 2 else 0) else 1)
      = ((Finset.univ.filter (fun x : Q => ¬ x ∈ U)).card : ℂ) := by
    rw [Finset.sum_congr rfl fun x hx => by rw [if_neg (Finset.mem_filter.mp hx).2],
      Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hA, hB]
  have hcardU : (Finset.univ.filter (fun x : Q => x ∈ U)).card = Nat.card U := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcards : (Finset.univ.filter (fun x : Q => ¬ x ∈ U)).card
      = Nat.card U * Nat.card C - Nat.card U := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Q))
      (fun x : Q => x ∈ U)
    rw [hcardU, Finset.card_univ, ← Nat.card_eq_fintype_card, ← hum] at h
    omega
  rw [hcards, ← hum, Nat.cast_sub (Nat.le_mul_of_pos_right _ Nat.card_pos)]
  push_cast
  field_simp
  ring

end Frobenius

end CFSG.FeitThompson
