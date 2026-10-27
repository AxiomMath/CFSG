module

public import Mathlib.GroupTheory.Complement
public import CFSG.FeitThompson.Representations.ClassFunctionInductionTransitivity

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ScalarComplementPermutationNorm

open Pointwise InductionTransitivity

variable {L : Type*} [Group L]

lemma extendByZero_one_eq_one {I : Subgroup L} {y : L} (hy : y ∈ I) :
    extendByZero I (1 : I → ℂ) y = 1 := by
  rw [extendByZero_of_mem _ _ hy]; rfl

lemma extendByZero_one_eq_ite (I : Subgroup L) [DecidablePred (· ∈ I)] (y : L) :
    extendByZero I (1 : I → ℂ) y = if y ∈ I then 1 else 0 := by
  by_cases hy : y ∈ I
  · rw [extendByZero_one_eq_one hy, if_pos hy]
  · rw [extendByZero_of_notMem _ _ hy, if_neg hy]

lemma conj_extendByZero_one (I : Subgroup L) (y : L) :
    (starRingEnd ℂ) (extendByZero I (1 : I → ℂ) y) = extendByZero I (1 : I → ℂ) y := by
  by_cases hy : y ∈ I
  · rw [extendByZero_one_eq_one hy]; simp
  · rw [extendByZero_of_notMem _ _ hy]; simp

lemma sum_extendByZero_one [Fintype L] (I : Subgroup L) :
    ∑ y : L, extendByZero I (1 : I → ℂ) y = (Nat.card I : ℂ) := by
  classical
  rw [Finset.sum_congr rfl fun y _ => extendByZero_one_eq_ite I y, Finset.sum_boole]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma mem_conj_smul_iff {g x : L} {I : Subgroup L} :
    x ∈ MulAut.conj g • I ↔ g⁻¹ * x * g ∈ I := by
  simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.conj, mul_assoc]

lemma conj_smul_le_of_le_normal {D I : Subgroup L} [D.Normal] (hID : I ≤ D) (g : L) :
    MulAut.conj g • I ≤ D := fun x hx => by
  have h : g⁻¹ * x * g ∈ D := hID (mem_conj_smul_iff.1 hx)
  simpa [mul_assoc] using ‹D.Normal›.conj_mem _ h g

lemma conj_eq_self_of_mem {D : Subgroup L} [IsMulCommutative D] {d x : L}
    (hd : d ∈ D) (hx : x ∈ D) : d⁻¹ * x * d = x := by
  rw [setLike_mul_comm (D.inv_mem hd) hx, mul_assoc, inv_mul_cancel, mul_one]

lemma conj_smul_eq_self {D K : Subgroup L} [IsMulCommutative D] (hKD : K ≤ D) {d : L}
    (hd : d ∈ D) : MulAut.conj d • K = K := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have h : d⁻¹ * x * d ∈ K := mem_conj_smul_iff.1 hx
    have hxD : x ∈ D := by
      have : d * (d⁻¹ * x * d) * d⁻¹ ∈ D := D.mul_mem (D.mul_mem hd (hKD h)) (D.inv_mem hd)
      simpa [mul_assoc] using this
    rwa [conj_eq_self_of_mem hd hxD] at h
  · exact mem_conj_smul_iff.2 (by rwa [conj_eq_self_of_mem hd (hKD hx)])

lemma card_mul_relIndex {D I : Subgroup L} (hID : I ≤ D) :
    Nat.card I * I.relIndex D = Nat.card D := by
  rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hID).toEquiv]
  exact Subgroup.card_mul_index _

lemma index_eq_card_mul_relIndex {D B I : Subgroup L} (hDB : D.IsComplement' B) (hID : I ≤ D) :
    I.index = Nat.card B * I.relIndex D := by
  rw [← Subgroup.relIndex_mul_index hID, hDB.symm.index_eq_card, mul_comm]

theorem indClassFun_one_apply_one [Finite L] {D B I : Subgroup L}
    (hDB : D.IsComplement' B) (hID : I ≤ D) :
    indClassFun I (1 : I → ℂ) 1 = (Nat.card B : ℂ) * (I.relIndex D : ℂ) := by
  let _ := Fintype.ofFinite L
  have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [indClassFun_apply]
  have h : ∀ t : L, extendByZero I (1 : I → ℂ) (t⁻¹ * 1 * t) = 1 := fun _ =>
    extendByZero_one_eq_one (by simp)
  rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Nat.card_eq_fintype_card, ← Subgroup.index_mul_card I,
    index_eq_card_mul_relIndex hDB hID]
  push_cast
  field_simp

theorem indClassFun_one_apply_eq_zero [Finite L] {D I : Subgroup L} [D.Normal] (hID : I ≤ D)
    {x : L} (hx : x ∉ D) : indClassFun I (1 : I → ℂ) x = 0 := by
  refine indClassFun_eq_zero_of_forall_notMem I _ fun t hmem => hx ?_
  have h : t⁻¹ * x * t ∈ D := hID hmem
  simpa [mul_assoc] using ‹D.Normal›.conj_mem _ h t

lemma extendByZero_one_mul_conj (I : Subgroup L) (g y : L) :
    extendByZero I (1 : I → ℂ) y * extendByZero I (1 : I → ℂ) (g⁻¹ * y * g)
      = extendByZero (I ⊓ MulAut.conj g • I)
          (1 : (I ⊓ MulAut.conj g • I : Subgroup L) → ℂ) y := by
  by_cases h1 : y ∈ I
  · by_cases h2 : g⁻¹ * y * g ∈ I
    · rw [extendByZero_one_eq_one h1, extendByZero_one_eq_one h2,
        extendByZero_one_eq_one (I := I ⊓ MulAut.conj g • I)
          (Subgroup.mem_inf.2 ⟨h1, mem_conj_smul_iff.2 h2⟩), one_mul]
    · rw [extendByZero_of_notMem _ _ h2, mul_zero,
        extendByZero_of_notMem _ _ (fun h => h2 (mem_conj_smul_iff.1 (Subgroup.mem_inf.1 h).2))]
  · rw [extendByZero_of_notMem _ _ h1, zero_mul,
      extendByZero_of_notMem _ _ (fun h => h1 (Subgroup.mem_inf.1 h).1)]

lemma sum_extendByZero_one_mul_conj [Fintype L] (I : Subgroup L) (t s : L) :
    ∑ x : L, extendByZero I (1 : I → ℂ) (t⁻¹ * x * t)
        * extendByZero I (1 : I → ℂ) (s⁻¹ * x * s)
      = (Nat.card (I ⊓ MulAut.conj (t⁻¹ * s) • I : Subgroup L) : ℂ) := by
  rw [← sum_extendByZero_one]
  refine (Fintype.sum_equiv (MulAut.conj t).toEquiv _ _ ?_).symm
  intro y
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply]
  rw [← extendByZero_one_mul_conj]
  congr 2 <;> group

lemma sum_mul_conj_indClassFun_one [Fintype L] (I : Subgroup L) :
    ∑ x : L, indClassFun I (1 : I → ℂ) x * (starRingEnd ℂ) (indClassFun I (1 : I → ℂ) x)
      = (Nat.card I : ℂ)⁻¹ ^ 2 * ((Nat.card L : ℂ)
        * ∑ g : L, (Nat.card (I ⊓ MulAut.conj g • I : Subgroup L) : ℂ)) := by
  have hconj : ∀ x : L, (starRingEnd ℂ) (indClassFun I (1 : I → ℂ) x)
      = indClassFun I (1 : I → ℂ) x := fun x => by
    rw [indClassFun_apply, map_mul, map_sum, map_inv₀, Complex.conj_natCast]
    exact congrArg _ (Finset.sum_congr rfl fun t _ => conj_extendByZero_one I _)
  calc ∑ x : L, indClassFun I (1 : I → ℂ) x * (starRingEnd ℂ) (indClassFun I (1 : I → ℂ) x)
      = ∑ x : L, (Nat.card I : ℂ)⁻¹ ^ 2 *
          ∑ t : L, ∑ s : L, extendByZero I (1 : I → ℂ) (t⁻¹ * x * t)
            * extendByZero I (1 : I → ℂ) (s⁻¹ * x * s) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hconj x, indClassFun_apply, mul_mul_mul_comm, ← sq, Finset.sum_mul_sum]
    _ = (Nat.card I : ℂ)⁻¹ ^ 2 * ∑ t : L, ∑ s : L, ∑ x : L,
          extendByZero I (1 : I → ℂ) (t⁻¹ * x * t)
            * extendByZero I (1 : I → ℂ) (s⁻¹ * x * s) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ => Finset.sum_comm ..
    _ = (Nat.card I : ℂ)⁻¹ ^ 2 * ∑ t : L, ∑ s : L,
          (Nat.card (I ⊓ MulAut.conj (t⁻¹ * s) • I : Subgroup L) : ℂ) :=
        congrArg _ (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ =>
          sum_extendByZero_one_mul_conj I t s)
    _ = (Nat.card I : ℂ)⁻¹ ^ 2 * ((Nat.card L : ℂ)
          * ∑ g : L, (Nat.card (I ⊓ MulAut.conj g • I : Subgroup L) : ℂ)) := by
        congr 1
        have h : ∀ t : L, ∑ s : L, (Nat.card (I ⊓ MulAut.conj (t⁻¹ * s) • I : Subgroup L) : ℂ)
            = ∑ g : L, (Nat.card (I ⊓ MulAut.conj g • I : Subgroup L) : ℂ) := fun t =>
          Fintype.sum_equiv (Equiv.mulLeft t⁻¹) _ _ fun s => rfl
        rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Nat.card_eq_fintype_card]

lemma sum_card_inf_conj [Fintype L] {D B I : Subgroup L} [D.Normal] [IsMulCommutative D]
    (hDB : D.IsComplement' B) (hID : I ≤ D)
    (hI : ∀ b ∈ B, b ≠ 1 → I ⊓ MulAut.conj b⁻¹ • I = ⊥) :
    ∑ g : L, (Nat.card (I ⊓ MulAut.conj g • I : Subgroup L) : ℂ)
      = (Nat.card D : ℂ) * ((Nat.card I : ℂ) + (Nat.card B : ℂ) - 1) := by
  classical
  have hbij := Fintype.sum_bijective (fun p : D × B => (p.1 : L) * (p.2 : L)) hDB
    (fun p => (Nat.card (I ⊓ MulAut.conj ((p.1 : L) * (p.2 : L)) • I : Subgroup L) : ℂ))
    (fun g => (Nat.card (I ⊓ MulAut.conj g • I : Subgroup L) : ℂ)) fun _ => rfl
  rw [← hbij, Fintype.sum_prod_type]
  have hterm : ∀ (d : D) (b : B),
      (Nat.card (I ⊓ MulAut.conj ((d : L) * (b : L)) • I : Subgroup L) : ℂ)
        = (Nat.card (I ⊓ MulAut.conj (b : L) • I : Subgroup L) : ℂ) := by
    intro d b
    have h1 : MulAut.conj ((d : L) * (b : L)) • I
        = MulAut.conj (d : L) • (MulAut.conj (b : L) • I) := by rw [map_mul, mul_smul]
    rw [h1, conj_smul_eq_self (conj_smul_le_of_le_normal hID (b : L)) d.2]
  rw [Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => hterm d b,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  congr 1
  have hinv : ∑ b : B, (Nat.card (I ⊓ MulAut.conj (b : L) • I : Subgroup L) : ℂ)
      = ∑ b : B, (Nat.card (I ⊓ MulAut.conj ((b : L)⁻¹) • I : Subgroup L) : ℂ) :=
    Fintype.sum_equiv (Equiv.inv B) _ _ fun b => by simp
  rw [hinv, ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : B))]
  have h1 : ∀ b ∈ Finset.univ.erase (1 : B),
      (Nat.card (I ⊓ MulAut.conj ((b : L)⁻¹) • I : Subgroup L) : ℂ) = 1 := by
    intro b hb
    have hb' : (b : L) ≠ 1 := fun h => (Finset.mem_erase.1 hb).1 (Subtype.ext h)
    rw [hI (b : L) b.2 hb', Subgroup.card_bot]
    norm_num
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card]
  simp only [OneMemClass.coe_one, inv_one, map_one, one_smul, inf_idem]
  rw [Nat.cast_sub Nat.card_pos]
  push_cast
  ring

theorem classFunInner_indClassFun_one_self [Finite L] {D B I : Subgroup L} [D.Normal]
    [IsMulCommutative D] (hDB : D.IsComplement' B) (hID : I ≤ D)
    (hI : ∀ b ∈ B, b ≠ 1 → I ⊓ MulAut.conj b⁻¹ • I = ⊥) :
    classFunInner (indClassFun I (1 : I → ℂ)) (indClassFun I (1 : I → ℂ))
      = (I.relIndex D : ℂ) + ((Nat.card B : ℂ) - 1) * (I.relIndex D : ℂ) ^ 2
        / (Nat.card D : ℂ) := by
  let _ := Fintype.ofFinite L
  have hI0 : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hL0 : (Nat.card L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hrel : (I.relIndex D : ℂ) ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
  have hu : (Nat.card D : ℂ) = (Nat.card I : ℂ) * (I.relIndex D : ℂ) := by
    rw [← Nat.cast_mul, card_mul_relIndex hID]
  rw [classFunInner_apply, sum_mul_conj_indClassFun_one, sum_card_inf_conj hDB hID hI, hu]
  field_simp
  ring

end ScalarComplementPermutationNorm

end CFSG.FeitThompson
