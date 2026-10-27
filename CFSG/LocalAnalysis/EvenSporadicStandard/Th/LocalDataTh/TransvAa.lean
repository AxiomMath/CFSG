module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.AaCard
public import Certificates.Certificate24216

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Native
open scoped Matrix

@[expose] def Mmat : Fin 4 → Fin 4 → ZMod 4 :=
  ![![1, 0, 2, 0], ![1, 1, 0, 3], ![2, 0, 3, 0], ![2, 0, 2, 3]]

theorem card_fix_Mmat :
    (Finset.univ.filter fun e : Fin 4 → ZMod 4 =>
      (fun i => ∑ j, Mmat i j * e j) = e).card ≤ 16 := by
  decide

theorem card_neg_Mmat :
    (Finset.univ.filter fun e : Fin 4 → ZMod 4 =>
      (fun i => ∑ j, Mmat i j * e j) = fun i => - e i).card ≤ 16 := by
  decide

section Aa


@[expose] noncomputable def ex (e : Fin 4 → ZMod 4) : J :=
  gA 0 ^ (e 0).val * gA 1 ^ (e 1).val * gA 2 ^ (e 2).val * gA 3 ^ (e 3).val

theorem gA_pow_four (R : AaRel) (i : Fin 4) : gA i ^ 4 = 1 := AaJ_exp R _ (gA_mem i)

theorem gA_pow_comm (R : AaRel) (i j : Fin 4) (k l : ℕ) :
    gA i ^ k * gA j ^ l = gA j ^ l * gA i ^ k :=
  AaJ_comm R _ (AaJ.pow_mem (gA_mem i) k) _ (AaJ.pow_mem (gA_mem j) l)

theorem gA_pow_val_add (R : AaRel) (i : Fin 4) (a b : ZMod 4) :
    gA i ^ (a + b).val = gA i ^ a.val * gA i ^ b.val := by
  calc gA i ^ (a + b).val = gA i ^ ((a.val + b.val) % 4) := by rw [ZMod.val_add]
    _ = gA i ^ (a.val + b.val) := (pow_eq_pow_mod _ (gA_pow_four R i)).symm
    _ = gA i ^ a.val * gA i ^ b.val := pow_add _ _ _

theorem ex_add (R : AaRel) (e e' : Fin 4 → ZMod 4) : ex (e + e') = ex e * ex e' := by
  unfold ex
  simp only [Pi.add_apply]
  rw [gA_pow_val_add R 0, gA_pow_val_add R 1, gA_pow_val_add R 2, gA_pow_val_add R 3]
  exact (mul4_mul4_J (gA_pow_comm R _ _ _ _) (gA_pow_comm R _ _ _ _) (gA_pow_comm R _ _ _ _)
    (gA_pow_comm R _ _ _ _) (gA_pow_comm R _ _ _ _) (gA_pow_comm R _ _ _ _)).symm

theorem ex_zero : ex 0 = 1 := by simp [ex]

theorem ex_mem (e : Fin 4 → ZMod 4) : ex e ∈ AaJ :=
  AaJ.mul_mem (AaJ.mul_mem (AaJ.mul_mem (AaJ.pow_mem (gA_mem 0) _) (AaJ.pow_mem (gA_mem 1) _))
    (AaJ.pow_mem (gA_mem 2) _)) (AaJ.pow_mem (gA_mem 3) _)

theorem ex_neg (R : AaRel) (e : Fin 4 → ZMod 4) : ex (-e) = (ex e)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← ex_add R, neg_add_cancel, ex_zero]

theorem ex_pow (R : AaRel) (v : Fin 4 → ZMod 4) (k : ℕ) :
    ex v ^ k = ex (fun i => (k : ZMod 4) * v i) := by
  induction k with
  | zero =>
    have : (fun i => ((0 : ℕ) : ZMod 4) * v i) = 0 := by funext i; simp
    rw [this, ex_zero, pow_zero]
  | succ k ih =>
    rw [pow_succ, ih, ← ex_add R]
    congr 1
    funext i
    simp [Nat.cast_succ, add_mul]

theorem ex_pow_val (R : AaRel) (v : Fin 4 → ZMod 4) (k : ZMod 4) :
    ex v ^ k.val = ex (fun i => k * v i) := by
  rw [ex_pow R]
  simp

theorem ex_surj (R : AaRel) {x : J} (hx : x ∈ AaJ) : ∃ e, ex e = x := by
  refine Subgroup.closure_induction (p := fun x _ => ∃ e, ex e = x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    have hv1 : (1 : ZMod 4).val = 1 := rfl
    fin_cases i <;> simp [ex, hv1]
  · exact ⟨0, ex_zero⟩
  · rintro a b - - ⟨e, rfl⟩ ⟨e', rfl⟩
    exact ⟨e + e', ex_add R e e'⟩
  · rintro a - ⟨e, rfl⟩
    exact ⟨-e, ex_neg R e⟩

theorem ex_bijective (R : AaRel) :
    Function.Bijective (fun e : Fin 4 → ZMod 4 => (⟨ex e, ex_mem e⟩ : ↥AaJ)) := by
  have hs : Function.Surjective (fun e : Fin 4 → ZMod 4 => (⟨ex e, ex_mem e⟩ : ↥AaJ)) := by
    rintro ⟨x, hx⟩
    obtain ⟨e, he⟩ := ex_surj R hx
    exact ⟨e, Subtype.ext he⟩
  have hcard : Nat.card (Fin 4 → ZMod 4) ≤ Nat.card ↥AaJ := by
    rw [card_AaJ R]
    simp [Nat.card_eq_fintype_card]
  exact hs.bijective_of_nat_card_le hcard

theorem ex_injective (R : AaRel) : Function.Injective ex := by
  intro e e' h
  exact (ex_bijective R).1 (Subtype.ext h)

theorem conj_mul4 (n a b c d : J) :
    n * (a * b * c * d) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) * (n * c * n⁻¹) * (n * d * n⁻¹) := by
  group

theorem ex_conj (R : AaRel) {n : J} (M : Fin 4 → Fin 4 → ZMod 4)
    (h : ∀ j, n * gA j * n⁻¹ = ex (fun i => M i j)) (e : Fin 4 → ZMod 4) :
    n * ex e * n⁻¹ = ex (fun i => ∑ j, M i j * e j) := by
  have h1 : ∀ (j : Fin 4) (k : ℕ), n * gA j ^ k * n⁻¹ = ex (fun i => M i j) ^ k := fun j k => by
    rw [← h j, conj_pow]
  conv_lhs => unfold ex
  rw [conj_mul4, h1, h1, h1, h1]
  rw [ex_pow_val R, ex_pow_val R, ex_pow_val R, ex_pow_val R, ← ex_add R, ← ex_add R,
    ← ex_add R]
  congr 1
  funext i
  simp only [Pi.add_apply, Fin.sum_univ_four]
  ring

theorem acts_q1 : Acts (q 1) (matOfCols 4 T0cols) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := Certificates.certificate24216
  have c0 : q 1 * aGen 0 * (q 1)⁻¹ = cA (matOfCols 4 T0cols *ᵥ Pi.single 0 1) := by
    rw [matOfCols_mulVec_single, aGen_zero]
    exact conj_gen_of_eqRows (isRows_q 1) isRows_z h0
  have c1 : q 1 * aGen 1 * (q 1)⁻¹ = cA (matOfCols 4 T0cols *ᵥ Pi.single 1 1) := by
    rw [matOfCols_mulVec_single]
    exact conj_gen_of_eqRows (isRows_q 1) isRows_aGen_one h1
  have c2 : q 1 * aGen 2 * (q 1)⁻¹ = cA (matOfCols 4 T0cols *ᵥ Pi.single 2 1) := by
    rw [matOfCols_mulVec_single]
    exact conj_gen_of_eqRows (isRows_q 1) isRows_aGen_two h2
  have c3 : q 1 * aGen 3 * (q 1)⁻¹ = cA (matOfCols 4 T0cols *ᵥ Pi.single 3 1) := by
    rw [matOfCols_mulVec_single]
    exact conj_gen_of_eqRows (isRows_q 1) isRows_aGen_three h3
  apply Acts.of_gens
  intro j
  fin_cases j
  · exact c0
  · exact c1
  · exact c2
  · exact c3

end Aa

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
