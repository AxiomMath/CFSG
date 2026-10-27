module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Polynomial

section Linearized

variable {K : Type*} [Field K]

variable (K) in
@[expose] noncomputable def addMonoidHomLinearEquiv (p : ℕ) [Algebra (ZMod p) K] :
    (K →+ K) ≃ₗ[K] (K →ₗ[ZMod p] K) :=
  { AddMonoidHom.toZModLinearMapEquiv p with map_smul' := fun _ _ => rfl }

variable (K) in
@[expose] noncomputable def addMonoidHom₂LinearEquiv (p : ℕ) [Algebra (ZMod p) K] :
    (K →+ K →+ K) ≃ₗ[K] (K →ₗ[ZMod p] K →ₗ[ZMod p] K) where
  toFun b := AddMonoidHom.toZModLinearMap p
    ((addMonoidHomLinearEquiv K p).toAddMonoidHom.comp b)
  invFun b := (addMonoidHomLinearEquiv K p).symm.toAddMonoidHom.comp b.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem addMonoidHomLinearEquiv_apply (p : ℕ) [Algebra (ZMod p) K] (g : K →+ K) (x : K) :
    addMonoidHomLinearEquiv K p g x = g x :=
  rfl

@[simp] theorem addMonoidHom₂LinearEquiv_apply (p : ℕ) [Algebra (ZMod p) K] (b : K →+ K →+ K)
    (x y : K) : addMonoidHom₂LinearEquiv K p b x y = b x y :=
  rfl

theorem addMonoidHom₂LinearEquiv_symm_apply (p : ℕ) [Algebra (ZMod p) K]
    (b : K →ₗ[ZMod p] K →ₗ[ZMod p] K) (x y : K) :
    (addMonoidHom₂LinearEquiv K p).symm b x y = b x y :=
  rfl

variable {p : ℕ} [Fact p.Prime] [CharP K p]

variable (K p) in
@[expose] noncomputable def frobPowHom (i : ℕ) : K →+ K :=
  (iterateFrobenius K p i).toAddMonoidHom

@[simp] theorem frobPowHom_apply (i : ℕ) (x : K) : frobPowHom K p i x = x ^ p ^ i :=
  iterateFrobenius_def p i x

variable (K p) in
@[expose] noncomputable def frobPowHom₂ (i j : ℕ) : K →+ K →+ K :=
  (AddMonoidHom.mul.compl₂ (frobPowHom K p j)).comp (frobPowHom K p i)

@[simp] theorem frobPowHom₂_apply (i j : ℕ) (x y : K) :
    frobPowHom₂ K p i j x y = x ^ p ^ i * y ^ p ^ j := by
  simp [frobPowHom₂]

omit [CharP K p] in
theorem eq_zero_of_forall_sum_mul_pow_eq_zero [Fintype K] {n : ℕ}
    (hn : p ^ (n - 1) < Fintype.card K) {a : Fin n → K}
    (ha : ∀ x : K, ∑ i, a i * x ^ p ^ (i : ℕ) = 0) : a = 0 := by
  classical
  have hp : p.Prime := Fact.out
  set P : K[X] := ∑ i : Fin n, C (a i) * X ^ p ^ (i : ℕ) with hPdef
  have hP : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := id) Function.injective_id
      (fun x => ?_) ?_
    · simp [P, eval_finsetSum, ha x]
    · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun i _ => ?_) hn
      exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.pow_le_pow_right hp.pos (by omega))
  funext i
  have hc := congrArg (fun P : K[X] => P.coeff (p ^ (i : ℕ))) hP
  simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single i (fun j _ hji => ite_eq_right fun h =>
    hji (Fin.ext (Nat.pow_right_injective hp.two_le h).symm)) (by simp), ite_eq_left rfl] at hc
  exact hc

omit [CharP K p] in
theorem eq_zero_of_forall_sum_sum_mul_pow_eq_zero [Fintype K] {n : ℕ}
    (hn : p ^ (n - 1) < Fintype.card K) {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, ∑ i, ∑ j, a i j * (x ^ p ^ (i : ℕ) * y ^ p ^ (j : ℕ)) = 0) : a = 0 := by
  have h1 : ∀ (y : K) (i : Fin n), ∑ j, a i j * y ^ p ^ (j : ℕ) = 0 := by
    intro y
    refine congrFun (eq_zero_of_forall_sum_mul_pow_eq_zero hn fun x => ?_)
    rw [← ha x y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  funext i
  exact eq_zero_of_forall_sum_mul_pow_eq_zero hn fun y => h1 y i

theorem linearIndependent_frobPowHom [Fintype K] {n : ℕ} (hn : p ^ (n - 1) < Fintype.card K) :
    LinearIndependent K (fun i : Fin n => frobPowHom K p i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  refine congrFun (eq_zero_of_forall_sum_mul_pow_eq_zero hn fun x => ?_)
  simpa using DFunLike.congr_fun hg x

theorem linearIndependent_frobPowHom₂ [Fintype K] {n : ℕ} (hn : p ^ (n - 1) < Fintype.card K) :
    LinearIndependent K (fun ij : Fin n × Fin n => frobPowHom₂ K p ij.1 ij.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg ij
  have h := eq_zero_of_forall_sum_sum_mul_pow_eq_zero hn (a := fun i j => g (i, j)) fun x y => by
    have := DFunLike.congr_fun (DFunLike.congr_fun hg x) y
    simpa [Fintype.sum_prod_type] using this
  exact congrFun (congrFun h ij.1) ij.2

theorem finrank_addMonoidHom {n : ℕ} (hK : Nat.card K = p ^ n) :
    Module.finrank K (K →+ K) = n := by
  have hp : p.Prime := Fact.out
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos n).ne')
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := K)
  rw [hK, Nat.card_zmod] at h
  rw [(addMonoidHomLinearEquiv K p).finrank_eq, Module.finrank_linearMap, Module.finrank_self,
    mul_one, ← Nat.pow_right_injective hp.two_le h]

theorem finrank_addMonoidHom₂ {n : ℕ} (hK : Nat.card K = p ^ n) :
    Module.finrank K (K →+ K →+ K) = n ^ 2 := by
  have hp : p.Prime := Fact.out
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos n).ne')
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := K)
  rw [hK, Nat.card_zmod] at h
  rw [(addMonoidHom₂LinearEquiv K p).finrank_eq, Module.finrank_linearMap,
    Module.finrank_linearMap, Module.finrank_self, mul_one,
    ← Nat.pow_right_injective hp.two_le h, sq]

end Linearized

theorem finite_field_linearized_map_bases {K : Type*} [Field K] {p n : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hK : Nat.card K = p ^ n) :
    (∀ g : K →+ K, ∃! a : Fin n → K, ∀ x, g x = ∑ i, a i * x ^ p ^ (i : ℕ)) ∧
    (∀ b : K →+ K →+ K, ∃! a : Fin n → Fin n → K,
      ∀ x y, b x y = ∑ i, ∑ j, a i j * (x ^ p ^ (i : ℕ) * y ^ p ^ (j : ℕ))) ∧
    (∃ B : Module.Basis (Fin n) K (K →+ K), ∀ i x, B i x = x ^ p ^ (i : ℕ)) ∧
    (∃ B : Module.Basis (Fin n × Fin n) K (K →+ K →+ K),
      ∀ i j x y, B (i, j) x y = x ^ p ^ (i : ℕ) * y ^ p ^ (j : ℕ)) ∧
    Module.finrank K (K →+ K) = n ∧ Module.finrank K (K →+ K →+ K) = n ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp hn hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos n).ne')
  have : Fintype K := Fintype.ofFinite K
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hlt : p ^ (n - 1) < Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have h1 := finrank_addMonoidHom (K := K) hK
  have h2 := finrank_addMonoidHom₂ (K := K) hK
  let B₁ := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_frobPowHom hlt)
    (by rw [Fintype.card_fin, h1])
  let B₂ := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_frobPowHom₂ hlt)
    (by rw [Fintype.card_prod, Fintype.card_fin, h2, sq])
  have hB₁ : ∀ i x, B₁ i x = x ^ p ^ (i : ℕ) := fun i x => by
    simp [B₁, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hB₂ : ∀ i j x y, B₂ (i, j) x y = x ^ p ^ (i : ℕ) * y ^ p ^ (j : ℕ) := fun i j x y => by
    simp [B₂, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hg : ∀ (g : K →+ K) (x : K), g x = ∑ i, B₁.repr g i * x ^ p ^ (i : ℕ) := fun g x => by
    conv_lhs => rw [← B₁.sum_repr g]
    rw [AddMonoidHom.finsetSum_apply]
    simp only [AddMonoidHom.smul_apply, smul_eq_mul, hB₁]
  have hb : ∀ (b : K →+ K →+ K) (x y : K),
      b x y = ∑ i, ∑ j, B₂.repr b (i, j) * (x ^ p ^ (i : ℕ) * y ^ p ^ (j : ℕ)) := fun b x y => by
    conv_lhs => rw [← B₂.sum_repr b]
    rw [AddMonoidHom.finsetSum_apply, AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type]
    simp only [AddMonoidHom.smul_apply, smul_eq_mul, hB₂]
  refine ⟨fun g => ⟨B₁.repr g, hg g, fun a ha => ?_⟩,
    fun b => ⟨fun i j => B₂.repr b (i, j), hb b, fun a ha => ?_⟩,
    ⟨B₁, hB₁⟩, ⟨B₂, hB₂⟩, h1, h2⟩
  · have := eq_zero_of_forall_sum_mul_pow_eq_zero hlt (a := a - B₁.repr g) fun x => by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, ← ha x, ← hg g x, sub_self]
    exact sub_eq_zero.mp this
  · have := eq_zero_of_forall_sum_sum_mul_pow_eq_zero hlt
      (a := fun i j => a i j - B₂.repr b (i, j)) fun x y => by
        simp only [sub_mul, Finset.sum_sub_distrib, ← ha x y, ← hb b x y, sub_self]
    funext i j
    exact sub_eq_zero.mp (congrFun (congrFun this i) j)

theorem finite_field_linearized_linearMap_bases {K : Type*} [Field K] {p n : ℕ}
    [Algebra (ZMod p) K] (hp : p.Prime) (hn : 1 ≤ n) (hK : Nat.card K = p ^ n) :
    (∀ g : K →ₗ[ZMod p] K, ∃! a : Fin n → K, ∀ x, g x = ∑ i, a i * x ^ p ^ (i : ℕ)) ∧
    (∀ b : K →ₗ[ZMod p] K →ₗ[ZMod p] K, ∃! a : Fin n → Fin n → K,
      ∀ x y, b x y = ∑ i, ∑ j, a i j * (x ^ p ^ (i : ℕ) * y ^ p ^ (j : ℕ))) ∧
    (∃ B : Module.Basis (Fin n) K (K →ₗ[ZMod p] K), ∀ i x, B i x = x ^ p ^ (i : ℕ)) ∧
    (∃ B : Module.Basis (Fin n × Fin n) K (K →ₗ[ZMod p] K →ₗ[ZMod p] K),
      ∀ i j x y, B (i, j) x y = x ^ p ^ (i : ℕ) * y ^ p ^ (j : ℕ)) ∧
    Module.finrank K (K →ₗ[ZMod p] K) = n ∧
    Module.finrank K (K →ₗ[ZMod p] K →ₗ[ZMod p] K) = n ^ 2 := by
  obtain ⟨h1, h2, ⟨B₁, hB₁⟩, ⟨B₂, hB₂⟩, hd₁, hd₂⟩ := finite_field_linearized_map_bases hp hn hK
  refine ⟨fun g => h1 g.toAddMonoidHom, fun b => ?_, ⟨B₁.map (addMonoidHomLinearEquiv K p), ?_⟩,
    ⟨B₂.map (addMonoidHom₂LinearEquiv K p), ?_⟩, ?_, ?_⟩
  · simpa only [addMonoidHom₂LinearEquiv_symm_apply] using
      h2 ((addMonoidHom₂LinearEquiv K p).symm b)
  · intro i x
    simp [hB₁]
  · intro i j x y
    simp [hB₂]
  · rw [← (addMonoidHomLinearEquiv K p).finrank_eq, hd₁]
  · rw [← (addMonoidHom₂LinearEquiv K p).finrank_eq, hd₂]

end CFSG.LocalAnalysis.ComponentInitial
