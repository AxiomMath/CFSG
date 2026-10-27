module

public import CFSG.Adapters.TauCetiExceptional.BigCellG2Three
public import CFSG.LieType.Chevalley.EvenExceptionalActorCoverage

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell Polynomial

variable {τ : Tag} {L : Type} [Field L]

theorem false_of_pow_eq_linear (E : Subfield L) [Finite E] {n : ℕ} (hn : 3 ≤ n)
    (hnE : n < Nat.card E) (a b : L) (h : ∀ c : E, (c : L) ^ n = a * c + b * c ^ 2) : False := by
  classical
  have : Fintype E := Fintype.ofFinite E
  set P : L[X] := X ^ n - C a * X - C b * X ^ 2 with hP
  have heval : ∀ c : E, P.eval (E.subtype c) = 0 := by
    intro c
    simp only [hP, eval_sub, eval_pow, eval_X, eval_mul, eval_C, Subfield.coe_subtype]
    rw [h c]
    ring
  have hdeg : P.natDegree < Fintype.card E := by
    rw [← Nat.card_eq_fintype_card]
    refine lt_of_le_of_lt ?_ hnE
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact natDegree_X_pow_le n
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by omega))
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have h0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero P E.subtype_injective heval hdeg
  have hc := congrArg (fun Q : L[X] => Q.coeff n) h0
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  simp [hP, coeff_X_pow, coeff_C_mul, coeff_X, hn1.symm, hn2] at hc

theorem xOp_entry_neg_inl
    (i : Fin τ.rank) (d : L) :
    xOp τ L i d (Finsupp.single (Sum.inr ⟨-Pi.single i 1, isRoot_neg_single τ i⟩) 1)
      (Sum.inl i) = d := by
  rw [← BigCell.rootVec_eq_single (isRoot_neg_single τ i), BigCell.xOp_rootVec_neg_single',
    BigCell.rootVec_eq_single (isRoot_neg_single τ i),
    BigCell.rootVec_eq_single (isRoot_single τ i), hVec]
  simp

theorem false_of_conj_xUnit_pow
    (E : Subfield L) [Finite E] (h : ModGL τ L) {i i' : Fin τ.rank}
    (hA3 : xCoeff τ L i 3 = 0) {m : ℕ} (hm : 2 ≤ m) (hmE : m < Nat.card E)
    (hm3 : 3 ≤ m ∨ 2 * m < Nat.card E)
    (hconj : ∀ c : E, h * xUnit τ L i (c : L) * h⁻¹ = xUnit τ L i' ((c : L) ^ m)) : False := by
  set T : Module.End L (RootModule τ L) → Module.End L (RootModule τ L) := fun A =>
    (h : Module.End L (RootModule τ L)) * A * ((h⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))
    with hT
  have hTx : ∀ c : E, T (xOp τ L i c) = xOp τ L i' ((c : L) ^ m) := by
    intro c
    have e := congrArg Units.val (hconj c)
    simpa only [hT, Units.val_mul, coe_xUnit] using e
  have hTq : ∀ c : L, T (xOp τ L i c) =
      1 + c • T (xCoeff τ L i 1) + c ^ 2 • T (xCoeff τ L i 2) := by
    intro c
    rw [xOp_eq_quadratic_of hA3]
    simp only [hT, mul_add, add_mul, mul_one, Units.mul_inv, mul_smul_comm, smul_mul_assoc]
  set v : RootModule τ L := Finsupp.single (Sum.inr ⟨-Pi.single i' 1, isRoot_neg_single τ i'⟩) 1
    with hv
  have hentry : ∀ (c : E) (b : Label τ), (1 : Module.End L (RootModule τ L)) v b = 0 →
      xOp τ L i' ((c : L) ^ m) v b =
        T (xCoeff τ L i 1) v b * c + T (xCoeff τ L i 2) v b * (c : L) ^ 2 := by
    intro c b h1
    rw [← hTx c, hTq]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul, h1, zero_add]
    ring
  rcases hm3 with hm3 | hm2
  · refine false_of_pow_eq_linear E hm3 hmE (T (xCoeff τ L i 1) v (Sum.inl i'))
      (T (xCoeff τ L i 2) v (Sum.inl i')) fun c => ?_
    have e := hentry c (Sum.inl i') (by
      rw [Module.End.one_apply, hv, Finsupp.single_eq_of_ne (by simp)])
    rw [hv, xOp_entry_neg_inl] at e
    rw [e]
  · refine false_of_pow_eq_linear E (n := 2 * m) (by omega) hm2
      (T (xCoeff τ L i 1) v (Sum.inr ⟨Pi.single i' 1, isRoot_single τ i'⟩))
      (T (xCoeff τ L i 2) v (Sum.inr ⟨Pi.single i' 1, isRoot_single τ i'⟩)) fun c => ?_
    have hne : (Sum.inr ⟨Pi.single i' 1, isRoot_single τ i'⟩ : Label τ) ≠
        Sum.inr ⟨-Pi.single i' 1, isRoot_neg_single τ i'⟩ := by
      intro e
      exact single_ne_neg_single i' (congrArg Subtype.val (Sum.inr_injective e))
    have e := hentry c (Sum.inr ⟨Pi.single i' 1, isRoot_single τ i'⟩) (by
      rw [Module.End.one_apply, hv, Finsupp.single_eq_of_ne hne])
    rw [hv, xOp_entry_neg, ← pow_mul, mul_comm m 2] at e
    rw [e]

theorem pow_two_pow_mul_eq_self {E : Type} [Field E] [Fintype E] {k : ℕ}
    (hE : Fintype.card E = 2 ^ k) (c : E) (q : ℕ) : c ^ 2 ^ (k * q) = c := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, ← hE, FiniteField.pow_card]

theorem eq_refl_of_conj_xUnit
    (E : Subfield L) [Finite E] {k : ℕ} (hE : Nat.card E = 2 ^ k)
    (hk : 3 ≤ k) (h : ModGL τ L) {i : Fin τ.rank} (hA3 : xCoeff τ L i 3 = 0) (σ : E ≃+* E)
    (hconj : ∀ c : E, h * xUnit τ L i (c : L) * h⁻¹ = xUnit τ L i ((σ c : E) : L)) :
    σ = RingEquiv.refl E := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hE' : Fintype.card E = 2 ^ k := by rw [← Nat.card_eq_fintype_card, hE]
  obtain ⟨j, hj⟩ := EvenExceptionalActorCoverage.exists_pow_two_pow_apply (by omega) hE σ
  have hr : ∀ c, σ c = c ^ 2 ^ (j % k) := fun c => by
    have e : c ^ 2 ^ j = c ^ 2 ^ (j % k) := by
      conv_lhs => rw [← Nat.div_add_mod j k]
      rw [pow_add, pow_mul, pow_two_pow_mul_eq_self hE' c]
    rw [hj, e]
  by_cases h0 : j % k = 0
  · exact RingEquiv.ext fun c => by rw [hr, h0, pow_zero, pow_one]; rfl
  exfalso
  have hrk : j % k < k := Nat.mod_lt j (by omega)
  have hm2 : 2 ≤ 2 ^ (j % k) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j % k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmE : 2 ^ (j % k) < Nat.card E := by
    rw [hE]
    exact Nat.pow_lt_pow_right (by norm_num) hrk
  have hm3 : 3 ≤ 2 ^ (j % k) ∨ 2 * 2 ^ (j % k) < Nat.card E := by
    by_cases h1 : j % k = 1
    · refine Or.inr ?_
      rw [h1, hE]
      calc 2 * 2 ^ 1 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    · refine Or.inl ?_
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j % k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine false_of_conj_xUnit_pow (i' := i) E h hA3 hm2 hmE hm3 fun c => ?_
  rw [hconj c, hr, SubmonoidClass.coe_pow]

end CFSG.TauCetiBridge.Even
