module

public import CFSG.Quasithin.Recognition.RuTypeSigma

public section

namespace CFSG.ComponentClassification.GMS78.RuGamma

open CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma Matrix

@[expose] def w2 : F4 := F4.ω * F4.ω

@[expose] def lineRep : Fin 5 → Fin 2 → F4 :=
  ![![1, 0], ![0, 1], ![1, 1], ![1, F4.ω], ![1, w2]]

@[expose] def lineIdx (v : Fin 2 → F4) : Fin 5 :=
  if v 0 = 0 then 1
  else if v 1 = 0 then 0
  else if v 1 = v 0 then 2
  else if v 1 = F4.ω * v 0 then 3 else 4

theorem lineIdx_lineRep : ∀ i, lineIdx (lineRep i) = i := by decide

theorem lineRep_ne_zero : ∀ i, lineRep i ≠ 0 := by decide

theorem lineIdx_smul : ∀ c : F4, c ≠ 0 → ∀ v : Fin 2 → F4, lineIdx (c • v) = lineIdx v := by
  decide

theorem exists_smul_lineRep :
    ∀ v : Fin 2 → F4, v ≠ 0 → ∃ c : F4, c ≠ 0 ∧ v = c • lineRep (lineIdx v) := by
  decide

@[expose] def frobPow (k : Multiplicative (ZMod 2)) (c : F4) : F4 :=
  if Multiplicative.toAdd k = 0 then c else frobF4 c

theorem frobPow_ne_zero : ∀ (k : Multiplicative (ZMod 2)) (c : F4), c ≠ 0 → frobPow k c ≠ 0 := by
  decide

theorem frobVec_smul (k : Multiplicative (ZMod 2)) (c : F4) (v : Fin 2 → F4) :
    frobVec k (c • v) = frobPow k c • frobVec k v := by
  unfold frobVec frobPow
  split_ifs
  · rfl
  · funext i
    simp [map_mul]

theorem sigmaAct_smul (x : SigmaL2F4) (c : F4) (v : Fin 2 → F4) :
    sigmaAct x (c • v) = frobPow x.right c • sigmaAct x v := by
  simp only [sigmaAct, frobVec_smul, Matrix.mulVec_smul]

theorem sigmaAct_ne_zero (x : SigmaL2F4) {v : Fin 2 → F4} (hv : v ≠ 0) : sigmaAct x v ≠ 0 := by
  intro h
  apply hv
  have h1 := sigmaAct_mul x⁻¹ x v
  rw [inv_mul_cancel, sigmaAct_one, h, sigmaAct_zero] at h1
  exact h1

@[expose] def lineAct (x : SigmaL2F4) (i : Fin 5) : Fin 5 := lineIdx (sigmaAct x (lineRep i))

theorem lineAct_mul (x y : SigmaL2F4) (i : Fin 5) :
    lineAct (x * y) i = lineAct x (lineAct y i) := by
  obtain ⟨c, hc, he⟩ := exists_smul_lineRep _ (sigmaAct_ne_zero y (lineRep_ne_zero i))
  have h1 : lineAct (x * y) i = lineIdx (sigmaAct x (sigmaAct y (lineRep i))) := by
    rw [lineAct, sigmaAct_mul]
  rw [h1, he, sigmaAct_smul, lineIdx_smul _ (frobPow_ne_zero _ _ hc)]
  rfl

theorem lineAct_one (i : Fin 5) : lineAct 1 i = i := by
  rw [lineAct, sigmaAct_one, lineIdx_lineRep]

@[expose] def linePerm : SigmaL2F4 →* Equiv.Perm (Fin 5) where
  toFun x :=
    { toFun := lineAct x
      invFun := lineAct x⁻¹
      left_inv := fun i => by rw [← lineAct_mul, inv_mul_cancel, lineAct_one]
      right_inv := fun i => by rw [← lineAct_mul, mul_inv_cancel, lineAct_one] }
  map_one' := Equiv.ext lineAct_one
  map_mul' x y := Equiv.ext (lineAct_mul x y)

theorem lineAct_faithful : ∀ x : SigmaL2F4, (∀ i, lineAct x i = i) → x = 1 := by
  decide +kernel

theorem linePerm_bijective : Function.Bijective linePerm := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by rw [card_Sigma, Fintype.card_perm, Fintype.card_fin]; rfl⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  exact lineAct_faithful x fun i => congrArg (fun σ : Equiv.Perm (Fin 5) => σ i) hx

abbrev V4 : Type := Fin 4 → ZMod 2

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def c5 : M4 := !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1]

@[expose] def fr : M4 := !![1, 0, 1, 0; 0, 0, 1, 1; 0, 1, 1, 0; 0, 0, 1, 0]

theorem c5_mulVec_single :
    c5 *ᵥ Pi.single 0 1 = Pi.single 1 1 ∧ c5 *ᵥ Pi.single 1 1 = Pi.single 2 1 ∧
      c5 *ᵥ Pi.single 2 1 = Pi.single 3 1 ∧ c5 *ᵥ Pi.single 3 1 = ![1, 1, 1, 1] := by
  decide

theorem fr_mulVec_single :
    ∀ j : Fin 4, fr *ᵥ Pi.single j 1 = c5 ^ (2 * (j : ℕ)) *ᵥ Pi.single 0 1 := by
  decide

theorem fr_pow_three_mulVec : fr ^ 3 *ᵥ Pi.single 1 1 = Pi.single 3 1 := by decide

theorem fr_mulVec_single_one : fr *ᵥ Pi.single 1 1 = Pi.single 2 1 := by decide

theorem c5_irred : ∀ c : V4, c ≠ 0 → ∃ a : V4,
    a 0 • c + a 1 • (c5 *ᵥ c) + a 2 • (c5 *ᵥ (c5 *ᵥ c)) + a 3 • (c5 *ᵥ (c5 *ᵥ (c5 *ᵥ c))) =
      Pi.single 0 1 := by
  decide +kernel

@[expose] def zf (a : ZMod 2) : F4 := if a = 0 then 0 else 1

@[expose] def kapE : Fin 4 → Fin 2 → F4 := ![![1, 0], ![F4.ω, F4.ω], ![F4.ω, w2], ![1, w2]]

@[expose] def kap (v : V4) : Fin 2 → F4 := ∑ i, zf (v i) • kapE i

theorem zf_add : ∀ a b : ZMod 2, zf (a + b) = zf a + zf b := by decide

theorem kap_add (v w : V4) : kap (v + w) = kap v + kap w := by
  simp only [kap, Pi.add_apply, zf_add, add_smul, Finset.sum_add_distrib]

theorem kap_eq_zero : ∀ v : V4, kap v = 0 → v = 0 := by decide

theorem kap_injective : Function.Injective kap := by
  intro v w h
  have h2 : kap (v + w) = 0 := by
    rw [kap_add, h]
    funext i
    exact CharTwo.add_self_eq_zero _
  have h3 := kap_eq_zero _ h2
  funext i
  have h4 := congrFun h3 i
  simp only [Pi.add_apply, Pi.zero_apply] at h4
  calc v i = v i + (v i + w i) := by rw [h4, add_zero]
    _ = w i := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem kap_surjective : Function.Surjective kap := by
  have h : Function.Bijective kap := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨kap_injective, rfl⟩
  exact h.2

@[expose] def sigC5 : SigmaL2F4 :=
  ⟨⟨!![F4.ω, w2; F4.ω, 0], by rw [Matrix.det_fin_two_of]; decide⟩, 1⟩

@[expose] def sigFr : SigmaL2F4 :=
  ⟨⟨!![1, F4.ω; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩, Multiplicative.ofAdd 1⟩

theorem c5_cert : ∀ v : V4, kap (c5 *ᵥ v) = sigmaAct sigC5 (kap v) := by decide +kernel

theorem fr_cert : ∀ v : V4, kap (fr *ᵥ v) = sigmaAct sigFr (kap v) := by decide +kernel

@[expose] def candMat (u : V4) (e : ℕ) : M4 :=
  Matrix.of fun r c => (![Pi.single 0 1, u, fr ^ e *ᵥ u, fr ^ (3 * e) *ᵥ u] c) r

theorem candMat_mulVec_single (u : V4) (e : ℕ) :
    candMat u e *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧ candMat u e *ᵥ Pi.single 1 1 = u ∧
      candMat u e *ᵥ Pi.single 2 1 = fr ^ e *ᵥ u ∧
        candMat u e *ᵥ Pi.single 3 1 = fr ^ (3 * e) *ᵥ u := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext r <;> simp [candMat]

@[expose] def evalW {α : Type*} [Monoid α] (g : Fin 3 → α) : List (Fin 3) → α
  | [] => 1
  | i :: w => g i * evalW g w

@[expose] def evalV (g : Fin 3 → M4) : List (Fin 3) → V4 → V4
  | [], v => v
  | i :: w, v => g i *ᵥ evalV g w v

theorem evalV_eq (g : Fin 3 → M4) : ∀ (w : List (Fin 3)) (v : V4), evalV g w v = evalW g w *ᵥ v
  | [], v => by rw [evalV, evalW, Matrix.one_mulVec]
  | i :: w, v => by rw [evalV, evalW, evalV_eq g w v, Matrix.mulVec_mulVec]

@[expose] def goodTriples : List (V4 × ℕ × SigmaL2F4 × List (List (Fin 3))) :=
  [(![1, 1, 0, 0], 3, ⟨⟨!![1, w2; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩, 1⟩,
      [[], [0], [2, 0], [0, 0], [1, 2, 0], [0, 2, 0], [0, 0, 0, 2, 0], [0, 0, 0], [2, 0, 0],
        [2, 0, 2, 0], [1, 0, 2, 0], [0, 0, 2, 0], [0, 2, 0, 0], [2, 1, 0, 0], [1, 0, 0]]),
    (![1, 0, 1, 0], 3, ⟨⟨!![1, 0; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩,
      Multiplicative.ofAdd 1⟩,
      [[], [0], [2, 0, 0], [0, 0], [2, 0], [0, 2, 0, 0], [1, 0, 0, 2, 0], [0, 0, 0], [2, 1, 0, 0],
        [0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0, 0], [0, 2, 1, 0, 0], [1, 2, 0], [1, 0, 0]]),
    (![1, 0, 0, 1], 3, ⟨⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩,
      Multiplicative.ofAdd 1⟩,
      [[], [0], [1, 2, 0], [0, 0], [2, 1, 0, 0], [0, 1, 2, 0], [0, 1, 0, 2, 0], [0, 0, 0], [2, 0],
        [0, 2, 1, 0, 0], [1, 0, 1, 2, 0], [1, 0, 2, 0], [0, 2, 0], [2, 0, 0], [1, 0, 0]]),
    (![0, 1, 1, 1], 3, ⟨⟨!![1, F4.ω; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩, 1⟩,
      [[], [0], [0, 2, 0], [0, 0], [2, 0, 0], [0, 0, 2, 0], [2, 0, 2, 0, 0], [0, 0, 0], [1, 2, 0],
        [0, 2, 0, 0], [0, 0, 2, 0, 0], [0, 0, 0, 2, 0], [0, 1, 2, 0], [2, 0], [1, 0, 0]])]

@[expose] def Order3Fix (M : M4) : Prop :=
  M ^ 3 = 1 ∧ M ≠ 1 ∧ ∃ v : V4, v ≠ 0 ∧ M *ᵥ v = v

instance (M : M4) : Decidable (Order3Fix M) := by
  unfold Order3Fix
  infer_instance

@[expose] def badTriples : List (V4 × ℕ × List (Fin 3)) :=
  [(![0, 1, 0, 0], 3, [0, 1, 2]), (![1, 1, 0, 0], 1, [0, 0, 0, 0, 2, 0, 2]),
    (![0, 0, 1, 0], 3, [0, 2]), (![1, 0, 1, 0], 1, [0, 1, 2, 0, 1, 2]),
    (![0, 0, 0, 1], 3, [0, 0, 2]), (![1, 0, 0, 1], 1, [0, 0, 2, 0, 1, 1, 2]),
    (![0, 1, 1, 1], 1, [0, 2, 0, 2]), (![1, 1, 1, 1], 3, [0, 2, 1])]

theorem cand_classify : ∀ u : V4, ∀ e ∈ ([1, 3] : List ℕ),
    candMat u e * fr = fr ^ e * candMat u e → (∀ j : Fin 4, candMat u e ≠ fr ^ (j : ℕ)) →
      (u, e) ∈ goodTriples.map (fun t => (t.1, t.2.1)) ∨
        (u, e) ∈ badTriples.map (fun t => (t.1, t.2.1)) := by
  decide +kernel

theorem good_cert : ∀ t ∈ goodTriples,
    ∀ v : V4, kap (candMat t.1 t.2.1 *ᵥ v) = sigmaAct t.2.2.1 (kap v) := by
  decide +kernel

theorem good_orbit : ∀ t ∈ goodTriples, ∀ c : V4, c ≠ 0 →
    ∃ w ∈ t.2.2.2, evalV ![c5, fr, candMat t.1 t.2.1] w (Pi.single 0 1) = c := by
  decide +kernel

theorem bad_cert : ∀ t ∈ badTriples, Order3Fix (evalW ![c5, fr, candMat t.1 t.2.1] t.2.2) := by
  decide +kernel

end CFSG.ComponentClassification.GMS78.RuGamma
