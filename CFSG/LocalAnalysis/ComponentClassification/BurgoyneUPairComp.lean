module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUPairBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

variable (m) in
@[expose] def prEv (l : K) (g : Matrix (Fin (m + m)) (Fin (m + m)) K) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  (prFin K m).symm (prWi m l * g * prW m l)

theorem prEv_mul (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    (g g' : Matrix (Fin (m + m)) (Fin (m + m)) K) :
    prEv m l (g * g') = prEv m l g * prEv m l g' := by
  rw [prEv, prEv, prEv, ← map_mul]
  congr 1
  calc prWi m l * (g * g') * prW m l = prWi m l * g * (prW m l * prWi m l) * g' * prW m l := by
        rw [prW_mul_prWi h2 hl, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem prEv_prPhi (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (G G' : Matrix (Fin m) (Fin m) K) :
    prEv m l (prPhi m l G G') = fromBlocks G 0 0 G' := by
  rw [prEv, prPhi]
  apply (prFin K m).injective
  rw [AlgEquiv.apply_symm_apply]
  calc prWi m l * (prW m l * prFin K m (fromBlocks G 0 0 G') * prWi m l) * prW m l =
      (prWi m l * prW m l) * prFin K m (fromBlocks G 0 0 G') * (prWi m l * prW m l) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [prWi_mul_prW h2 hl, Matrix.one_mul, Matrix.mul_one]

theorem prPhi_inj (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) {G G' H H' : Matrix (Fin m) (Fin m) K}
    (e : prPhi m l G G' = prPhi m l H H') : G = H ∧ G' = H' := by
  have := congrArg (prEv m l) e
  rw [prEv_prPhi h2 hl, prEv_prPhi h2 hl] at this
  obtain ⟨e1, -, -, e4⟩ := fromBlocks_inj.1 this
  exact ⟨e1, e4⟩

theorem prPhi_add {l : K} (G G' H H' : Matrix (Fin m) (Fin m) K) :
    prPhi m l (G + H) (G' + H') = prPhi m l G G' + prPhi m l H H' := by
  rw [prPhi, prPhi, prPhi, show fromBlocks (G + H) 0 0 (G' + H') =
    fromBlocks G 0 0 G' + fromBlocks H 0 0 H' by rw [fromBlocks_add, add_zero],
    map_add, Matrix.mul_add, Matrix.add_mul]

theorem prPhi_smul {l : K} (c : K) (G G' : Matrix (Fin m) (Fin m) K) :
    prPhi m l (c • G) (c • G') = c • prPhi m l G G' := by
  rw [prPhi, prPhi, show fromBlocks (c • G) 0 0 (c • G') = c • fromBlocks G 0 0 G' by
    rw [fromBlocks_smul, smul_zero], map_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem prPhi_commute (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (G G' : Matrix (Fin m) (Fin m) K)
    (c c' : K) :
    prPhi m l G G' * prPhi m l (c • 1) (c' • 1) = prPhi m l (c • 1) (c' • 1) * prPhi m l G G' := by
  rw [prPhi_mul h2 hl, prPhi_mul h2 hl]
  simp

theorem prEv_one (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) : prEv m l 1 = 1 := by
  rw [prEv, Matrix.mul_one]
  apply (prFin K m).injective
  rw [AlgEquiv.apply_symm_apply, map_one, prWi_mul_prW h2 hl]

section Unitary

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem prA_unitary (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    ((prA m l).map h.bar)ᵀ * prA m l = 1 := by
  rw [prA_eq_prPhi h2 hl, prPhi_unitary_iff h h2 hl hN, smul_one_map h, Matrix.mul_neg,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm,
    ← UnitaryFieldData.norm, hN, neg_smul, one_smul, neg_neg]

@[expose] def uPairA (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    uU h (m + m) :=
  ⟨uGL h (prA m l) (prA_unitary h h2 hl hN), uGL_mem h _ _⟩

theorem coe_uPairA (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    (((uPairA h h2 hl hN : uU h (m + m)) : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) = prA m l := rfl

abbrev prDual (G : SL(m, K)) : Matrix (Fin m) (Fin m) K :=
  (((G⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ

theorem prDual_spec (G : SL(m, K)) :
    ((G : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * prDual h G = 1 := by
  rw [prDual, ← conjT_mul h, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
    transpose_one]

theorem prDual_mul (G H : SL(m, K)) : prDual h (G * H) = prDual h G * prDual h H := by
  rw [prDual, prDual, prDual, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
    conjT_mul h]

theorem det_prDual (G : SL(m, K)) : (prDual h G).det = 1 := by
  have e := RingHom.map_det h.bar ((G⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)
  rw [RingHom.mapMatrix_apply] at e
  rw [prDual, det_transpose, ← e, (G⁻¹).2, map_one]

@[expose] def prSLHom (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    SL(m, K) →* StatedSU (m + m) (p ^ f) K where
  toFun G := uSUmk h (prPhi m l G (prDual h G))
    (by rw [det_prPhi h2 hl, G.2, det_prDual, one_mul])
    ((prPhi_unitary_iff h h2 hl hN _ _).2 (prDual_spec h G))
  map_one' := Subtype.ext (Units.ext (by
    change prPhi m l _ (prDual h 1) = 1
    rw [prDual, inv_one, Matrix.SpecialLinearGroup.coe_one,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one, prPhi_one h2 hl]))
  map_mul' G H := Subtype.ext (Units.ext (by
    change prPhi m l _ (prDual h (G * H)) = prPhi m l _ (prDual h G) * prPhi m l _ (prDual h H)
    rw [prPhi_mul h2 hl, prDual_mul, Matrix.SpecialLinearGroup.coe_mul]))

theorem coe_prSLHom (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    (G : SL(m, K)) :
    (((prSLHom h h2 hl hN G : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) = prPhi m l G (prDual h G) := rfl

theorem prSLHom_injective (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    Function.Injective (prSLHom (m := m) h h2 hl hN) := by
  intro G H e
  have := congrArg (fun x : StatedSU (m + m) (p ^ f) K =>
    ((x : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K)) e
  simp only [coe_prSLHom] at this
  exact Subtype.ext (prPhi_inj h2 hl this).1

theorem uLift_one_eq_iff {n : ℕ} (A : uU h n) (g : StatedSU n (p ^ f) K) :
    uLift h A 1 g = g ↔ ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hAi : ((((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAi' : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro e
    have e' := congrArg (fun x : StatedSU n (p ^ f) K =>
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) e
    simp only [coe_uLift, map_one_ringEquiv] at e'
    calc ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hAi, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e']
  · intro e
    apply Subtype.ext
    apply Units.ext
    rw [coe_uLift, map_one_ringEquiv, e, Matrix.mul_assoc, hAi', Matrix.mul_one]

theorem prPhi_commute_prA (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    (G G' : Matrix (Fin m) (Fin m) K) :
    prA m l * prPhi m l G G' = prPhi m l G G' * prA m l := by
  rw [prA_eq_prPhi h2 hl, show -(l • (1 : Matrix (Fin m) (Fin m) K)) = (-l) • 1 by
    rw [neg_smul], prPhi_commute h2 hl]

theorem mem_range_prSLHom (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    {g : StatedSU (m + m) (p ^ f) K}
    (hc : prA m l * ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
      ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) * prA m l)
    (hdet : ((prEv m l ((g : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K)).toBlocks₁₁).det = 1) :
    g ∈ (prSLHom h h2 hl hN).range := by
  obtain ⟨P, P', hg⟩ := exists_prPhi_of_commute h2 hl hc.symm
  rw [hg, prEv_prPhi h2 hl, toBlocks_fromBlocks₁₁] at hdet
  have hU := ((mem_unitarySU_iff h).1 g.2).2
  rw [hg, prPhi_unitary_iff h h2 hl hN] at hU
  set G : SL(m, K) := ⟨P, hdet⟩ with hG
  have hP' : P' = prDual h G := by
    have e3 : prDual h G * (P.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 (prDual_spec h G)
    calc P' = (prDual h G * (P.map h.bar)ᵀ) * P' := by rw [e3, Matrix.one_mul]
      _ = prDual h G := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  refine ⟨G, Subtype.ext (Units.ext ?_)⟩
  rw [coe_prSLHom, hg, hP']

theorem conj_mem_range_prSLHom (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    {x : StatedSU (m + m) (p ^ f) K}
    (hx : prA m l * ((x : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
      ((x : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) * prA m l)
    {g : StatedSU (m + m) (p ^ f) K} (hg : g ∈ (prSLHom h h2 hl hN).range) :
    x * g * x⁻¹ ∈ (prSLHom h h2 hl hN).range := by
  obtain ⟨G, rfl⟩ := hg
  set X := ((x : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) with hX
  set Xi := (((x⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
    Matrix (Fin (m + m)) (Fin (m + m)) K) with hXi
  have hXX : X * Xi = 1 := by
    rw [hX, hXi, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one]
  have hXX' : Xi * X = 1 := mul_eq_one_comm.1 hXX
  have hxi : prA m l * Xi = Xi * prA m l := by
    calc prA m l * Xi = Xi * X * prA m l * Xi := by rw [hXX', Matrix.one_mul]
      _ = Xi * (prA m l * X) * Xi := by rw [hx]; simp only [Matrix.mul_assoc]
      _ = Xi * prA m l := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hXX, Matrix.mul_one]
  obtain ⟨X₁, X₂, hX₁⟩ := exists_prPhi_of_commute h2 hl hx.symm
  obtain ⟨Y₁, Y₂, hY₁⟩ := exists_prPhi_of_commute h2 hl hxi.symm
  have hXY : X₁ * Y₁ = 1 := by
    have := congrArg (prEv m l) hXX
    rw [prEv_mul h2 hl, hX₁, hY₁, prEv_prPhi h2 hl, prEv_prPhi h2 hl, prEv_one h2 hl,
      fromBlocks_multiply, ← fromBlocks_one] at this
    simpa using (fromBlocks_inj.1 this).1
  have hmat : (((x * prSLHom h h2 hl hN G * x⁻¹ : StatedSU (m + m) (p ^ f) K) :
      GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        X * prPhi m l G (prDual h G) * Xi := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    rfl
  refine mem_range_prSLHom h h2 hl hN ?_ ?_
  · rw [hmat]
    calc prA m l * (X * prPhi m l G (prDual h G) * Xi) =
        X * (prA m l * prPhi m l G (prDual h G)) * Xi := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hx]; simp only [Matrix.mul_assoc]
      _ = X * prPhi m l G (prDual h G) * (prA m l * Xi) := by
          rw [prPhi_commute_prA h2 hl]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hxi]; simp only [Matrix.mul_assoc]
  · rw [hmat, prEv_mul h2 hl, prEv_mul h2 hl, hX₁, hY₁, prEv_prPhi h2 hl, prEv_prPhi h2 hl,
      prEv_prPhi h2 hl, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, toBlocks_fromBlocks₁₁, det_mul]
    have e := congrArg Matrix.det hXY
    rw [det_mul, det_one] at e
    rw [G.2]
    linear_combination e

theorem isQuasisimple_range_prSLHom [Finite K] (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    (hN : h.norm l = -1) (hm : 2 ≤ m) (hK : 4 ≤ Nat.card K) :
    IsQuasisimple (prSLHom (m := m) h h2 hl hN).range :=
  LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (prSLHom_injective h h2 hl hN))
    (CatalogueBGeneralLinear.specialLinear_quasisimple m K hm (Or.inr (by omega))
      (Or.inr (by omega)))

end Unitary

end CFSG.ComponentClassification.Burgoyne.U
