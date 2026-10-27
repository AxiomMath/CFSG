module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelLevi
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)

variable {K : Type} [Field K] {n j : ℕ}

section Off

variable (j) in
@[expose] def SpAOff (B : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ k l, B k l ≠ 0 → k.val < 2 * j ∧ 2 * j ≤ l.val

variable (j) in
@[expose] def SpAInner (C : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ k l : Fin n, 2 * j ≤ k.val → 2 * j ≤ l.val → C k l = 0

theorem SpAOff.mul_eq_zero {B B' : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B)
    (hB' : SpAOff j B') : B * B' = 0 := by
  ext k l
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_contra h
  have h1 := hB k m (left_ne_zero_of_mul h)
  have h2 := hB' m l (right_ne_zero_of_mul h)
  omega

theorem SpAOff.mul_left_eq_zero {B M : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B)
    (hM : ∀ k l, 2 * j ≤ k.val → M k l = 0) : B * M = 0 := by
  ext k l
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases h : B k m = 0
  · rw [h, zero_mul]
  · rw [hM m l (hB k m h).2, mul_zero]

theorem SpAOff.mul_spARepMat {B : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) :
    B * spARepMat n j = 0 :=
  hB.mul_left_eq_zero fun k l hk => by
    rw [spARepMat, of_apply, ite_eq_right (fun h => absurd h.2.2.1 (by omega))]

theorem SpAOff.spARepMat_mul_transpose {B : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) :
    spARepMat n j * Bᵀ = 0 := by
  have h := congrArg Matrix.transpose hB.mul_spARepMat
  rwa [transpose_mul, spARepMat_transpose, transpose_zero] at h

theorem SpAOff.apply_eq_zero {B : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) {k : Fin n}
    (hk : 2 * j ≤ k.val) (l : Fin n) : B k l = 0 := by
  by_contra h
  have := (hB k l h).1
  omega

@[expose] def spAOffUnit {B : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) : GL (Fin n) K where
  val := 1 + B
  inv := 1 - B
  val_inv := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hB.mul_eq_zero hB,
      sub_zero, sub_add_cancel]
  inv_val := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hB.mul_eq_zero hB,
      add_zero, add_sub_cancel_right]

theorem coe_spAOffUnit {B : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) :
    ((spAOffUnit hB : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + B := rfl

theorem coe_spAOffUnit_inv {B : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) :
    (((spAOffUnit hB)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 - B := rfl

end Off

section Elt

variable {B C : Matrix (Fin n) (Fin n) K}

@[expose] noncomputable def spARadElt (hB : SpAOff j B) (hC : Cᵀ = C) : StatedSp n K :=
  leviEmbedGL K n (spAOffUnit hB) * upperUnipotentSp n K hC

theorem mat_spARadElt (hB : SpAOff j B) (hC : Cᵀ = C) :
    mat n K (spARadElt hB hC) = fromBlocks (1 + B) ((1 + B) * C) 0 (1 - Bᵀ) := by
  rw [spARadElt, map_mul, mat_leviEmbedGL, mat_upperUnipotentSp, fromBlocks_multiply,
    coe_spAOffUnit, coe_spAOffUnit_inv]
  simp [transpose_sub]

theorem spARadElt_mem_centralizer (hB : SpAOff j B) (hC : Cᵀ = C) :
    spARadElt hB hC ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  rw [mem_centralizer_singleton_iff, commute_spARep_iff, mat_spARadElt, spANil,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.add_mul, Matrix.one_mul, hB.mul_spARepMat, add_zero, Matrix.mul_sub, Matrix.mul_one,
    hB.spARepMat_mul_transpose, sub_zero]

theorem spALeviPart_spARadElt (hB : SpAOff j B) (hC : Cᵀ = C) (hCi : SpAInner j C) :
    spALeviPart j (mat n K (spARadElt hB hC)) = 1 := by
  ext r t
  rw [spALeviPart_apply, mat_spARadElt]
  split_ifs with hrt
  · rcases r with k | k <;> rcases t with l | l
    · have hB0 : B k l = 0 := by
        by_contra h
        have h' := hB k l h
        simp [h'.1, show ¬ l.val < 2 * j by omega] at hrt
      simp [Matrix.add_apply, hB0, Matrix.one_apply]
    · have hk : 2 * j ≤ k.val := by
        by_contra hk
        rw [spABlk_inl, spABlk_inr, ite_eq_left (by omega)] at hrt
        split_ifs at hrt <;> exact absurd hrt (by decide)
      have hl : 2 * j ≤ l.val := by
        by_contra hl
        rw [spABlk_inl, spABlk_inr, ite_eq_right (by omega), ite_eq_left (by omega)] at hrt
        exact absurd hrt (by decide)
      have hBC : ((1 + B) * C) k l = C k l := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
          Finset.sum_eq_zero (fun m _ => by rw [hB.apply_eq_zero hk, zero_mul]), add_zero]
      rw [fromBlocks_apply₁₂, hBC, hCi k l hk hl]
      simp
    · simp
    · have hB0 : B l k = 0 := by
        by_contra h
        have h' := hB l k h
        simp [h'.1, show ¬ k.val < 2 * j by omega] at hrt
      simp [Matrix.sub_apply, hB0, Matrix.one_apply]
  · exact (Matrix.one_apply_ne (fun h => hrt (by rw [h]))).symm

theorem spARadElt_mem_spARadical (hjn : 2 * j ≤ n) (hB : SpAOff j B) (hC : Cᵀ = C)
    (hCi : SpAInner j C) : spARadElt hB hC ∈ spARadical K n j hjn := by
  refine (mem_spARadical_iff hjn).2 ⟨spARadElt_mem_centralizer hB hC, mat_injective ?_⟩
  rw [mat_spALeviHom, spALeviPart_spARadElt hB hC hCi, map_one]

theorem spARadElt_congr {B' C' : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) (hC : Cᵀ = C)
    (hB' : SpAOff j B') (hC' : C'ᵀ = C') (h1 : B = B') (h2 : C = C') :
    spARadElt hB hC = spARadElt hB' hC' := by
  subst h1 h2
  rfl

theorem eq_of_spARadElt_eq {B' C' : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) (hC : Cᵀ = C)
    (hB' : SpAOff j B') (hC' : C'ᵀ = C') (h : spARadElt hB hC = spARadElt hB' hC') :
    B = B' ∧ C = C' := by
  have h' := congrArg (mat n K) h
  rw [mat_spARadElt, mat_spARadElt, fromBlocks_inj] at h'
  obtain ⟨h1, h2, -, -⟩ := h'
  have hBB : B = B' := add_left_cancel h1
  refine ⟨hBB, ?_⟩
  subst hBB
  have e : (1 - B) * ((1 + B) * C) = C := by
    rw [← Matrix.mul_assoc, ← coe_spAOffUnit_inv hB, ← coe_spAOffUnit hB, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have e' : (1 - B) * ((1 + B) * C') = C' := by
    rw [← Matrix.mul_assoc, ← coe_spAOffUnit_inv hB, ← coe_spAOffUnit hB, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [← e, h2, e']

end Elt

section Structure

variable (hjn : 2 * j ≤ n)
include hjn

theorem exists_spARadElt_of_mem {x : StatedSp n K} (hx : x ∈ spARadical K n j hjn) :
    ∃ (B : Matrix (Fin n) (Fin n) K) (hB : SpAOff j B) (C : Matrix (Fin n) (Fin n) K)
      (hC : Cᵀ = C), SpAInner j C ∧ x = spARadElt hB hC := by
  obtain ⟨hxC, h1⟩ := (mem_spARadical_iff hjn).1 hx
  have hc := spABlockCond_of_mem hjn hxC
  have hL : spALeviPart j (mat n K x) = 1 := by
    have := congrArg (mat n K) h1
    rwa [mat_spALeviHom, map_one] at this
  have hL' : ∀ r t, spABlk j r = spABlk j t →
      mat n K x r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := by
    intro r t h
    have e := congrFun (congrFun hL r) t
    rwa [spALeviPart_apply, ite_eq_left h] at e
  have h21 : (mat n K x).toBlocks₂₁ = 0 := by
    ext k l
    rw [toBlocks₂₁, of_apply, Matrix.zero_apply]
    by_cases hk : k.val < 2 * j
    · exact hc.2 (Sum.inr k) (Sum.inl l) (by simp [hk])
        (by by_cases hl : l.val < 2 * j <;> simp [hl])
    · by_cases hl : l.val < 2 * j
      · exact hc.1 (Sum.inr k) (Sum.inl l) (by simp [hl]) (by simp [hk])
      · rw [hL' _ _ (by simp [hk, hl])]
        simp
  rw [mat_apply] at h21
  obtain ⟨hdet, C, hC, hxe⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_blockMat_of_toBlocks₂₁_eq_zero h21
  rw [← mat_apply] at hxe
  set A := (mat n K x).toBlocks₁₁ with hA
  have hAe : ∀ k l, A k l = mat n K x (Sum.inl k) (Sum.inl l) := fun _ _ => rfl
  set B := A - 1 with hBdef
  have hB : SpAOff j B := by
    intro k l hkl
    rw [hBdef, Matrix.sub_apply, hAe] at hkl
    by_contra hcon
    apply hkl
    by_cases hb : spABlk j (Sum.inl k : Fin n ⊕ Fin n) = spABlk j (Sum.inl l)
    · rw [hL' _ _ hb]
      simp [Matrix.one_apply]
    · have hk : 2 * j ≤ k.val := by
        by_contra hk
        have hl : 2 * j ≤ l.val := by
          by_contra hl
          exact hb (by simp [show k.val < 2 * j by omega, show l.val < 2 * j by omega])
        exact hcon ⟨by omega, hl⟩
      have hl : l.val < 2 * j := by
        by_contra hl
        exact hb (by simp [show ¬ k.val < 2 * j by omega, hl])
      have hkl' : k ≠ l := fun h => by subst h; omega
      rw [hc.1 (Sum.inl k) (Sum.inl l) (by simp [hl]) (by simp [show ¬ k.val < 2 * j by omega]),
        Matrix.one_apply_ne hkl', sub_zero]
  have hAB : A = 1 + B := by rw [hBdef, add_sub_cancel]
  have hCi : SpAInner j C := by
    intro k l hk hl
    have e1 : mat n K x (Sum.inl k) (Sum.inr l) = 0 := by
      rw [hL' _ _ (by simp [show ¬ k.val < 2 * j by omega, show ¬ l.val < 2 * j by omega])]
      simp
    have e2 : mat n K x (Sum.inl k) (Sum.inr l) = (A * C) k l := by
      rw [hxe]
      rfl
    rw [e2, hAB, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
      Finset.sum_eq_zero (fun m _ => by rw [hB.apply_eq_zero hk, zero_mul]), add_zero] at e1
    exact e1
  refine ⟨B, hB, C, hC, hCi, mat_injective ?_⟩
  rw [mat_spARadElt, hxe, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.blockMat, hAB]
  congr 1
  have hinv : (1 + B)⁻¹ = 1 - B := by
    rw [← coe_spAOffUnit hB, ← coe_spAOffUnit_inv hB, ← Matrix.coe_units_inv]
  rw [hinv, transpose_sub, transpose_one]

end Structure

section Order

abbrev SpAPairs (n j : ℕ) := {p : Fin n × Fin n // p.1.val < 2 * j ∧ 2 * j ≤ p.2.val}

@[expose] def spAPairsEquiv : SpAPairs n j ≃ Fin (2 * j) × Fin (n - 2 * j) where
  toFun p := (⟨p.1.1.val, p.2.1⟩,
    ⟨p.1.2.val - 2 * j, by have := p.1.2.isLt; have := p.2.2; omega⟩)
  invFun q := ⟨(⟨q.1.val, by have := q.1.isLt; have := q.2.isLt; omega⟩,
    ⟨q.2.val + 2 * j, by have := q.2.isLt; omega⟩), q.1.isLt, by simp⟩
  left_inv p := Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext (by dsimp; have := p.2.2; omega)))
  right_inv q := Prod.ext (Fin.ext rfl) (Fin.ext (by dsimp; omega))

theorem card_spAPairs : Nat.card (SpAPairs n j) = 2 * j * (n - 2 * j) := by
  rw [Nat.card_congr spAPairsEquiv, Nat.card_prod, Nat.card_fin, Nat.card_fin]

@[expose] def spAOffMat (b : SpAPairs n j → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun k l => if h : k.val < 2 * j ∧ 2 * j ≤ l.val then b ⟨(k, l), h⟩ else 0

theorem spAOffMat_spAOff (b : SpAPairs n j → K) : SpAOff j (spAOffMat b) := by
  intro k l h
  by_contra h'
  apply h
  rw [spAOffMat, of_apply, dite_eq_right h']

@[expose] def spAInnerMat (c : SpAPairs n j → K) (S : Matrix (Fin (2 * j)) (Fin (2 * j)) K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun k l =>
    if h : k.val < 2 * j ∧ l.val < 2 * j then S ⟨k.val, h.1⟩ ⟨l.val, h.2⟩
    else if h' : k.val < 2 * j ∧ 2 * j ≤ l.val then c ⟨(k, l), h'⟩
    else if h'' : l.val < 2 * j ∧ 2 * j ≤ k.val then c ⟨(l, k), h''⟩ else 0

theorem spAInnerMat_transpose (c : SpAPairs n j → K) {S : Matrix (Fin (2 * j)) (Fin (2 * j)) K}
    (hS : Sᵀ = S) : (spAInnerMat c S)ᵀ = spAInnerMat c S := by
  ext k l
  rw [transpose_apply, spAInnerMat, of_apply, of_apply]
  by_cases h1 : k.val < 2 * j <;> by_cases h2 : l.val < 2 * j
  · rw [dite_eq_left ⟨h2, h1⟩, dite_eq_left ⟨h1, h2⟩]
    have := congrFun (congrFun hS ⟨k.val, h1⟩) ⟨l.val, h2⟩
    rwa [transpose_apply] at this
  · simp [h1, h2, show 2 * j ≤ l.val by omega]
  · simp [h1, h2, show 2 * j ≤ k.val by omega]
  · simp [h1, h2]

theorem spAInnerMat_inner (c : SpAPairs n j → K) (S : Matrix (Fin (2 * j)) (Fin (2 * j)) K) :
    SpAInner j (spAInnerMat c S) := by
  intro k l hk hl
  simp [spAInnerMat, show ¬ k.val < 2 * j by omega, show ¬ l.val < 2 * j by omega]

variable (K n j) in
abbrev SpARadParams :=
  (SpAPairs n j → K) × (SpAPairs n j → K) × {S : Matrix (Fin (2 * j)) (Fin (2 * j)) K // Sᵀ = S}

@[expose] noncomputable def spARadParam (hjn : 2 * j ≤ n) (p : SpARadParams K n j) :
    spARadical K n j hjn :=
  ⟨spARadElt (spAOffMat_spAOff p.1) (spAInnerMat_transpose p.2.1 p.2.2.2),
    spARadElt_mem_spARadical hjn _ _ (spAInnerMat_inner _ _)⟩

theorem spARadParam_bijective (hjn : 2 * j ≤ n) :
    Function.Bijective (spARadParam (K := K) hjn) := by
  refine ⟨fun p p' h => ?_, fun x => ?_⟩
  · obtain ⟨hB, hC⟩ := eq_of_spARadElt_eq _ _ _ _ (congrArg Subtype.val h)
    obtain ⟨b, c, S, hS⟩ := p
    obtain ⟨b', c', S', hS'⟩ := p'
    have e1 : b = b' := funext fun q => by
      have := congrFun (congrFun hB q.1.1) q.1.2
      simpa [spAOffMat, q.2] using this
    have e2 : c = c' := funext fun q => by
      have := congrFun (congrFun hC q.1.1) q.1.2
      have hq : ¬ q.1.2.val < 2 * j := by have := q.2.2; omega
      simpa [spAInnerMat, hq, q.2.1, q.2.2] using this
    have e3 : S = S' := by
      ext k l
      have := congrFun (congrFun hC ⟨k.val, by omega⟩) ⟨l.val, by omega⟩
      simpa [spAInnerMat] using this
    subst e1 e2 e3
    rfl
  · obtain ⟨B, hB, C, hC, hCi, hx⟩ := exists_spARadElt_of_mem hjn x.2
    refine ⟨(fun q => B q.1.1 q.1.2, fun q => C q.1.1 q.1.2,
      ⟨fun k l => C ⟨k.val, by omega⟩ ⟨l.val, by omega⟩, ?_⟩), Subtype.ext ?_⟩
    · ext k l
      exact congrFun (congrFun hC _) _
    · rw [hx]
      refine spARadElt_congr _ _ _ _ ?_ ?_
      · ext k l
        rw [spAOffMat, of_apply]
        split_ifs with h
        · rfl
        · by_contra h'
          exact h (hB k l (Ne.symm h'))
      · ext k l
        rw [spAInnerMat, of_apply]
        split_ifs with h1 h2 h3
        · rfl
        · rfl
        · exact congrFun (congrFun hC k) l
        · have hk : 2 * j ≤ k.val := by omega
          have hl : 2 * j ≤ l.val := by omega
          exact (hCi k l hk hl).symm

theorem card_spARadical [Finite K] (hjn : 2 * j ≤ n) :
    Nat.card (spARadical K n j hjn) =
      Nat.card K ^ (2 * (2 * j * (n - 2 * j)) + j * (2 * j + 1)) := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (spARadParam_bijective (K := K) hjn)),
    Nat.card_prod, Nat.card_prod, Nat.card_fun, card_spAPairs,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_symmetric,
    show 2 * j * (2 * j + 1) / 2 = j * (2 * j + 1) by
      rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ two_pos], ← pow_add, ← pow_add]
  ring_nf

end Order

end CFSG.SeitzReduction.SymplecticPilot
