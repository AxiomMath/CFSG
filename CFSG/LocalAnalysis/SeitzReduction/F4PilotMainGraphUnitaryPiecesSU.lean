module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryModel
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear blockEmbed
  blockMatrix blockMatrix_apply coe_blockEmbed blockEmbed_injective range_blockEmbed
  det_blockMatrix)

section PermGram

variable {n : ℕ} {F : Type*} [Field F]

structure IsPermGram (C : Matrix (Fin n) (Fin n) F) (π : Fin n → Fin n) : Prop where
  invol : Function.Involutive π
  apply : ∀ i j, C i j = if π i = j then 1 else 0

variable {C : Matrix (Fin n) (Fin n) F} {π : Fin n → Fin n}

theorem IsPermGram.mul_apply_left (hC : IsPermGram C π) (Y : Matrix (Fin n) (Fin n) F)
    (i l : Fin n) : (C * Y) i l = Y (π i) l := by
  rw [mul_apply]
  simp only [hC.apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

theorem IsPermGram.mul_apply_right (hC : IsPermGram C π) (Y : Matrix (Fin n) (Fin n) F)
    (k j : Fin n) : (Y * C) k j = Y k (π j) := by
  rw [mul_apply]
  simp only [hC.apply, hC.invol.eq_iff, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]

theorem IsPermGram.conj_apply (hC : IsPermGram C π) (Y : Matrix (Fin n) (Fin n) F)
    (i j : Fin n) : (C * Y * C) i j = Y (π i) (π j) := by
  rw [hC.mul_apply_right, hC.mul_apply_left]

theorem IsPermGram.mul_self (hC : IsPermGram C π) : C * C = 1 := by
  ext i j
  rw [hC.mul_apply_left, hC.apply, hC.invol, one_apply]

theorem IsPermGram.transpose_eq (hC : IsPermGram C π) : Cᵀ = C := by
  ext i j
  rw [transpose_apply, hC.apply, hC.apply]
  exact if_congr (hC.invol.eq_iff.trans eq_comm) rfl rfl

theorem IsPermGram.map_eq (hC : IsPermGram C π) (σ : F →+* F) : C.map σ = C := by
  ext i j
  rw [map_apply, hC.apply]
  split_ifs <;> simp

theorem IsPermGram.hermitian {p f : ℕ} {K : Type} [Field K] {C : Matrix (Fin n) (Fin n) K}
    (hC : IsPermGram C π) (h : UnitaryFieldData p f K) : (C.map h.bar)ᵀ = C := by
  rw [hC.map_eq, hC.transpose_eq]

theorem IsPermGram.apply_eq_zero (hC : IsPermGram C π) {I : Finset (Fin n)}
    (hI : ∀ i, i ∈ I ↔ π i ∈ I) {i j : Fin n} (hij : i ∈ I ↔ j ∉ I) : C i j = 0 := by
  rw [hC.apply, ite_eq_right]
  rintro rfl
  rw [← hI] at hij
  tauto

end PermGram

section GramSL

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F) {ι : Type*} [Fintype ι]
  [DecidableEq ι]

@[expose] def uPieceGramToSL (G : Matrix ι ι F) : gramSU h G →* SpecialLinearGroup ι F where
  toFun g := ⟨((g : GL ι F) : Matrix ι ι F), g.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem uPieceGramToSL_injective (G : Matrix ι ι F) : Function.Injective (uPieceGramToSL h G) :=
  fun _ _ hgg' => Subtype.ext (Units.ext (congrArg
    (fun x : SpecialLinearGroup ι F => (x : Matrix ι ι F)) hgg'))

theorem uPiece_cast_ordSU {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    ((ordSU m q : ℕ) : ℤ) =
      (q : ℤ) ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 2 m, ((q : ℤ) ^ i - (-1) ^ i) := by
  rw [ordSU, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one,
      Even.neg_one_pow (Nat.even_iff.2 hi)]
  · rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, Odd.neg_one_pow (Nat.odd_iff.2 (by omega))]
    ring

theorem uPiece_natCard_gramSU {G : Matrix ι ι F} (hG : (G.map h.bar)ᵀ = G) (hdet : G.det ≠ 0)
    (hι : 1 ≤ Fintype.card ι) : Nat.card (gramSU h G) = ordSU (Fintype.card ι) (p ^ f) := by
  rw [card_gramSU]
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have h1 := (CFSG.LinearGroups.unitary_full_group_order h (gramForm_isSymm h hG)
    (gramForm_separatingLeft h hdet) (Module.finrank_fintype_fun_eq_card F) hι).2.1
  rw [← uPiece_cast_ordSU hq] at h1
  exact_mod_cast h1

theorem uPiece_isPerfect_gramSU {G : Matrix ι ι F} (hG : (G.map h.bar)ᵀ = G) (hdet : G.det ≠ 0)
    (hι : 2 ≤ Fintype.card ι)
    (hq : (Fintype.card ι = 2 → 4 ≤ p ^ f) ∧ (Fintype.card ι = 3 → 3 ≤ p ^ f)) :
    Group.IsPerfect (gramSU h G) := by
  have hfin : Module.finrank F (ι → F) = Fintype.card ι := Module.finrank_fintype_fun_eq_card F
  have hQ := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le h
    (gramForm_isSymm h hG) (gramForm_separatingLeft h hdet) (hfin ▸ hι) (hfin ▸ hq)
  obtain ⟨φ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h
    (Pi.basisFun F ι) (G := G) (fun i j => by
      rw [Pi.basisFun_apply, Pi.basisFun_apply, gramForm_single])
  have := hQ.1
  exact Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective

end GramSL

section Block

variable {p f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
  {C : Matrix (Fin n) (Fin n) F} {I : Finset (Fin n)}

theorem uPiece_submatrix_sumCompl (hCI : ∀ i j, (i ∈ I ↔ j ∉ I) → C i j = 0) :
    C.submatrix (Equiv.sumCompl (· ∈ I)) (Equiv.sumCompl (· ∈ I)) =
      fromBlocks (C.submatrix (Subtype.val : I → Fin n) Subtype.val) 0 0
        (C.submatrix (Subtype.val : {i // i ∉ I} → Fin n) Subtype.val) := by
  ext (a | a) (b | b)
  · rfl
  · exact hCI _ _ (iff_of_true a.2 b.2)
  · exact hCI _ _ (iff_of_false a.2 (not_not.2 b.2))
  · rfl

theorem uPiece_submatrix_conj {κ : Type*} [Fintype κ] (e : κ ≃ Fin n)
    (X : Matrix (Fin n) (Fin n) F) :
    ((X.map h.bar)ᵀ * C * X).submatrix e e =
      ((X.submatrix e e).map h.bar)ᵀ * C.submatrix e e * X.submatrix e e := by
  rw [← submatrix_mul_equiv _ _ _ e, ← submatrix_mul_equiv _ _ _ e, ← submatrix_map,
    transpose_submatrix]

theorem uPiece_blockMatrix_unitary_iff (hCI : ∀ i j, (i ∈ I ↔ j ∉ I) → C i j = 0)
    (A : Matrix I I F) :
    ((blockMatrix I A).map h.bar)ᵀ * C * blockMatrix I A = C ↔
      (A.map h.bar)ᵀ * C.submatrix (Subtype.val : I → Fin n) Subtype.val * A =
        C.submatrix (Subtype.val : I → Fin n) Subtype.val := by
  set e := Equiv.sumCompl (· ∈ I)
  have hb : (blockMatrix I A).submatrix e e = fromBlocks A 0 0 1 := by
    simp [e, blockMatrix, reindex_apply, submatrix_submatrix]
  rw [← (reindex e.symm e.symm).injective.eq_iff, reindex_apply, reindex_apply, Equiv.symm_symm,
    uPiece_submatrix_conj, hb, uPiece_submatrix_sumCompl hCI]
  simp only [fromBlocks_map, Matrix.map_zero _ (map_zero h.bar),
    Matrix.map_one _ (map_zero h.bar) (map_one h.bar), fromBlocks_transpose, transpose_zero,
    transpose_one, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_one, add_zero, zero_add, fromBlocks_inj, and_true]

theorem uPiece_range_inf_blockSpecialLinear (hCI : ∀ i j, (i ∈ I ↔ j ∉ I) → C i j = 0) :
    (gramSUToSL h C).range ⊓ blockSpecialLinear I =
      ((blockEmbed I).comp
        (uPieceGramToSL h (C.submatrix (Subtype.val : I → Fin n) Subtype.val))).range := by
  apply le_antisymm
  · rintro x ⟨⟨g, rfl⟩, hx⟩
    rw [← range_blockEmbed] at hx
    obtain ⟨B, hB⟩ := hx
    have hgB : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        blockMatrix I (B : Matrix I I F) := by
      rw [← coe_gramSUToSL h C g, ← hB, coe_blockEmbed]
    have hBu := (uPiece_blockMatrix_unitary_iff h hCI (B : Matrix I I F)).1
      (by rw [← hgB]; exact g.2.1)
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL B, hBu, B.2⟩, ?_⟩
    rw [MonoidHom.comp_apply, ← hB]
    rfl
  · rintro _ ⟨A, rfl⟩
    refine ⟨?_, ?_⟩
    · set x := blockEmbed I (uPieceGramToSL h _ A)
      have hx : (Matrix.SpecialLinearGroup.toGL x : GL (Fin n) F) ∈ gramSU h C := by
        refine ⟨?_, x.2⟩
        exact (uPiece_blockMatrix_unitary_iff h hCI _).2 A.2.1
      exact ⟨⟨_, hx⟩, rfl⟩
    · rw [← range_blockEmbed]
      exact ⟨_, rfl⟩

theorem uPiece_natCard_range_inf_blockSpecialLinear
    (hCI : ∀ i j, (i ∈ I ↔ j ∉ I) → C i j = 0) :
    Nat.card ((gramSUToSL h C).range ⊓ blockSpecialLinear I : Subgroup _) =
      Nat.card (gramSU h (C.submatrix (Subtype.val : I → Fin n) Subtype.val)) := by
  rw [uPiece_range_inf_blockSpecialLinear h hCI]
  have hinj : Function.Injective ((blockEmbed (K := F) I).comp
      (uPieceGramToSL h (C.submatrix (Subtype.val : I → Fin n) Subtype.val))) :=
    fun a b hab => uPieceGramToSL_injective h _ (blockEmbed_injective I hab)
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem uPiece_commutator_range_inf_blockSpecialLinear
    (hCI : ∀ i j, (i ∈ I ↔ j ∉ I) → C i j = 0)
    (hperf : Group.IsPerfect (gramSU h (C.submatrix (Subtype.val : I → Fin n) Subtype.val))) :
    ⁅(gramSUToSL h C).range ⊓ blockSpecialLinear I,
      (gramSUToSL h C).range ⊓ blockSpecialLinear I⁆ =
        (gramSUToSL h C).range ⊓ blockSpecialLinear I := by
  rw [uPiece_range_inf_blockSpecialLinear h hCI, ← isPerfect_iff]
  exact Group.IsPerfect.range _

omit h in
theorem IsPermGram.submatrix_mul_self {π : Fin n → Fin n} (hC : IsPermGram C π)
    (hI : ∀ i, i ∈ I ↔ π i ∈ I) :
    C.submatrix (Subtype.val : I → Fin n) (Subtype.val : I → Fin n) *
      C.submatrix (Subtype.val : I → Fin n) (Subtype.val : I → Fin n) = 1 := by
  have hCI : ∀ i j, (i ∈ I ↔ j ∉ I) → C i j = 0 := fun i j hij => hC.apply_eq_zero hI hij
  have h1 := congrArg
    (fun X => X.submatrix (Equiv.sumCompl (· ∈ I)) (Equiv.sumCompl (· ∈ I))) hC.mul_self
  simp only at h1
  rw [← submatrix_mul_equiv _ _ _ (Equiv.sumCompl (· ∈ I)), uPiece_submatrix_sumCompl hCI,
    fromBlocks_multiply, submatrix_one_equiv, ← fromBlocks_one, fromBlocks_inj] at h1
  simpa using h1.1

omit h in
theorem IsPermGram.det_submatrix_ne_zero {π : Fin n → Fin n} (hC : IsPermGram C π)
    (hI : ∀ i, i ∈ I ↔ π i ∈ I) :
    (C.submatrix (Subtype.val : I → Fin n) Subtype.val).det ≠ 0 := by
  intro h0
  have h1 := congrArg det (hC.submatrix_mul_self hI)
  rw [det_mul, h0, zero_mul, det_one] at h1
  exact zero_ne_one h1

theorem IsPermGram.hermitian_submatrix {π : Fin n → Fin n} (hC : IsPermGram C π) :
    ((C.submatrix (Subtype.val : I → Fin n) Subtype.val).map h.bar)ᵀ =
      C.submatrix (Subtype.val : I → Fin n) Subtype.val := by
  rw [← submatrix_map, transpose_submatrix, hC.hermitian h]

theorem IsPermGram.natCard_and_commutator_range_inf_blockSpecialLinear {π : Fin n → Fin n}
    (hC : IsPermGram C π) (hI : ∀ i, i ∈ I ↔ π i ∈ I) (hI2 : 2 ≤ I.card)
    (hq : (I.card = 2 → 4 ≤ p ^ f) ∧ (I.card = 3 → 3 ≤ p ^ f)) :
    Nat.card ((gramSUToSL h C).range ⊓ blockSpecialLinear I : Subgroup _) =
        ordSU I.card (p ^ f) ∧
      ⁅(gramSUToSL h C).range ⊓ blockSpecialLinear I,
        (gramSUToSL h C).range ⊓ blockSpecialLinear I⁆ =
          (gramSUToSL h C).range ⊓ blockSpecialLinear I := by
  have hCI : ∀ i j, (i ∈ I ↔ j ∉ I) → C i j = 0 := fun i j hij => hC.apply_eq_zero hI hij
  have hcard : Fintype.card I = I.card := Fintype.card_coe I
  refine ⟨?_, uPiece_commutator_range_inf_blockSpecialLinear h hCI ?_⟩
  · rw [uPiece_natCard_range_inf_blockSpecialLinear h hCI,
      uPiece_natCard_gramSU h (hC.hermitian_submatrix h) (hC.det_submatrix_ne_zero hI)
        (by omega), hcard]
  · exact uPiece_isPerfect_gramSU h (hC.hermitian_submatrix h) (hC.det_submatrix_ne_zero hI)
      (by omega) (by rw [hcard]; exact hq)

end Block

end CFSG.SeitzReduction.F4Pilot
