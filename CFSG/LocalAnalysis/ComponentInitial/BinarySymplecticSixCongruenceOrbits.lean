module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixLagrangianSylow

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix

theorem card_image_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) : (Finset.univ.image A.mulVec).card = 2 ^ A.rank := by
  have h1 : (Finset.univ.image A.mulVec).card = Nat.card (Set.range A.mulVec) := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_range]
  have h2 : Set.range A.mulVec = (LinearMap.range A.mulVecLin : Set (ι → ZMod 2)) := by
    rw [LinearMap.coe_range, coe_mulVecLin]
  have hfin : Module.Finite (ZMod 2) (LinearMap.range A.mulVecLin) := Module.Finite.range _
  have h3 := @Module.natCard_eq_pow_finrank (ZMod 2) (LinearMap.range A.mulVecLin) _
    (Submodule.addCommGroup _) (Submodule.module _) hfin
  rw [h1, h2, SetLike.coe_sort_coe, h3, Nat.card_zmod]
  rfl

theorem rank_eq_iff_card_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) (r : ℕ) :
    A.rank = r ↔ (Finset.univ.image A.mulVec).card = 2 ^ r := by
  rw [card_image_mulVec]
  exact (Nat.pow_right_injective le_rfl).eq_iff.symm

theorem rank_congr_three (D : GL (Fin 3) (ZMod 2)) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ((D : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B * (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ).rank =
      B.rank := by
  have hD : IsUnit (D : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
  have hDt : IsUnit (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ.det := by rwa [det_transpose]
  rw [Matrix.mul_assoc, rank_mul_eq_right_of_isUnit_det _ _ hD,
    rank_mul_eq_left_of_isUnit_det _ _ hDt]

@[expose] def altBits (x : SixBits) : Prop :=
  x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0

instance : DecidablePred altBits := fun _ => inferInstanceAs (Decidable (_ ∧ _))

@[expose] def rkBits (x : SixBits) : ℕ :=
  (Finset.univ.image (symMat x).mulVec).card

theorem symMat_transpose (x : SixBits) : (symMat x)ᵀ = symMat x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem symCoord_symMat (x : SixBits) : symCoord (symMat x) = x :=
  rfl

theorem rank_symMat_eq_iff (x : SixBits) (r : ℕ) : (symMat x).rank = r ↔ rkBits x = 2 ^ r :=
  rank_eq_iff_card_image _ r

theorem altBits_iff (x : SixBits) : altBits x ↔ ∀ i, symMat x i i = 0 := by
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    exacts [h0, h1, h2]
  · intro h
    exact ⟨h 0, h 1, h 2⟩

@[expose] def symEquiv : binarySymMatrices 3 ≃ SixBits where
  toFun B := symCoord B
  invFun x := ⟨symMat x, symMat_transpose x⟩
  left_inv B := Subtype.ext (symMat_symCoord B.2)
  right_inv x := symCoord_symMat x

theorem symMat_symEquiv (B : binarySymMatrices 3) :
    symMat (symEquiv B) = (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  symMat_symCoord B.2

@[expose] def congrBits (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : SixBits) : SixBits :=
  symCoord (D * symMat x * Dᵀ)

theorem symMat_congrBits (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : SixBits) :
    symMat (congrBits D x) = D * symMat x * Dᵀ :=
  symMat_symCoord (by
    rw [transpose_mul, transpose_mul, transpose_transpose, symMat_transpose, Matrix.mul_assoc])

@[expose] def elemList : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 1, 0; 0, 0, 1],
    !![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 1, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 1, 1]]

theorem elemList_mul_self : ∀ g ∈ elemList, g * g = 1 := by
  intro g hg
  simp only [elemList, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

@[expose] def congrStep (S : Finset SixBits) : Finset SixBits :=
  S ∪ S.biUnion fun x => (elemList.map fun g => congrBits g x).toFinset

theorem mem_congrStep {S : Finset SixBits} {x : SixBits} :
    x ∈ congrStep S ↔ x ∈ S ∨ ∃ y ∈ S, ∃ g ∈ elemList, congrBits g y = x := by
  unfold congrStep
  simp only [Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_map]

attribute [irreducible] congrStep

theorem exists_congr_of_mem_iterate (x₀ : SixBits) :
    ∀ (k : ℕ) (x : SixBits), x ∈ congrStep^[k] {x₀} →
      ∃ D : GL (Fin 3) (ZMod 2),
        (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) * symMat x₀ *
          (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = symMat x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [Function.iterate_zero, id, Finset.mem_singleton] at hx
    exact ⟨1, by rw [hx, Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]⟩
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply', mem_congrStep] at hx
    rcases hx with hx | ⟨y, hy, g, hg, rfl⟩
    · exact ih x hx
    obtain ⟨D, hD⟩ := ih y hy
    have hgg := elemList_mul_self g hg
    refine ⟨⟨g, g, hgg, hgg⟩ * D, ?_⟩
    rw [symMat_congrBits, ← hD, Units.val_mul, transpose_mul]
    simp only [Matrix.mul_assoc]

@[expose] def orbitBits (x₀ : SixBits) : Finset SixBits :=
  congrStep^[4] {x₀}

@[expose] def repZero : SixBits := (0, 0, 0, 0, 0, 0)

@[expose] def repOne : SixBits := (1, 0, 0, 0, 0, 0)

@[expose] def repAlt : SixBits := (0, 0, 0, 0, 1, 0)

@[expose] def repNonalt : SixBits := (1, 0, 0, 1, 0, 0)

@[expose] def repThree : SixBits := (1, 1, 1, 0, 0, 0)

@[expose] def orbitRep (x : SixBits) : SixBits :=
  if rkBits x = 4 then (if altBits x then repAlt else repNonalt)
  else if rkBits x = 1 then repZero
  else if rkBits x = 2 then repOne
  else repThree

attribute [irreducible] rkBits orbitBits

theorem subset_orbit_one :
    (Finset.univ.filter fun x : SixBits => rkBits x = 1) ⊆ orbitBits repZero := by
  decide +kernel

theorem subset_orbit_two :
    (Finset.univ.filter fun x : SixBits => rkBits x = 2) ⊆ orbitBits repOne := by
  decide +kernel

theorem subset_orbit_four_alt :
    (Finset.univ.filter fun x : SixBits => rkBits x = 4 ∧ altBits x) ⊆ orbitBits repAlt := by
  decide +kernel

theorem subset_orbit_four_nonalt :
    (Finset.univ.filter fun x : SixBits => rkBits x = 4 ∧ ¬ altBits x) ⊆ orbitBits repNonalt := by
  decide +kernel

theorem subset_orbit_eight :
    (Finset.univ.filter fun x : SixBits => rkBits x = 8) ⊆ orbitBits repThree := by
  decide +kernel

theorem rkBits_mem : (Finset.univ.filter fun x : SixBits =>
    rkBits x = 1 ∨ rkBits x = 2 ∨ rkBits x = 4 ∨ rkBits x = 8) = Finset.univ := by
  decide +kernel

theorem mem_orbitRep (x : SixBits) : x ∈ orbitBits (orbitRep x) := by
  have hx := Finset.mem_filter.1 (Finset.eq_univ_iff_forall.1 rkBits_mem x)
  unfold orbitRep
  rcases hx.2 with h | h | h | h
  · rw [ite_eq_right (by omega), ite_eq_left h]
    exact subset_orbit_one (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
    exact subset_orbit_two (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  · rw [ite_eq_left h]
    by_cases ha : altBits x
    · rw [ite_eq_left ha]
      exact subset_orbit_four_alt (Finset.mem_filter.2 ⟨Finset.mem_univ _, h, ha⟩)
    · rw [ite_eq_right ha]
      exact subset_orbit_four_nonalt (Finset.mem_filter.2 ⟨Finset.mem_univ _, h, ha⟩)
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact subset_orbit_eight (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

theorem exists_congr_orbitRep (x : SixBits) :
    ∃ D : GL (Fin 3) (ZMod 2), (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) * symMat (orbitRep x) *
      (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = symMat x := by
  have h := mem_orbitRep x
  unfold orbitBits at h
  exact exists_congr_of_mem_iterate _ 4 x h

theorem altBits_iff_dotProduct : ∀ x : SixBits,
    altBits x ↔ ∀ v : Fin 3 → ZMod 2, v ⬝ᵥ (symMat x *ᵥ v) = 0 := by
  decide

theorem dotProduct_congr (D B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    v ⬝ᵥ ((D * B * Dᵀ) *ᵥ v) = (Dᵀ *ᵥ v) ⬝ᵥ (B *ᵥ (Dᵀ *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]

theorem altBits_congrBits (D : GL (Fin 3) (ZMod 2)) {x : SixBits} (hx : altBits x) :
    altBits (congrBits (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) x) := by
  rw [altBits_iff_dotProduct] at hx ⊢
  intro v
  rw [symMat_congrBits, dotProduct_congr]
  exact hx _

theorem congrBits_inv (D : GL (Fin 3) (ZMod 2)) (x : SixBits) :
    congrBits ((D⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      (congrBits (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) x) = x := by
  apply_fun symMat using fun a b h => by rw [← symCoord_symMat a, h, symCoord_symMat]
  rw [symMat_congrBits, symMat_congrBits, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
    ← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one,
    Matrix.mul_one]

theorem rkBits_symEquiv_eq_iff (B : binarySymMatrices 3) (r : ℕ) :
    rkBits (symEquiv B) = 2 ^ r ↔ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = r := by
  rw [← rank_symMat_eq_iff, symMat_symEquiv]

theorem altBits_symEquiv_iff (B : binarySymMatrices 3) :
    altBits (symEquiv B) ↔ ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0 := by
  rw [altBits_iff, symMat_symEquiv]

theorem symEquiv_congr (D : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3) :
    symMat (congrBits (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) (symEquiv B)) =
      (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := by
  rw [symMat_congrBits, symMat_symEquiv]

theorem orbitRep_eq {x y : SixBits} (hr : rkBits x = rkBits y)
    (ha : rkBits x = 4 → (altBits x ↔ altBits y)) : orbitRep x = orbitRep y := by
  unfold orbitRep
  rw [← hr]
  by_cases h4 : rkBits x = 4
  · have hxy := ha h4
    rw [ite_eq_left h4, ite_eq_left h4]
    by_cases hx : altBits x
    · rw [ite_eq_left hx, ite_eq_left (hxy.1 hx)]
    · rw [ite_eq_right hx, ite_eq_right (fun hy => hx (hxy.2 hy))]
  · rw [ite_eq_right h4, ite_eq_right h4]

theorem sym_congruent_iff (B B' : binarySymMatrices 3) :
    (∃ D : GL (Fin 3) (ZMod 2), (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = B') ↔
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ∧
        ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 →
          ((∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ↔
            ∀ i, (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0)) := by
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨by rw [← hD, rank_congr_three], fun _ => ?_⟩
    rw [← altBits_symEquiv_iff, ← altBits_symEquiv_iff]
    have hB' : congrBits (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) (symEquiv B) = symEquiv B' := by
      apply symEquiv.symm.injective
      rw [Equiv.symm_apply_apply]
      exact Subtype.ext ((symEquiv_congr D B).trans hD)
    constructor
    · intro h
      rw [← hB']
      exact altBits_congrBits D h
    · intro h
      rw [← congrBits_inv D (symEquiv B), hB']
      exact altBits_congrBits D⁻¹ h
  · rintro ⟨hr, ha⟩
    have hr' : rkBits (symEquiv B) = rkBits (symEquiv B') := by
      rw [(rkBits_symEquiv_eq_iff B _).2 rfl, (rkBits_symEquiv_eq_iff B' _).2 hr.symm]
    have ha' : rkBits (symEquiv B) = 4 → (altBits (symEquiv B) ↔ altBits (symEquiv B')) :=
      fun h4 => by
        rw [altBits_symEquiv_iff, altBits_symEquiv_iff]
        exact ha ((rkBits_symEquiv_eq_iff B 2).1 h4)
    obtain ⟨D, hD⟩ := exists_congr_orbitRep (symEquiv B)
    obtain ⟨D', hD'⟩ := exists_congr_orbitRep (symEquiv B')
    rw [orbitRep_eq hr' ha', symMat_symEquiv] at hD
    rw [symMat_symEquiv] at hD'
    refine ⟨D' * D⁻¹, ?_⟩
    rw [← hD', ← hD, Units.val_mul, transpose_mul]
    have h1 : ((D⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
        ((D⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = 1 := by
      rw [← transpose_mul, h1, transpose_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (D⁻¹ : GL (Fin 3) (ZMod 2)).val, h1, Matrix.one_mul,
      ← Matrix.mul_assoc (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ, h2, Matrix.one_mul]

theorem card_sym_subtype_eq (P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop) [DecidablePred P] :
    Nat.card {B : binarySymMatrices 3 // P B} =
      (Finset.univ.filter fun x : SixBits => P (symMat x)).card := by
  rw [Nat.card_congr (symEquiv.subtypeEquiv
    (p := fun B : binarySymMatrices 3 => P (B : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (q := fun x => P (symMat x)) fun B => by rw [symMat_symEquiv]), Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem card_filter_rkBits_two :
    (Finset.univ.filter fun x : SixBits => rkBits x = 2).card = 7 := by
  decide +kernel

theorem card_filter_rkBits_four_alt :
    (Finset.univ.filter fun x : SixBits => rkBits x = 4 ∧ altBits x).card = 7 := by
  decide +kernel

theorem card_filter_rkBits_four_nonalt :
    (Finset.univ.filter fun x : SixBits => rkBits x = 4 ∧ ¬ altBits x).card = 21 := by
  decide +kernel

theorem card_filter_rkBits_eight :
    (Finset.univ.filter fun x : SixBits => rkBits x = 8).card = 28 := by
  decide +kernel

theorem sym_rank_eq_zero_iff (B : binarySymMatrices 3) :
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 0 ↔ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
  constructor
  · intro h
    have h1 := (rkBits_symEquiv_eq_iff B 0).2 h
    have h2 : symEquiv B ∈ Finset.univ.filter fun x : SixBits => rkBits x = 1 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
    have h3 : (Finset.univ.filter fun x : SixBits => rkBits x = 1) = {(0, 0, 0, 0, 0, 0)} := by
      decide +kernel
    rw [h3, Finset.mem_singleton] at h2
    rw [← symMat_symEquiv, h2]
    decide
  · intro h
    rw [h, rank_zero]

theorem card_sym_rank_one :
    Nat.card {B : binarySymMatrices 3 // (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1} = 7 := by
  classical
  rw [card_sym_subtype_eq (fun B => B.rank = 1), ← card_filter_rkBits_two,
    Finset.filter_congr fun x _ => rank_symMat_eq_iff x 1]
  rfl

theorem card_sym_rank_two_alternating :
    Nat.card {B : binarySymMatrices 3 // (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∧
      ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0} = 7 := by
  classical
  rw [card_sym_subtype_eq (fun B => B.rank = 2 ∧ ∀ i, B i i = 0), ← card_filter_rkBits_four_alt,
    Finset.filter_congr fun x _ => and_congr (rank_symMat_eq_iff x 2) (altBits_iff x).symm]
  rfl

theorem card_sym_rank_two_nonalternating :
    Nat.card {B : binarySymMatrices 3 // (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∧
      ¬ ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0} = 21 := by
  classical
  rw [card_sym_subtype_eq (fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0),
    ← card_filter_rkBits_four_nonalt, Finset.filter_congr fun x _ =>
      and_congr (rank_symMat_eq_iff x 2) (not_congr (altBits_iff x).symm)]
  rfl

theorem card_sym_rank_three :
    Nat.card {B : binarySymMatrices 3 // (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 3} = 28 := by
  classical
  rw [card_sym_subtype_eq (fun B => B.rank = 3), ← card_filter_rkBits_eight,
    Finset.filter_congr fun x _ => rank_symMat_eq_iff x 3]
  rfl

theorem rkBits_two_iff : ∀ x : SixBits,
    rkBits x = 2 ↔ ∃ v : Fin 3 → ZMod 2, v ≠ 0 ∧ symMat x = vecMulVec v v := by
  decide +kernel

theorem sym_rank_one_iff (B : binarySymMatrices 3) :
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1 ↔
      ∃ v : Fin 3 → ZMod 2, v ≠ 0 ∧ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = vecMulVec v v := by
  rw [← rkBits_symEquiv_eq_iff, pow_one, rkBits_two_iff, symMat_symEquiv]

theorem vecMulVec_self_injective :
    Function.Injective fun v : Fin 3 → ZMod 2 => vecMulVec v v := by
  intro v w h
  have : ∀ v w : Fin 3 → ZMod 2, vecMulVec v v = vecMulVec w w → v = w := by decide
  exact this v w h

theorem mul_vecMulVec_mul_transpose (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    D * vecMulVec v v * Dᵀ = vecMulVec (D *ᵥ v) (D *ᵥ v) := by
  rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

@[expose] def altMat (v : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, v 2, v 1; v 2, 0, v 0; v 1, v 0, 0]

@[expose] def crossMat {α : Type*} [CommRing α] (v : Fin 3 → α) : Matrix (Fin 3) (Fin 3) α :=
  !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0]

theorem mul_crossMat_mul_transpose {α : Type*} [CommRing α] (M : Matrix (Fin 3) (Fin 3) α)
    (v : Fin 3 → α) : M * crossMat v * Mᵀ = crossMat (M.adjugateᵀ *ᵥ v) := by
  rw [adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMat, Matrix.mul_apply, Fin.sum_univ_three, mulVec, dotProduct] <;> ring

theorem altMat_eq_crossMat (v : Fin 3 → ZMod 2) : altMat v = crossMat v := by
  simp only [altMat, crossMat, ZMod.neg_eq_self_mod_two]

theorem altMat_transpose (v : Fin 3 → ZMod 2) : (altMat v)ᵀ = altMat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem altMat_add (v w : Fin 3 → ZMod 2) : altMat (v + w) = altMat v + altMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

theorem altMat_injective : Function.Injective altMat := by
  intro v w h
  funext k
  fin_cases k
  · exact congrFun (congrFun h 1) 2
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 0) 1

theorem rkBits_four_alt_iff_altMat : ∀ x : SixBits,
    (rkBits x = 4 ∧ altBits x) ↔ ∃ v : Fin 3 → ZMod 2, v ≠ 0 ∧ symMat x = altMat v := by
  decide +kernel

theorem sym_rank_two_alternating_iff (B : binarySymMatrices 3) :
    ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∧
        ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ↔
      ∃ v : Fin 3 → ZMod 2, v ≠ 0 ∧ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = altMat v := by
  rw [← altBits_symEquiv_iff, ← rkBits_symEquiv_eq_iff, show 2 ^ 2 = 4 from rfl,
    rkBits_four_alt_iff_altMat, symMat_symEquiv]

theorem det_GL_three_eq_one (D : GL (Fin 3) (ZMod 2)) :
    (D : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have h := (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
  have : ∀ a : ZMod 2, IsUnit a → a = 1 := by decide
  exact this _ h

theorem coe_inv_eq_adjugate_three (D : GL (Fin 3) (ZMod 2)) :
    ((D⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (D : Matrix (Fin 3) (Fin 3) (ZMod 2)).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, det_GL_three_eq_one, Ring.inverse_one, one_smul]

theorem mul_altMat_mul_transpose (D : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) * altMat v * (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ =
      altMat (((D⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ v) := by
  rw [altMat_eq_crossMat, altMat_eq_crossMat, mul_crossMat_mul_transpose, coe_inv_eq_adjugate_three]

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
