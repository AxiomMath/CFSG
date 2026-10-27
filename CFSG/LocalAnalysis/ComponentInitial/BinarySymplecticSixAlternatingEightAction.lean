module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegreeEight

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix MulAction DegreeEight
open scoped Pointwise BinarySymThreeOrbit

@[expose] def bvec (i : Fin 3) : Fin 3 → ZMod 2 := fun k => if k = i then 1 else 0

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

@[expose] def stabWitnesses : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![1, 0, 0; 0, 1, 0; 0, 1, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1],
    !![0, 1, 0; 1, 1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 1, 0, 1], !![1, 0, 0; 1, 1, 0; 0, 0, 1],
    !![1, 1, 0; 0, 1, 0; 0, 0, 1]]

theorem stabWitnesses_det : ∀ s ∈ stabWitnesses, s.det = 1 := by
  decide +kernel

theorem exists_stabWitness (i j : Fin 3) (x : Fin 3 → ZMod 2) (h0 : x ≠ 0) (hi : x ≠ bvec i) :
    ∃ s ∈ stabWitnesses, sᵀ *ᵥ bvec i = bvec i ∧ s *ᵥ bvec j = bvec j ∧ sᵀ *ᵥ x ≠ x := by
  revert i j x
  decide +kernel

@[expose] def orderSeven : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 0, 1, 1; 1, 1, 0]

theorem orderSeven_det : orderSeven.det = 1 := by
  decide +kernel

@[expose] def diagBilin (c : Fin 3 → Fin 3 → ZMod 2) (a w : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  fun k => ∑ j, a k * w j * c k j

theorem diagBilin_orderSeven : ∀ c : Fin 3 → Fin 3 → ZMod 2,
    (∀ i j : Fin 3, orderSevenᵀ *ᵥ diagBilin c (bvec i) (orderSeven *ᵥ bvec j) =
      diagBilin c (orderSevenᵀ *ᵥ bvec i) (bvec j)) → c = 0 := by
  decide +kernel

theorem bilin_expand (t : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (h₁ : ∀ a a' w, t (a + a') w = t a w + t a' w) (h₂ : ∀ a w w', t a (w + w') = t a w + t a w')
    (a w : Fin 3 → ZMod 2) :
    t a w = ∑ i, ∑ j, (a i * w j) • t (bvec i) (bvec j) := by
  have hz₁ : ∀ w, t 0 w = 0 := fun w => by simpa using h₁ 0 0 w
  have hz₂ : ∀ a, t a 0 = 0 := fun a => by simpa using h₂ a 0 0
  have hs₁ : ∀ (c : ZMod 2) a w, t (c • a) w = c • t a w := fun c a w => by
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul, zero_smul, hz₁]
    · rw [one_smul, one_smul]
  have hs₂ : ∀ (c : ZMod 2) a w, t a (c • w) = c • t a w := fun c a w => by
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul, zero_smul, hz₂]
    · rw [one_smul, one_smul]
  have hdec : ∀ x : Fin 3 → ZMod 2, x = x 0 • bvec 0 + x 1 • bvec 1 + x 2 • bvec 2 := fun x => by
    funext k
    fin_cases k <;> simp [bvec]
  have key : t a w = t (a 0 • bvec 0 + a 1 • bvec 1 + a 2 • bvec 2)
      (w 0 • bvec 0 + w 1 • bvec 1 + w 2 • bvec 2) := by
    rw [← hdec a, ← hdec w]
  rw [key]
  simp only [h₁, h₂, hs₁, hs₂, Fin.sum_univ_three, smul_smul]

theorem bilin_eq_zero_of_equivariant
    (t : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (h₁ : ∀ a a' w, t (a + a') w = t a w + t a' w) (h₂ : ∀ a w w', t a (w + w') = t a w + t a w')
    (hs : ∀ s : Matrix (Fin 3) (Fin 3) (ZMod 2), s.det = 1 →
      ∀ a w, sᵀ *ᵥ t a (s *ᵥ w) = t (sᵀ *ᵥ a) w) (a w : Fin 3 → ZMod 2) :
    t a w = 0 := by
  have hT : ∀ i j, t (bvec i) (bvec j) = t (bvec i) (bvec j) i • bvec i := by
    intro i j
    by_contra hne
    have h0 : t (bvec i) (bvec j) ≠ 0 := fun h => hne (by rw [h]; simp)
    have hi : t (bvec i) (bvec j) ≠ bvec i := fun h => hne (by rw [h]; simp [bvec])
    obtain ⟨s, hsL, hsi, hsj, hsx⟩ := exists_stabWitness i j _ h0 hi
    have h := hs s (stabWitnesses_det s hsL) (bvec i) (bvec j)
    rw [hsj, hsi] at h
    exact hsx h
  set c : Fin 3 → Fin 3 → ZMod 2 := fun i j => t (bvec i) (bvec j) i with hc
  have hexp : ∀ a w, t a w = diagBilin c a w := fun a w => by
    rw [bilin_expand t h₁ h₂ a w]
    funext k
    simp only [diagBilin, hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [hT i j]
    simp [Fin.sum_univ_three, bvec]
  have hc0 : c = 0 := diagBilin_orderSeven c fun i j => by
    rw [← hexp, ← hexp]
    exact hs orderSeven orderSeven_det (bvec i) (bvec j)
  rw [hexp, hc0]
  funext k
  simp [diagBilin]

@[expose] def covecWitnesses : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![1, 0, 0; 1, 0, 1; 1, 1, 0],
    !![1, 0, 0; 0, 1, 0; 0, 1, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 1, 1; 0, 0, 1; 0, 1, 0],
    !![1, 0, 1; 0, 1, 0; 0, 0, 1], !![0, 1, 0; 1, 1, 0; 0, 0, 1]]

theorem covecWitnesses_det : ∀ s ∈ covecWitnesses, s.det = 1 := by
  decide +kernel

theorem exists_covecWitness (a x : Fin 3 → ZMod 2) (ha : a ≠ 0) (hx : x ≠ 0) :
    ∃ s ∈ covecWitnesses, sᵀ *ᵥ a = a ∧ s *ᵥ x ≠ x := by
  revert a x
  decide +kernel

theorem eq_zero_of_forall_covec_stabilizer {a x : Fin 3 → ZMod 2} (ha : a ≠ 0)
    (h : ∀ s : Matrix (Fin 3) (Fin 3) (ZMod 2), s.det = 1 → sᵀ *ᵥ a = a → s *ᵥ x = x) :
    x = 0 := by
  by_contra hx
  obtain ⟨s, hsL, hsa, hsx⟩ := exists_covecWitness a x ha hx
  exact hsx (h s (covecWitnesses_det s hsL) hsa)

theorem eq_zero_of_smul_eq_smul : ∀ (ε ε' : ZMod 2) (a a' : Fin 3 → ZMod 2), a ≠ 0 → a' ≠ 0 →
    a' ≠ a → ε' • a = ε • a' → ε = 0 ∧ ε' = 0 := by
  decide +kernel

theorem exists_ne_zero_ne : ∀ a : Fin 3 → ZMod 2, ∃ a' : Fin 3 → ZMod 2, a' ≠ 0 ∧ a' ≠ a := by
  decide +kernel

theorem exists_gl_mulVec_eq {u w : Fin 3 → ZMod 2} (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ σ : GL (Fin 3) (ZMod 2), (σ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u = w := by
  obtain ⟨A, hA⟩ := BinaryAffineEight.exists_linearEquiv_apply_eq (Module.finrank_fin_fun _) hu hw
  exact ⟨glLin.symm A, by rw [← glLin_apply, MulEquiv.apply_symm_apply, hA]⟩

@[expose] def glOfDet (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hs : s.det = 1) :
    GL (Fin 3) (ZMod 2) :=
  nonsingInvUnit s (by rw [hs]; exact isUnit_one)

theorem coe_glOfDet (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hs : s.det = 1) :
    (glOfDet s hs : Matrix (Fin 3) (Fin 3) (ZMod 2)) = s :=
  rfl

theorem altLabel_add (v w : Fin 3 → ZMod 2) : altLabel (v + w) = altLabel v + altLabel w :=
  Subtype.ext (altMat_add v w)

theorem altLabel_smul (c : ZMod 2) (v : Fin 3 → ZMod 2) : altLabel (c • v) = c • altLabel v := by
  rcases zmod_two_cases c with rfl | rfl
  · rw [zero_smul, zero_smul, altLabel_zero]
  · rw [one_smul, one_smul]

theorem symThreeOff_altLabel (v : Fin 3 → ZMod 2) :
    symThreeOff (altLabel v : Matrix (Fin 3) (Fin 3) (ZMod 2)) = v := by
  funext k
  fin_cases k <;> rfl

theorem diag_altLabel (v : Fin 3 → ZMod 2) :
    symThreeDiag (altLabel v : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 :=
  symThreeDiag_alt v

theorem eq_altLabel_of_diag_eq_zero {B : binarySymMatrices 3}
    (hB : symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0) :
    B = altLabel (symThreeOff (B : Matrix (Fin 3) (Fin 3) (ZMod 2))) :=
  Subtype.ext (eq_symThreeAlt B.2 hB)

theorem diag_label (w : Fin 3 → ZMod 2) :
    symThreeDiag (BinarySymThreeOrbit.label w : Matrix (Fin 3) (Fin 3) (ZMod 2)) = w :=
  BinarySymThreeOrbit.diag_vecMulVec_self w

theorem label_add (w w' : Fin 3 → ZMod 2) :
    BinarySymThreeOrbit.label (w + w') = BinarySymThreeOrbit.label w +
      BinarySymThreeOrbit.label w' + ⟨symThreePolar w w', symThreePolar_mem w w'⟩ :=
  Subtype.ext (BinarySymThreeOrbit.vecMulVec_add_self w w')

theorem symThreeCongr_label' (σ : GL (Fin 3) (ZMod 2)) (w : Fin 3 → ZMod 2) :
    symThreeCongr σ (BinarySymThreeOrbit.label w) =
      BinarySymThreeOrbit.label ((σ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) :=
  symThreeCongr_label σ w

section ConjLabel

variable {G : Type*} [Group G] {R : Subgroup G}
  (θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2))

theorem conj_mem_of_mem_normalizer {g x : G} (hg : g ∈ normalizer (R : Set G)) (hx : x ∈ R) :
    g * x * g⁻¹ ∈ R :=
  (mem_normalizer_iff.1 hg x).1 hx

@[expose] def conjLabel :
    normalizer (R : Set G) →* AddMonoid.End (binarySymMatrices 3 × ZMod 2) where
  toFun g :=
    { toFun := fun X => Multiplicative.toAdd (θ ⟨g * θ.symm (.ofAdd X) * (g : G)⁻¹,
        conj_mem_of_mem_normalizer g.2 (θ.symm _).2⟩)
      map_zero' := by
        have h : (⟨g * θ.symm (.ofAdd 0) * (g : G)⁻¹,
            conj_mem_of_mem_normalizer g.2 (θ.symm _).2⟩ : R) = 1 :=
          Subtype.ext (by
            change (g : G) * θ.symm (.ofAdd 0) * (g : G)⁻¹ = 1
            rw [ofAdd_zero, map_one, OneMemClass.coe_one, mul_one, mul_inv_cancel])
        rw [h, map_one, toAdd_one]
      map_add' := fun X Y => by
        have h : (⟨g * θ.symm (.ofAdd (X + Y)) * (g : G)⁻¹,
            conj_mem_of_mem_normalizer g.2 (θ.symm _).2⟩ : R) =
            ⟨g * θ.symm (.ofAdd X) * (g : G)⁻¹, conj_mem_of_mem_normalizer g.2 (θ.symm _).2⟩ *
              ⟨g * θ.symm (.ofAdd Y) * (g : G)⁻¹,
                conj_mem_of_mem_normalizer g.2 (θ.symm _).2⟩ :=
          Subtype.ext (by
            change (g : G) * θ.symm (.ofAdd (X + Y)) * (g : G)⁻¹ =
              (g : G) * θ.symm (.ofAdd X) * (g : G)⁻¹ * ((g : G) * θ.symm (.ofAdd Y) * (g : G)⁻¹)
            rw [ofAdd_add, map_mul, Subgroup.coe_mul]
            group)
        rw [h, map_mul, toAdd_mul] }
  map_one' := AddMonoidHom.ext fun X => by
    change Multiplicative.toAdd (θ ⟨((1 : normalizer (R : Set G)) : G) * θ.symm (.ofAdd X) *
      ((1 : normalizer (R : Set G)) : G)⁻¹, _⟩) = X
    have h : (⟨((1 : normalizer (R : Set G)) : G) * θ.symm (.ofAdd X) *
        ((1 : normalizer (R : Set G)) : G)⁻¹,
          conj_mem_of_mem_normalizer (1 : normalizer (R : Set G)).2 (θ.symm _).2⟩ : R) =
        θ.symm (.ofAdd X) :=
      Subtype.ext (by simp)
    rw [h, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  map_mul' g h := AddMonoidHom.ext fun X => by
    change Multiplicative.toAdd (θ ⟨((g * h : normalizer (R : Set G)) : G) * θ.symm (.ofAdd X) *
      ((g * h : normalizer (R : Set G)) : G)⁻¹, _⟩) =
      Multiplicative.toAdd (θ ⟨g * θ.symm (.ofAdd (Multiplicative.toAdd
        (θ ⟨h * θ.symm (.ofAdd X) * (h : G)⁻¹,
          conj_mem_of_mem_normalizer h.2 (θ.symm _).2⟩))) * (g : G)⁻¹, _⟩)
    congr 2
    apply Subtype.ext
    simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply, Subgroup.coe_mul]
    group

theorem conjLabel_spec (g : normalizer (R : Set G)) (X : binarySymMatrices 3 × ZMod 2) :
    (θ.symm (.ofAdd (conjLabel θ g X)) : G) = g * θ.symm (.ofAdd X) * (g : G)⁻¹ := by
  have h : conjLabel θ g X = Multiplicative.toAdd (θ ⟨g * θ.symm (.ofAdd X) * (g : G)⁻¹,
      conj_mem_of_mem_normalizer g.2 (θ.symm _).2⟩) := rfl
  rw [h, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem conjLabel_eq_iff (g : normalizer (R : Set G)) (X Y : binarySymMatrices 3 × ZMod 2) :
    conjLabel θ g X = Y ↔ (g : G) * θ.symm (.ofAdd X) * (g : G)⁻¹ = θ.symm (.ofAdd Y) := by
  rw [← conjLabel_spec]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact Multiplicative.ofAdd.injective (θ.symm.injective (Subtype.ext h))

theorem conjLabel_mul_apply (g h : normalizer (R : Set G)) (X : binarySymMatrices 3 × ZMod 2) :
    conjLabel θ (g * h) X = conjLabel θ g (conjLabel θ h X) := by
  rw [map_mul]
  rfl

theorem conjLabel_inv_apply (g : normalizer (R : Set G)) (X : binarySymMatrices 3 × ZMod 2) :
    conjLabel θ g⁻¹ (conjLabel θ g X) = X := by
  rw [← conjLabel_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem conjLabel_of_mem (hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (g : normalizer (R : Set G))
    (hg : (g : G) ∈ R) (X : binarySymMatrices 3 × ZMod 2) : conjLabel θ g X = X := by
  rw [conjLabel_eq_iff, hcomm _ hg _ (θ.symm _).2, mul_inv_cancel_right]

@[expose] def zLabel (g : normalizer (R : Set G)) : Fin 3 → ZMod 2 :=
  symThreeOff ((conjLabel θ g (0, 1)).1 : Matrix (Fin 3) (Fin 3) (ZMod 2))

end ConjLabel

section ExactAction

variable {G : Type*} [Group G] {R : Subgroup G}
  (θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2))

structure AltTranslationData (D S : Subgroup G) : Prop where
  comm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
  le_normalizer : D ≤ normalizer (R : Set G)
  le_normalizer' : S ≤ normalizer (R : Set G)
  le : R ≤ D
  normal : ∀ n ∈ normalizer (R : Set G), ∀ d ∈ D, n * d * n⁻¹ ∈ D
  isPGroup : IsPGroup 2 D
  translate : ∀ (d : G) (hd : d ∈ D) (v : Fin 3 → ZMod 2),
    conjLabel θ ⟨d, le_normalizer hd⟩ (altLabel v, 1) =
      (altLabel (v + zLabel θ ⟨d, le_normalizer hd⟩), 1)
  mem_of_zLabel : ∀ (d : G) (hd : d ∈ D), zLabel θ ⟨d, le_normalizer hd⟩ = 0 → d ∈ R
  zLabel_surj : ∀ a : Fin 3 → ZMod 2, ∃ (d : G) (hd : d ∈ D), zLabel θ ⟨d, le_normalizer hd⟩ = a
  levi : ∀ (n : G) (hn : n ∈ S), ∃ σ : GL (Fin 3) (ZMod 2),
    ∀ X, conjLabel θ ⟨n, le_normalizer' hn⟩ X = (symThreeCongr σ X.1, X.2)
  levi_surj : ∀ σ : GL (Fin 3) (ZMod 2), ∃ (n : G) (hn : n ∈ S),
    ∀ X, conjLabel θ ⟨n, le_normalizer' hn⟩ X = (symThreeCongr σ X.1, X.2)

namespace AltTranslationData

variable {θ} {D S : Subgroup G} (H : AltTranslationData θ D S)
include H

abbrev T (d : D) : AddMonoid.End (binarySymMatrices 3 × ZMod 2) :=
  conjLabel θ ⟨d, H.le_normalizer d.2⟩

abbrev lab (d : D) : Fin 3 → ZMod 2 :=
  zLabel θ ⟨d, H.le_normalizer d.2⟩

theorem T_mul (d d' : D) (X : binarySymMatrices 3 × ZMod 2) :
    H.T (d * d') X = H.T d (H.T d' X) := by
  rw [← conjLabel_mul_apply]
  rfl

theorem T_one (X : binarySymMatrices 3 × ZMod 2) : H.T 1 X = X := by
  change conjLabel θ 1 X = X
  rw [map_one]
  rfl

theorem T_translate (d : D) (v : Fin 3 → ZMod 2) :
    H.T d (altLabel v, 1) = (altLabel (v + H.lab d), 1) :=
  H.translate d d.2 v

theorem T_z (d : D) : H.T d (0, 1) = (altLabel (H.lab d), 1) := by
  have h := H.T_translate d 0
  rwa [zero_add, altLabel_zero] at h

theorem T_alt (d : D) (v : Fin 3 → ZMod 2) : H.T d (altLabel v, 0) = (altLabel v, 0) := by
  have h1 := H.T_translate d v
  have h2 := H.T_z d
  have h : ((altLabel v, 0) : binarySymMatrices 3 × ZMod 2) = (altLabel v, 1) - (0, 1) := by
    ext
    · simp
    · simp
  rw [h, map_sub, h1, h2, altLabel_add]
  ext
  · simp
  · simp

theorem T_of_diag_eq_zero (d : D) {B : binarySymMatrices 3}
    (hB : symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0) : H.T d (B, 0) = (B, 0) := by
  rw [eq_altLabel_of_diag_eq_zero hB]
  exact H.T_alt d _

theorem T_of_mem (d : D) (hd : (d : G) ∈ R) (X : binarySymMatrices 3 × ZMod 2) : H.T d X = X :=
  conjLabel_of_mem θ H.comm _ hd X

theorem lab_mul (d d' : D) : H.lab (d * d') = H.lab d + H.lab d' := by
  have h : H.T (d * d') (0, 1) = (altLabel (H.lab d' + H.lab d), 1) := by
    rw [H.T_mul, H.T_z, H.T_translate]
  have h' := congrArg (fun X : binarySymMatrices 3 × ZMod 2 =>
    symThreeOff ((X.1 : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  simp only [symThreeOff_altLabel] at h'
  change symThreeOff ((H.T (d * d') (0, 1)).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [h', add_comm]

theorem lab_one : H.lab 1 = 0 := by
  have h := H.lab_mul 1 1
  rw [mul_one] at h
  have h2 : H.lab 1 + H.lab 1 = 0 := by
    funext k
    exact symThree_zmod_add_self _
  rw [← h] at h2
  exact h2

theorem lab_inv (d : D) : H.lab d⁻¹ = H.lab d := by
  have h := H.lab_mul d d⁻¹
  rw [mul_inv_cancel, H.lab_one] at h
  have h2 : H.lab d + H.lab d = 0 := by
    funext k
    exact symThree_zmod_add_self _
  rw [← h2] at h
  exact (add_left_cancel h).symm

theorem T_comm (d d' : D) (X : binarySymMatrices 3 × ZMod 2) :
    H.T d (H.T d' X) = H.T d' (H.T d X) := by
  set r : D := (d' * d)⁻¹ * (d * d') with hr
  have hrR : (r : G) ∈ R := by
    apply H.mem_of_zLabel _ r.2
    change H.lab r = 0
    rw [hr, H.lab_mul, H.lab_inv, H.lab_mul, H.lab_mul]
    funext k
    simp only [Pi.add_apply, Pi.zero_apply]
    have h1 := symThree_zmod_add_self (H.lab d' k)
    have h2 := symThree_zmod_add_self (H.lab d k)
    grind
  have h : d * d' = (d' * d) * r := by
    rw [hr, mul_inv_cancel_left]
  rw [← H.T_mul, h, H.T_mul, H.T_of_mem r hrR, H.T_mul]

abbrev conjD (n : G) (hn : n ∈ normalizer (R : Set G)) (d : D) : D :=
  ⟨n * d * n⁻¹, H.normal n hn d d.2⟩

theorem T_conjD (n : G) (hn : n ∈ normalizer (R : Set G)) (d : D)
    (X : binarySymMatrices 3 × ZMod 2) :
    H.T (H.conjD n hn d) (conjLabel θ ⟨n, hn⟩ X) = conjLabel θ ⟨n, hn⟩ (H.T d X) := by
  have h : (⟨n * d * n⁻¹, H.le_normalizer (H.normal n hn d d.2)⟩ : normalizer (R : Set G)) =
      ⟨n, hn⟩ * ⟨d, H.le_normalizer d.2⟩ * ⟨n, hn⟩⁻¹ := rfl
  change conjLabel θ ⟨n * d * n⁻¹, _⟩ _ = _
  rw [h, conjLabel_mul_apply, conjLabel_mul_apply, conjLabel_inv_apply]

theorem conjD_conjD_inv (n : G) (hn : n ∈ normalizer (R : Set G)) (d : D) :
    H.conjD n hn (H.conjD n⁻¹ (inv_mem hn) d) = d :=
  Subtype.ext (by simp only [inv_inv]; group)

theorem T_zero (d : D) : H.T d 0 = 0 :=
  map_zero _

abbrev diagMap (d : D) (w : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  symThreeDiag ((H.T d (BinarySymThreeOrbit.label w, 0)).1 : Matrix (Fin 3) (Fin 3) (ZMod 2))

theorem diag_T_zero (d : D) (B : binarySymMatrices 3) :
    symThreeDiag ((H.T d (B, 0)).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      H.diagMap d (symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  set w := symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2))
  have hBd : symThreeDiag ((B - BinarySymThreeOrbit.label w : binarySymMatrices 3) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
    rw [AddSubgroupClass.coe_sub]
    change symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) -
      symThreeDiag (BinarySymThreeOrbit.label w : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0
    rw [diag_label, sub_self]
  have hsplit : ((B, 0) : binarySymMatrices 3 × ZMod 2) =
      (BinarySymThreeOrbit.label w, 0) + (B - BinarySymThreeOrbit.label w, 0) := by
    ext <;> simp
  rw [hsplit, map_add, H.T_of_diag_eq_zero d hBd, Prod.fst_add, AddSubgroup.coe_add,
    symThreeDiag_add, hBd, add_zero]

theorem diag_T (d : D) (X : binarySymMatrices 3 × ZMod 2) :
    symThreeDiag ((H.T d X).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      H.diagMap d (symThreeDiag ((X.1 : binarySymMatrices 3) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  obtain ⟨B, c⟩ := X
  rcases zmod_two_cases c with rfl | rfl
  · exact H.diag_T_zero d B
  · have hsplit : ((B, 1) : binarySymMatrices 3 × ZMod 2) = (B, 0) + (0, 1) := by
      ext <;> simp
    rw [hsplit, map_add, H.T_z, Prod.fst_add, AddSubgroup.coe_add, symThreeDiag_add,
      diag_altLabel, add_zero, H.diag_T_zero d B]
    simp

theorem diagMap_mul (d d' : D) (w : Fin 3 → ZMod 2) :
    H.diagMap (d * d') w = H.diagMap d (H.diagMap d' w) := by
  change symThreeDiag ((H.T (d * d') (BinarySymThreeOrbit.label w, 0)).1 :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [H.T_mul, H.diag_T]

theorem diagMap_one (w : Fin 3 → ZMod 2) : H.diagMap 1 w = w := by
  change symThreeDiag ((H.T 1 (BinarySymThreeOrbit.label w, 0)).1 :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [H.T_one, diag_label]

theorem diagMap_zero (d : D) : H.diagMap d 0 = 0 := by
  change symThreeDiag ((H.T d (BinarySymThreeOrbit.label 0, 0)).1 :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [BinarySymThreeOrbit.label_zero, Prod.mk_zero_zero, H.T_zero]
  rfl

theorem diagMap_ne_zero (d : D) {w : Fin 3 → ZMod 2} (hw : w ≠ 0) : H.diagMap d w ≠ 0 :=
  fun h => hw (by
    have h1 := H.diagMap_mul d⁻¹ d w
    rw [inv_mul_cancel, H.diagMap_one, h, H.diagMap_zero] at h1
    exact h1)

theorem diagMap_conjD (n : G) (hn : n ∈ S) (σ : GL (Fin 3) (ZMod 2))
    (hσ : ∀ X, conjLabel θ ⟨n, H.le_normalizer' hn⟩ X = (symThreeCongr σ X.1, X.2)) (d : D)
    (w : Fin 3 → ZMod 2) :
    H.diagMap (H.conjD n (H.le_normalizer' hn) d) ((σ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) =
      (σ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ H.diagMap d w := by
  have h1 : ((BinarySymThreeOrbit.label ((σ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w), 0) :
      binarySymMatrices 3 × ZMod 2) =
      conjLabel θ ⟨n, H.le_normalizer' hn⟩ (BinarySymThreeOrbit.label w, 0) := by
    rw [hσ, symThreeCongr_label']
  change symThreeDiag ((H.T _ (BinarySymThreeOrbit.label _, 0)).1 :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [h1, H.T_conjD, hσ, symThreeDiag_coe_congr]

theorem diagMap_eq (d : D) (w : Fin 3 → ZMod 2) : H.diagMap d w = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction D {w : Fin 3 → ZMod 2 // w ≠ 0} :=
    { smul := fun d w => ⟨H.diagMap d w, H.diagMap_ne_zero d w.2⟩
      one_smul := fun w => Subtype.ext (H.diagMap_one w)
      mul_smul := fun d d' w => Subtype.ext (H.diagMap_mul d d' w) }
  have hmod := H.isPGroup.card_modEq_card_fixedPoints {w : Fin 3 → ZMod 2 // w ≠ 0}
  have h7 : Nat.card {w : Fin 3 → ZMod 2 // w ≠ 0} = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rfl
  rw [h7] at hmod
  have hpos : Nat.card (MulAction.fixedPoints D {w : Fin 3 → ZMod 2 // w ≠ 0}) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨w₀, hw₀⟩⟩ := (Nat.card_ne_zero.mp hpos).1
  have hfix : ∀ d' : D, H.diagMap d' w₀.1 = w₀.1 := fun d' => congrArg Subtype.val (hw₀ d')
  by_cases hw : w = 0
  · rw [hw, H.diagMap_zero]
  obtain ⟨σ, hσw⟩ := exists_gl_mulVec_eq w₀.2 hw
  obtain ⟨n, hn, hσ⟩ := H.levi_surj σ
  have h := H.diagMap_conjD n hn σ hσ (H.conjD n⁻¹ (inv_mem (H.le_normalizer' hn)) d) w₀.1
  rw [H.conjD_conjD_inv, hfix, hσw] at h
  exact h

theorem diag_T_eq (d : D) (X : binarySymMatrices 3 × ZMod 2) :
    symThreeDiag ((H.T d X).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      symThreeDiag ((X.1 : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [H.diag_T, H.diagMap_eq]

abbrev err₁ (d : D) (B : binarySymMatrices 3) : binarySymMatrices 3 :=
  (H.T d (B, 0)).1 - B

abbrev err₂ (d : D) (B : binarySymMatrices 3) : ZMod 2 :=
  (H.T d (B, 0)).2

theorem T_eq_zero (d : D) (B : binarySymMatrices 3) :
    H.T d (B, 0) = (B + H.err₁ d B, H.err₂ d B) := by
  ext
  · simp
  · rfl

theorem T_eq_one (d : D) (B : binarySymMatrices 3) :
    H.T d (B, 1) = (B + H.err₁ d B + altLabel (H.lab d), H.err₂ d B + 1) := by
  have hsplit : ((B, 1) : binarySymMatrices 3 × ZMod 2) = (B, 0) + (0, 1) := by
    ext <;> simp
  rw [hsplit, map_add, H.T_eq_zero, H.T_z]
  rfl

theorem err₁_add (d : D) (B C : binarySymMatrices 3) :
    H.err₁ d (B + C) = H.err₁ d B + H.err₁ d C := by
  have h : ((B + C, 0) : binarySymMatrices 3 × ZMod 2) = (B, 0) + (C, 0) := by
    ext <;> simp
  change (H.T d (B + C, 0)).1 - (B + C) = ((H.T d (B, 0)).1 - B) + ((H.T d (C, 0)).1 - C)
  rw [h, map_add, Prod.fst_add]
  abel

theorem err₂_add (d : D) (B C : binarySymMatrices 3) :
    H.err₂ d (B + C) = H.err₂ d B + H.err₂ d C := by
  have h : ((B + C, 0) : binarySymMatrices 3 × ZMod 2) = (B, 0) + (C, 0) := by
    ext <;> simp
  change (H.T d (B + C, 0)).2 = (H.T d (B, 0)).2 + (H.T d (C, 0)).2
  rw [h, map_add, Prod.snd_add]

theorem err₁_alt (d : D) (v : Fin 3 → ZMod 2) : H.err₁ d (altLabel v) = 0 := by
  change (H.T d (altLabel v, 0)).1 - altLabel v = 0
  rw [H.T_alt, sub_self]

theorem err₂_alt (d : D) (v : Fin 3 → ZMod 2) : H.err₂ d (altLabel v) = 0 := by
  change (H.T d (altLabel v, 0)).2 = 0
  rw [H.T_alt]

theorem diag_err₁ (d : D) (B : binarySymMatrices 3) :
    symThreeDiag (H.err₁ d B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
  change symThreeDiag (((H.T d (B, 0)).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) -
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2))) = 0
  rw [show ∀ M N : Matrix (Fin 3) (Fin 3) (ZMod 2), symThreeDiag (M - N) =
    symThreeDiag M - symThreeDiag N from fun _ _ => rfl, H.diag_T_eq, sub_self]

theorem T_T_eq (d d' : D) (B : binarySymMatrices 3) :
    H.T d (H.T d' (B, 0)) = (B + H.err₁ d' B + H.err₁ d B +
      H.err₂ d' B • altLabel (H.lab d), H.err₂ d B + H.err₂ d' B) := by
  have he : H.err₁ d (B + H.err₁ d' B) = H.err₁ d B := by
    rw [H.err₁_add, eq_altLabel_of_diag_eq_zero (H.diag_err₁ d' B), H.err₁_alt, add_zero]
  have he₂ : H.err₂ d (B + H.err₁ d' B) = H.err₂ d B := by
    rw [H.err₂_add, eq_altLabel_of_diag_eq_zero (H.diag_err₁ d' B), H.err₂_alt, add_zero]
  rw [H.T_eq_zero d' B]
  rcases zmod_two_cases (H.err₂ d' B) with h | h
  · rw [h, H.T_eq_zero, he, he₂, zero_smul, add_zero, add_zero]
  · rw [h, H.T_eq_one, he, he₂, one_smul]

theorem err₂_eq_zero (d : D) (B : binarySymMatrices 3) : H.err₂ d B = 0 := by
  by_cases ha : H.lab d = 0
  · have hR := H.mem_of_zLabel d d.2 ha
    change (H.T d (B, 0)).2 = 0
    rw [H.T_of_mem d hR]
  obtain ⟨a', ha'0, ha'⟩ := exists_ne_zero_ne (H.lab d)
  obtain ⟨d', hd', hlab'⟩ := H.zLabel_surj a'
  set d'' : D := ⟨d', hd'⟩
  have hlab'' : H.lab d'' = a' := hlab'
  have hc := H.T_comm d d'' (B, 0)
  rw [H.T_T_eq, H.T_T_eq] at hc
  have h1 := congrArg Prod.fst hc
  simp only at h1
  have h2 : H.err₂ d'' B • altLabel (H.lab d) = H.err₂ d B • altLabel (H.lab d'') := by
    have h3 : B + H.err₁ d'' B + H.err₁ d B + H.err₂ d'' B • altLabel (H.lab d) =
        B + H.err₁ d'' B + H.err₁ d B + H.err₂ d B • altLabel (H.lab d'') := by
      rw [h1]
      abel
    exact add_left_cancel h3
  rw [← altLabel_smul, ← altLabel_smul] at h2
  have h4 := altLabel_injective h2
  rw [hlab''] at h4
  exact (eq_zero_of_smul_eq_smul _ _ _ _ ha ha'0 ha' h4).1

theorem err₁_eq_err₁_label (d : D) (B : binarySymMatrices 3) :
    H.err₁ d B = H.err₁ d (BinarySymThreeOrbit.label
      (symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2)))) := by
  set w := symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2))
  have hBd : symThreeDiag ((B - BinarySymThreeOrbit.label w : binarySymMatrices 3) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
    rw [AddSubgroupClass.coe_sub]
    change symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) -
      symThreeDiag (BinarySymThreeOrbit.label w : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0
    rw [diag_label, sub_self]
  have h : B = BinarySymThreeOrbit.label w + (B - BinarySymThreeOrbit.label w) := by abel
  conv_lhs => rw [h]
  rw [H.err₁_add, eq_altLabel_of_diag_eq_zero hBd, H.err₁_alt, add_zero]

theorem T_eq_of_lab_eq (d d' : D) (h : H.lab d = H.lab d') (X : binarySymMatrices 3 × ZMod 2) :
    H.T d' X = H.T d X := by
  have hR : ((d⁻¹ * d' : D) : G) ∈ R := by
    apply H.mem_of_zLabel _ (d⁻¹ * d').2
    change H.lab (d⁻¹ * d') = 0
    rw [H.lab_mul, H.lab_inv, h]
    funext k
    exact symThree_zmod_add_self _
  have hd : d' = d * (d⁻¹ * d') := by rw [mul_inv_cancel_left]
  rw [hd, H.T_mul, H.T_of_mem _ hR]

theorem err₁_mul (d d' : D) (B : binarySymMatrices 3) :
    H.err₁ (d * d') B = H.err₁ d B + H.err₁ d' B := by
  have h := H.T_T_eq d d' B
  rw [H.err₂_eq_zero, zero_smul, add_zero, ← H.T_mul, H.T_eq_zero] at h
  have h1 := congrArg Prod.fst h
  simp only at h1
  have h2 : B + H.err₁ (d * d') B = B + (H.err₁ d B + H.err₁ d' B) := by
    rw [h1]
    abel
  exact add_left_cancel h2

abbrev tau (d : D) (w : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  symThreeOff (H.err₁ d (BinarySymThreeOrbit.label w) : Matrix (Fin 3) (Fin 3) (ZMod 2))

theorem err₁_label (d : D) (w : Fin 3 → ZMod 2) :
    H.err₁ d (BinarySymThreeOrbit.label w) = altLabel (H.tau d w) :=
  eq_altLabel_of_diag_eq_zero (H.diag_err₁ d _)

theorem tau_add (d : D) (w w' : Fin 3 → ZMod 2) : H.tau d (w + w') = H.tau d w + H.tau d w' := by
  have h : H.err₁ d (BinarySymThreeOrbit.label (w + w')) =
      H.err₁ d (BinarySymThreeOrbit.label w) + H.err₁ d (BinarySymThreeOrbit.label w') := by
    rw [label_add, H.err₁_add, H.err₁_add,
      eq_altLabel_of_diag_eq_zero (B := ⟨symThreePolar w w', symThreePolar_mem w w'⟩)
        (symThreeDiag_polar w w'), H.err₁_alt, add_zero]
  rw [H.err₁_label, H.err₁_label, H.err₁_label, ← altLabel_add] at h
  have h' := altLabel_injective h
  change H.tau d (w + w') = _
  rw [show H.tau d (w + w') = symThreeOff (altLabel (H.tau d (w + w')) :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) from (symThreeOff_altLabel _).symm]
  rw [h', symThreeOff_altLabel]

theorem tau_mul (d d' : D) (w : Fin 3 → ZMod 2) : H.tau (d * d') w = H.tau d w + H.tau d' w := by
  have h := H.err₁_mul d d' (BinarySymThreeOrbit.label w)
  rw [H.err₁_label, H.err₁_label, H.err₁_label, ← altLabel_add] at h
  exact altLabel_injective h

theorem tau_eq_of_lab_eq (d d' : D) (h : H.lab d = H.lab d') (w : Fin 3 → ZMod 2) :
    H.tau d' w = H.tau d w := by
  change symThreeOff (((H.T d' (BinarySymThreeOrbit.label w, 0)).1 -
    BinarySymThreeOrbit.label w : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [H.T_eq_of_lab_eq d d' h]

theorem conjD_levi (n : G) (hn : n ∈ S) (σ : GL (Fin 3) (ZMod 2))
    (hσ : ∀ X, conjLabel θ ⟨n, H.le_normalizer' hn⟩ X = (symThreeCongr σ X.1, X.2)) (d : D) :
    H.lab (H.conjD n (H.le_normalizer' hn) d) =
        ((σ⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ H.lab d ∧
      ∀ w, H.tau (H.conjD n (H.le_normalizer' hn) d) ((σ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) =
        ((σ⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ H.tau d w := by
  constructor
  · have h1 : ((0, 1) : binarySymMatrices 3 × ZMod 2) =
        conjLabel θ ⟨n, H.le_normalizer' hn⟩ (0, 1) := by
      rw [hσ, symThreeCongr_zero]
    have h2 := H.T_conjD n (H.le_normalizer' hn) d (0, 1)
    rw [← h1, H.T_z, H.T_z, hσ, symThreeCongr_altLabel] at h2
    have h3 := congrArg (fun X : binarySymMatrices 3 × ZMod 2 =>
      symThreeOff ((X.1 : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2))) h2
    simpa only [symThreeOff_altLabel] using h3
  · intro w
    have h1 : ((BinarySymThreeOrbit.label ((σ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w), 0) :
        binarySymMatrices 3 × ZMod 2) =
        conjLabel θ ⟨n, H.le_normalizer' hn⟩ (BinarySymThreeOrbit.label w, 0) := by
      rw [hσ, symThreeCongr_label']
    have h2 := H.T_conjD n (H.le_normalizer' hn) d (BinarySymThreeOrbit.label w, 0)
    rw [← h1, H.T_eq_zero, H.T_eq_zero, hσ, H.err₁_label, H.err₁_label] at h2
    have h3 := congrArg Prod.fst h2
    simp only at h3
    rw [symThreeCongr_add, symThreeCongr_label', symThreeCongr_altLabel] at h3
    have h4 := altLabel_injective (add_left_cancel h3)
    exact h4

theorem tau_eq_zero (d : D) (w : Fin 3 → ZMod 2) : H.tau d w = 0 := by
  classical
  choose dsel hdsel hlab using H.zLabel_surj
  set t : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) :=
    fun a w => H.tau ⟨dsel a, hdsel a⟩ w with ht
  have hlab' : ∀ a, H.lab ⟨dsel a, hdsel a⟩ = a := hlab
  have htau : ∀ (d : D) w, H.tau d w = t (H.lab d) w := fun d w =>
    (H.tau_eq_of_lab_eq d ⟨dsel (H.lab d), hdsel (H.lab d)⟩ (hlab' _).symm w).symm
  have h₁ : ∀ a a' w, t (a + a') w = t a w + t a' w := fun a a' w => by
    have h := htau (⟨dsel a, hdsel a⟩ * ⟨dsel a', hdsel a'⟩) w
    rw [H.lab_mul, hlab', hlab', H.tau_mul] at h
    exact h.symm
  have h₂ : ∀ a w w', t a (w + w') = t a w + t a w' := fun a w w' => H.tau_add _ w w'
  have hs : ∀ s : Matrix (Fin 3) (Fin 3) (ZMod 2), s.det = 1 →
      ∀ a w, sᵀ *ᵥ t a (s *ᵥ w) = t (sᵀ *ᵥ a) w := by
    intro s hs a w
    set σ := glOfDet s hs
    obtain ⟨n, hn, hσ⟩ := H.levi_surj σ
    set d₀ : D := ⟨dsel (sᵀ *ᵥ a), hdsel (sᵀ *ᵥ a)⟩
    obtain ⟨hl, htw⟩ := H.conjD_levi n hn σ hσ d₀
    have hinv : ((σ⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ (sᵀ *ᵥ a) =
        a := by
      rw [mulVec_mulVec, ← transpose_mul, ← coe_glOfDet s hs, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, transpose_one, one_mulVec]
    have hinv' : ∀ x, sᵀ *ᵥ (((σ⁻¹ : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ x) = x := fun x => by
      rw [mulVec_mulVec, ← transpose_mul, ← coe_glOfDet s hs, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, transpose_one, one_mulVec]
    rw [hlab', hinv] at hl
    have h := htw w
    rw [htau, hl, htau, hlab', coe_glOfDet] at h
    rw [h, hinv']
  rw [htau, bilin_eq_zero_of_equivariant t h₁ h₂ hs]

theorem T_eq (d : D) (B : binarySymMatrices 3) (s : ZMod 2) :
    H.T d (B, s) = (B + s • altLabel (H.lab d), s) := by
  have he : H.err₁ d B = 0 := by
    rw [H.err₁_eq_err₁_label, H.err₁_label, H.tau_eq_zero]
    exact altLabel_zero
  rcases zmod_two_cases s with rfl | rfl
  · rw [H.T_eq_zero, he, H.err₂_eq_zero, zero_smul, add_zero]
  · rw [H.T_eq_one, he, H.err₂_eq_zero, one_smul, add_zero, zero_add]

end AltTranslationData

end ExactAction

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
