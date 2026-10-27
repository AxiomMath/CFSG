module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Blk
public import Mathlib.RingTheory.Coalgebra.CoassocSimps

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {n : ℕ}

section Char2

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem add_self_W (x : W) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]

end Char2

section Mat

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def matOfN (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) (f : W →ₗ[ZMod 2] W) :
    Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2) :=
  LinearMap.toMatrix' (e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap)

theorem matOfN_mulVec (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) (f : W →ₗ[ZMod 2] W) (x : W) :
    matOfN e f *ᵥ e x = e (f x) := by
  rw [matOfN, LinearMap.toMatrix'_mulVec]
  simp

theorem matOfN_comp (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) (f g : W →ₗ[ZMod 2] W) :
    matOfN e (f ∘ₗ g) = matOfN e f * matOfN e g := by
  rw [matOfN, matOfN, matOfN, ← LinearMap.toMatrix'_comp]
  congr 1
  ext x
  simp

theorem matOfN_id (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) : matOfN e LinearMap.id = 1 := by
  rw [matOfN, ← LinearMap.toMatrix'_id]
  congr 1
  ext x
  simp

theorem matOfN_mul (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) (f g : W →ₗ[ZMod 2] W) :
    matOfN e (f * g) = matOfN e f * matOfN e g :=
  matOfN_comp e f g

theorem matOfN_one (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) : matOfN e 1 = 1 :=
  matOfN_id e

theorem matOfN_eq_of_single (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) (f : W →ₗ[ZMod 2] W)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2))
    (h : ∀ c : Fin (n + n), e (f (e.symm (Pi.single c 1))) = M *ᵥ Pi.single c 1) :
    matOfN e f = M := by
  ext i j
  rw [matOfN, LinearMap.toMatrix'_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h j, mulVec_single_one]
  rfl

theorem matOfN_eq_iff (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) (f : W →ₗ[ZMod 2] W)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2)) :
    matOfN e f = M ↔ ∀ x, e (f x) = M *ᵥ e x := by
  constructor
  · rintro rfl x; exact (matOfN_mulVec e f x).symm
  · intro h
    exact matOfN_eq_of_single e f M fun c => by rw [h, LinearEquiv.apply_symm_apply]

theorem matOfN_injective (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) {f g : W →ₗ[ZMod 2] W}
    (h : matOfN e f = matOfN e g) : f = g := by
  ext x
  apply e.injective
  rw [← matOfN_mulVec, h, matOfN_mulVec]

@[expose] def matHomN (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) :
    (W →ₗ[ZMod 2] W) →* Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2) where
  toFun := matOfN e
  map_one' := matOfN_one e
  map_mul' := matOfN_mul e

end Mat

section Adapted

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def adaptedLinN (ι : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (w : Fin n → W) :
    (Fin (n + n) → ZMod 2) →ₗ[ZMod 2] W :=
  ι ∘ₗ LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castAdd n) +
    Fintype.linearCombination (ZMod 2) w ∘ₗ LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd n)

theorem adaptedLinN_apply (ι : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (w : Fin n → W)
    (x : Fin (n + n) → ZMod 2) :
    adaptedLinN ι w x = ι (fun j => x (Fin.castAdd n j)) + ∑ j, x (Fin.natAdd n j) • w j := by
  simp [adaptedLinN, Fintype.linearCombination_apply, LinearMap.funLeft_apply]
  rfl

theorem adaptedLinN_append (ι : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (w : Fin n → W)
    (u v : Fin n → ZMod 2) :
    adaptedLinN ι w (Fin.append u v) = ι u + ∑ j, v j • w j := by
  rw [adaptedLinN_apply]
  simp only [Fin.append_left, Fin.append_right]

variable {τ : W →ₗ[ZMod 2] W} {ι : (Fin n → ZMod 2) →ₗ[ZMod 2] W} {w : Fin n → W}

theorem tau_add_adaptedLinN (hτι : ∀ u, τ (ι u) = ι u)
    (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1)) (u v : Fin n → ZMod 2) :
    τ (adaptedLinN ι w (Fin.append u v)) + adaptedLinN ι w (Fin.append u v) = ι v := by
  rw [adaptedLinN_append, map_add, hτι, map_sum]
  simp only [map_smul]
  rw [show ∀ a b c : W, a + b + (a + c) = (a + a) + (b + c) by intro a b c; abel, add_self_W,
    zero_add, ← Finset.sum_add_distrib]
  simp only [← smul_add, hw]
  have hv : v = ∑ x, v x • (Pi.single x 1 : Fin n → ZMod 2) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv, map_sum]
  simp only [map_smul]

theorem adaptedLinN_eq_zero (hτι : ∀ u, τ (ι u) = ι u)
    (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1)) (hι : Function.Injective ι)
    (x : Fin (n + n) → ZMod 2) (hx : adaptedLinN ι w x = 0) : x = 0 := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : Fin n → ZMod 2, x = Fin.append u v :=
    ⟨fun i => x (Fin.castAdd n i), fun i => x (Fin.natAdd n i),
      (Fin.append_castAdd_natAdd (f := x)).symm⟩
  have hv : v = 0 := by
    apply hι
    rw [← tau_add_adaptedLinN hτι hw u v, hx, map_zero, add_zero, map_zero]
  subst hv
  have hu : u = 0 := by
    apply hι
    rw [map_zero, ← hx, adaptedLinN_append]
    simp
  subst hu
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

theorem adaptedLinN_injective (hτι : ∀ u, τ (ι u) = ι u)
    (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1)) (hι : Function.Injective ι) :
    Function.Injective (adaptedLinN ι w) := by
  intro x y hxy
  have h0 := adaptedLinN_eq_zero hτι hw hι (x + y) (by rw [map_add, hxy, add_self_W])
  ext i
  have := congrFun h0 i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  rw [← sub_eq_zero, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  exact this

theorem card_finN : Nat.card (Fin (n + n) → ZMod 2) = 2 ^ (n + n) := by
  simp [Nat.card_eq_fintype_card, ZMod.card]

@[expose] noncomputable def adaptedEquivN [Finite W] (hτι : ∀ u, τ (ι u) = ι u)
    (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1)) (hι : Function.Injective ι)
    (hW : Nat.card W = 2 ^ (n + n)) : (Fin (n + n) → ZMod 2) ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofBijective (adaptedLinN ι w)
    ((adaptedLinN_injective hτι hw hι).bijective_of_nat_card_le (by rw [hW, card_finN]))

variable [Finite W] (hτι : ∀ u, τ (ι u) = ι u) (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1))
  (hι : Function.Injective ι) (hW : Nat.card W = 2 ^ (n + n))

theorem adaptedEquivN_append (u v : Fin n → ZMod 2) :
    adaptedEquivN hτι hw hι hW (Fin.append u v) = ι u + ∑ j, v j • w j :=
  adaptedLinN_append ι w u v

theorem adaptedEquivN_symm_iota (u : Fin n → ZMod 2) :
    (adaptedEquivN hτι hw hι hW).symm (ι u) = Fin.append u (0 : Fin n → ZMod 2) := by
  rw [LinearEquiv.symm_apply_eq, adaptedEquivN_append]
  simp

theorem adaptedEquivN_symm_w (j : Fin n) :
    (adaptedEquivN hτι hw hι hW).symm (w j) =
      Fin.append (0 : Fin n → ZMod 2) (Pi.single j (1 : ZMod 2)) := by
  rw [LinearEquiv.symm_apply_eq, adaptedEquivN_append]
  simp [Pi.single_apply]

omit [Finite W] in
theorem appendN_add_append (a b c d : Fin n → ZMod 2) :
    (Fin.append a b : Fin (n + n) → ZMod 2) + Fin.append c d = Fin.append (a + c) (b + d) := by
  ext r
  refine Fin.addCases (fun i => ?_) (fun i => ?_) r <;>
    simp only [Pi.add_apply, Fin.append_left, Fin.append_right]

theorem adaptedEquivN_append_zero (u : Fin n → ZMod 2) :
    adaptedEquivN hτι hw hι hW (Fin.append u (0 : Fin n → ZMod 2)) = ι u := by
  rw [adaptedEquivN_append]
  simp

theorem adaptedEquivN_zero_append_single (j : Fin n) :
    adaptedEquivN hτι hw hι hW (Fin.append (0 : Fin n → ZMod 2) (Pi.single j (1 : ZMod 2))) =
      w j := by
  rw [adaptedEquivN_append, map_zero, zero_add]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

omit [Finite W] in
theorem appendN_single_castAdd (j : Fin n) :
    (Pi.single (Fin.castAdd n j) (1 : ZMod 2) : Fin (n + n) → ZMod 2) =
      Fin.append (Pi.single j 1) (0 : Fin n → ZMod 2) := by
  ext r
  refine Fin.addCases (fun i => ?_) (fun i => ?_) r
  · rw [Fin.append_left]
    by_cases h : i = j
    · subst h; simp
    · rw [Pi.single_eq_of_ne (fun e => h (Fin.castAdd_injective _ _ e)), Pi.single_eq_of_ne h]
  · rw [Fin.append_right, Pi.single_eq_of_ne (fun e => by
      have := congrArg Fin.val e
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega)]
    rfl

omit [Finite W] in
theorem appendN_single_natAdd (j : Fin n) :
    (Pi.single (Fin.natAdd n j) (1 : ZMod 2) : Fin (n + n) → ZMod 2) =
      Fin.append (0 : Fin n → ZMod 2) (Pi.single j 1) := by
  ext r
  refine Fin.addCases (fun i => ?_) (fun i => ?_) r
  · rw [Fin.append_left, Pi.single_eq_of_ne (fun e => by
      have := congrArg Fin.val e
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega)]
    rfl
  · rw [Fin.append_right]
    by_cases h : i = j
    · subst h; simp
    · rw [Pi.single_eq_of_ne (fun e => h (Fin.natAdd_injective _ _ e)), Pi.single_eq_of_ne h]

theorem matOfN_tau : matOfN (adaptedEquivN hτι hw hι hW).symm τ = tMN n := by
  apply matOfN_eq_of_single
  intro c
  refine Fin.addCases (fun j => ?_) (fun j => ?_) c
  · rw [appendN_single_castAdd, LinearEquiv.symm_symm, adaptedEquivN_append_zero, hτι,
      adaptedEquivN_symm_iota, tMN, blkN_mulVec_append, one_mulVec, one_mulVec, add_zero]
  · rw [appendN_single_natAdd, LinearEquiv.symm_symm, adaptedEquivN_zero_append_single]
    have h2 : τ (w j) = ι (Pi.single j 1) + w j := by
      rw [← hw j, add_assoc, add_self_W, add_zero]
    rw [h2, map_add, adaptedEquivN_symm_iota, adaptedEquivN_symm_w, tMN, blkN_mulVec_append,
      one_mulVec, one_mulVec, appendN_add_append, add_zero, zero_add]

@[expose] def urBlockN (M : Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => M (Fin.castAdd n i) (Fin.natAdd n j)

omit [Finite W] in
omit hτι hw hι hW in
theorem blkN_urBlockN (A C : Matrix (Fin n) (Fin n) (ZMod 2)) : urBlockN (blkN A C) = C := by
  ext i j; exact blkN_cn A C i j

omit [Finite W] in
omit hτι hw hι hW in
theorem urBlockN_one : urBlockN (1 : Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2)) = 0 := by
  rw [← blkN_one, blkN_urBlockN]

theorem natAddN_part {f : W →ₗ[ZMod 2] W} {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hfι : ∀ u, f (ι u) = ι (A *ᵥ u)) (hfτ : ∀ x, τ (f x) = f (τ x)) (j : Fin n) :
    (fun i : Fin n => (adaptedEquivN hτι hw hι hW).symm (f (w j)) (Fin.natAdd n i)) =
      A *ᵥ Pi.single j 1 := by
  apply hι
  have hy : (Fin.append
      (fun i : Fin n => (adaptedEquivN hτι hw hι hW).symm (f (w j)) (Fin.castAdd n i))
      (fun i : Fin n => (adaptedEquivN hτι hw hι hW).symm (f (w j)) (Fin.natAdd n i)) :
      Fin (n + n) → ZMod 2) = (adaptedEquivN hτι hw hι hW).symm (f (w j)) :=
    Fin.append_castAdd_natAdd
  have key := tau_add_adaptedLinN hτι hw
    (fun i : Fin n => (adaptedEquivN hτι hw hι hW).symm (f (w j)) (Fin.castAdd n i))
    (fun i : Fin n => (adaptedEquivN hτι hw hι hW).symm (f (w j)) (Fin.natAdd n i))
  rw [← key]
  change τ (adaptedEquivN hτι hw hι hW _) + adaptedEquivN hτι hw hι hW _ = _
  rw [hy, LinearEquiv.apply_symm_apply, hfτ, ← map_add, hw, hfι]

theorem matOfN_eq_blkN {f : W →ₗ[ZMod 2] W} {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hfι : ∀ u, f (ι u) = ι (A *ᵥ u)) (hfτ : ∀ x, τ (f x) = f (τ x)) :
    matOfN (adaptedEquivN hτι hw hι hW).symm f =
      blkN A (urBlockN (matOfN (adaptedEquivN hτι hw hι hW).symm f)) := by
  set e := (adaptedEquivN hτι hw hι hW).symm with he
  set M := matOfN e f with hM
  have h1 : ∀ u, M *ᵥ Fin.append u (0 : Fin n → ZMod 2) =
      Fin.append (A *ᵥ u) (0 : Fin n → ZMod 2) := fun u => by
    rw [← adaptedEquivN_symm_iota hτι hw hι hW, ← he, matOfN_mulVec, hfι, he,
      adaptedEquivN_symm_iota]
  have h2 : ∀ j : Fin n, ∀ i : Fin n,
      (M *ᵥ Fin.append (0 : Fin n → ZMod 2) (Pi.single j 1)) (Fin.natAdd n i) = A i j := by
    intro j i
    rw [hM, ← adaptedEquivN_symm_w hτι hw hι hW, he, matOfN_mulVec]
    have h3 := congrFun (natAddN_part hτι hw hι hW hfι hfτ j) i
    refine h3.trans ?_
    rw [mulVec_single_one]
    rfl
  ext r c
  refine Fin.addCases (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c
  · rw [blkN_cc]
    have := congrFun (h1 (Pi.single j 1)) (Fin.castAdd n i)
    rw [← appendN_single_castAdd, mulVec_single_one, Fin.append_left, mulVec_single_one] at this
    exact this
  · rw [blkN_cn]; rfl
  · rw [blkN_nc]
    have := congrFun (h1 (Pi.single j 1)) (Fin.natAdd n i)
    rw [← appendN_single_castAdd, mulVec_single_one, Fin.append_right] at this
    exact this
  · rw [blkN_nn]
    have := h2 j i
    rw [← appendN_single_natAdd, mulVec_single_one] at this
    exact this

end Adapted

section Shear

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def shearEquivN (X : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (Fin (n + n) → ZMod 2) ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2) where
  toFun v := blkN 1 X *ᵥ v
  invFun v := blkN 1 X *ᵥ v
  map_add' v v' := mulVec_add _ v v'
  map_smul' c v := mulVec_smul _ c v
  left_inv v := by simp only [mulVec_mulVec, blkN_one_mul_self, one_mulVec]
  right_inv v := by simp only [mulVec_mulVec, blkN_one_mul_self, one_mulVec]

theorem shearEquivN_apply (X : Matrix (Fin n) (Fin n) (ZMod 2)) (v : Fin (n + n) → ZMod 2) :
    shearEquivN X v = blkN 1 X *ᵥ v := rfl

theorem matOfN_shear (e : W ≃ₗ[ZMod 2] (Fin (n + n) → ZMod 2)) (X : Matrix (Fin n) (Fin n) (ZMod 2))
    (f : W →ₗ[ZMod 2] W) :
    matOfN (e.trans (shearEquivN X)) f = blkN 1 X * matOfN e f * blkN 1 X := by
  rw [matOfN_eq_iff]
  intro x
  simp only [LinearEquiv.trans_apply, shearEquivN_apply]
  rw [← matOfN_mulVec, mulVec_mulVec, mulVec_mulVec,
    mul_assoc (blkN 1 X * matOfN e f), blkN_one_mul_self, mul_one]

end Shear

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
