module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4GLCocycle
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.Transfer
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusLevi
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K : Type} [Field K] {Z : Type*} [AddCommGroup Z]

@[expose] noncomputable def homAct (g : orthElementaryGroup (quadPlus 4 K))
    (f : (Fin 4 ⊕ Fin 4 → K) →+ Z) : (Fin 4 ⊕ Fin 4 → K) →+ Z :=
  f.comp ((g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm.toLinearMap.toAddMonoidHom)

private def inlHom : (Fin 4 → K) →+ (Fin 4 ⊕ Fin 4 → K) where
  toFun x := Sum.elim x (0 : Fin 4 → K)
  map_zero' := by ext c; cases c <;> rfl
  map_add' x y := by ext c; cases c <;> simp

private def inrHom : (Fin 4 → K) →+ (Fin 4 ⊕ Fin 4 → K) where
  toFun y := Sum.elim (0 : Fin 4 → K) y
  map_zero' := by ext c; cases c <;> rfl
  map_add' x y := by ext c; cases c <;> simp

private noncomputable def fstPart (f : (Fin 4 ⊕ Fin 4 → K) →+ Z) : (Fin 4 → K) →+ Z :=
  f.comp inlHom

private noncomputable def sndPart (f : (Fin 4 ⊕ Fin 4 → K) →+ Z) : (Fin 4 → K) →+ Z :=
  f.comp inrHom

private lemma eq_inlHom_add_inrHom (v : Fin 4 ⊕ Fin 4 → K) :
    v = inlHom (v ∘ Sum.inl) + inrHom (v ∘ Sum.inr) := by
  ext c
  cases c <;> simp [inlHom, inrHom]

private lemma addHom_ext_parts {f g : (Fin 4 ⊕ Fin 4 → K) →+ Z}
    (h1 : fstPart f = fstPart g) (h2 : sndPart f = sndPart g) : f = g := by
  refine AddMonoidHom.ext fun v => ?_
  rw [eq_inlHom_add_inrHom v, map_add, map_add]
  change fstPart f (v ∘ Sum.inl) + sndPart f (v ∘ Sum.inr) =
    fstPart g (v ∘ Sum.inl) + sndPart g (v ∘ Sum.inr)
  rw [h1, h2]

private lemma homAct_zero (g : orthElementaryGroup (quadPlus 4 K)) :
    homAct g (0 : (Fin 4 ⊕ Fin 4 → K) →+ Z) = 0 := by
  refine AddMonoidHom.ext fun v => ?_
  rfl

private lemma homAct_add (g : orthElementaryGroup (quadPlus 4 K))
    (f f' : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    homAct g (f + f') = homAct g f + homAct g f' := by
  refine AddMonoidHom.ext fun v => ?_
  rfl

private lemma homAct_one (f : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    homAct (1 : orthElementaryGroup (quadPlus 4 K)) f = f := by
  refine AddMonoidHom.ext fun v => ?_
  rfl

private lemma homAct_mul (g h : orthElementaryGroup (quadPlus 4 K))
    (f : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    homAct (g * h) f = homAct g (homAct h f) := by
  have hcomp : ∀ v : Fin 4 ⊕ Fin 4 → K,
      ((↑(g * h) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).symm v =
        ((↑h : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).symm
          (((↑g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).symm v) := by
    intro v
    rw [show ((↑(g * h) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) =
      (↑g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) *
        (↑h : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) from rfl]
    rw [LinearEquiv.symm_apply_eq]
    simp [LinearEquiv.mul_apply]
  refine AddMonoidHom.ext fun v => ?_
  change f (((↑(g * h) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).symm v) =
    f (((↑h : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).symm
      (((↑g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).symm v))
  rw [hcomp]

private lemma fixedBy_of_homAct {g : orthElementaryGroup (quadPlus 4 K)}
    {f : (Fin 4 ⊕ Fin 4 → K) →+ Z} (h : homAct g f = f) :
    ∀ v, f ((g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v) = f v := by
  have h1 : ∀ u, f (((g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))⁻¹) u) = f u := by
    intro u
    have := congrArg (fun F : (Fin 4 ⊕ Fin 4 → K) →+ Z => F u) h
    simpa [homAct] using this
  intro v
  have h2 := h1 ((g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v)
  rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h2
  exact h2.symm

private lemma quadPlus_single_inr_apply (i : Fin 4) :
    quadPlus 4 K (Pi.single (Sum.inr i) 1) = 0 := by
  rw [quadPlus_apply]
  simp

private lemma quadPlus_smul_single_inr (s : K) (i : Fin 4) :
    quadPlus 4 K (s • Pi.single (Sum.inr i) 1) = 0 := by
  rw [map_smul_eq_sq, quadPlus_single_inr_apply, mul_zero]

private lemma eichler_polar_zero (a b : Fin 4) (hab : a ≠ b) (s : K) :
    polar (quadPlus 4 K) (Pi.single (Sum.inl a) 1) ((-s) • Pi.single (Sum.inr b) 1) = 0 := by
  have hne : (Sum.inr b : Fin 4 ⊕ Fin 4) ≠ Sum.inr a := by
    simpa using hab.symm
  rw [polar_smul_right_eq, OrthogonalSplit.polar_single_single hne, mul_zero]

private lemma eichler_single_inl (a b : Fin 4) (hab : a ≠ b) (s : K) :
    eichler (quadPlus 4 K) (Pi.single (Sum.inl a) 1) ((-s) • Pi.single (Sum.inr b) 1)
      (Pi.single (Sum.inl b) 1) =
      Pi.single (Sum.inl b) 1 + s • Pi.single (Sum.inl a) 1 := by
  rw [eichler_apply (OrthogonalSplit.quadPlus_single_inl a) (eichler_polar_zero a b hab s)]
  ext c
  cases c <;>
    simp [Pi.single_apply, OrthogonalSplit.polar_single,
      quadPlus_smul_single_inr, Sum.inr_ne_inl]

private lemma eichler_single_inr (a b : Fin 4) (hab : a ≠ b) (s : K) :
    eichler (quadPlus 4 K) (Pi.single (Sum.inl a) 1) ((-s) • Pi.single (Sum.inr b) 1)
      (Pi.single (Sum.inr a) 1) =
      Pi.single (Sum.inr a) 1 - s • Pi.single (Sum.inr b) 1 := by
  rw [eichler_apply (OrthogonalSplit.quadPlus_single_inl a) (eichler_polar_zero a b hab s)]
  ext c
  cases c <;>
    simp [Pi.single_apply, OrthogonalSplit.polar_single,
      quadPlus_smul_single_inr, Sum.inl_ne_inr]; ring

private lemma fixed_eichler_kills_inl {f : (Fin 4 ⊕ Fin 4 → K) →+ Z} {a b : Fin 4}
    (hab : a ≠ b) {s : K}
    (hf : ∀ v, f ((eichler (quadPlus 4 K) (Pi.single (Sum.inl a) 1)
      ((-s) • Pi.single (Sum.inr b) 1)) v) = f v) :
    f (s • Pi.single (Sum.inl a) 1) = 0 := by
  have h := hf (Pi.single (Sum.inl b) 1)
  rw [eichler_single_inl a b hab s, map_add] at h
  have h' : f (Pi.single (Sum.inl b) 1) + f (s • Pi.single (Sum.inl a) 1) =
      f (Pi.single (Sum.inl b) 1) + 0 := by
    rw [add_zero]
    exact h
  exact add_left_cancel h'

private lemma fixed_eichler_kills_inr {f : (Fin 4 ⊕ Fin 4 → K) →+ Z} {a b : Fin 4}
    (hab : a ≠ b) {s : K}
    (hf : ∀ v, f ((eichler (quadPlus 4 K) (Pi.single (Sum.inl a) 1)
      ((-s) • Pi.single (Sum.inr b) 1)) v) = f v) :
    f (s • Pi.single (Sum.inr b) 1) = 0 := by
  have h := hf (Pi.single (Sum.inr a) 1)
  rw [eichler_single_inr a b hab s, map_sub] at h
  have h' : f (Pi.single (Sum.inr a) 1) + (- f (s • Pi.single (Sum.inr b) 1)) =
      f (Pi.single (Sum.inr a) 1) + 0 := by
    rw [add_zero]
    simpa [sub_eq_add_neg] using h
  exact neg_eq_zero.1 (add_left_cancel h')

private lemma sum_single_eq (v : Fin 4 ⊕ Fin 4 → K) :
    (∑ c : Fin 4 ⊕ Fin 4, v c • Pi.single c (1 : K)) = v := by
  ext i
  rw [Finset.sum_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq]

section Main

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit Matrix

variable [Finite K] [CharP K 2]

private instance finiteV : Finite (Fin 4 ⊕ Fin 4 → K) := inferInstance

private instance finiteLinearEquiv :
    Finite ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
  Finite.of_injective (fun e => (e : (Fin 4 ⊕ Fin 4 → K) → (Fin 4 ⊕ Fin 4 → K)))
    (fun _e1 _e2 h => LinearEquiv.ext fun v => congrFun h v)

private instance finiteE : Finite (orthElementaryGroup (quadPlus 4 K)) := Subtype.finite

omit [Finite K] in
private lemma addHom_two_nsmul (f : (Fin 4 ⊕ Fin 4 → K) →+ Z) : (2 : ℕ) • f = 0 := by
  refine AddMonoidHom.ext fun v => ?_
  rw [AddMonoidHom.nsmul_apply, two_nsmul, ← map_add, CharTwo.add_self_eq_zero, map_zero]
  simp

private lemma leviE_mem (A : GL (Fin 4) K) :
    levi 4 K A ∈ orthElementaryGroup (quadPlus 4 K) :=
  CFSG.AGLEmbedding.LeviBlock.maxStab_le_orthElementaryGroup (r := 4) (K := K) (by norm_num)
    (levi_mem_maxStab A)

private noncomputable def leviE (A : GL (Fin 4) K) :
    orthElementaryGroup (quadPlus 4 K) :=
  ⟨levi 4 K A, leviE_mem A⟩

private lemma leviE_mul (A B : GL (Fin 4) K) : leviE (A * B) = leviE A * leviE B :=
  Subtype.ext (map_mul (levi 4 K) A B)


private noncomputable def transvectionGL (i j : Fin 4) (hij : i ≠ j) (c : K) : GL (Fin 4) K where
  val := Matrix.transvection i j c
  inv := Matrix.transvection i j (-c)
  val_inv := by
    rw [Matrix.transvection_mul_transvection_same _ _ hij, add_neg_cancel,
      Matrix.transvection_zero]
  inv_val := by
    rw [Matrix.transvection_mul_transvection_same _ _ hij, neg_add_cancel,
      Matrix.transvection_zero]

omit [Finite K] [CharP K 2] in
private lemma coe_transvectionGL (i j : Fin 4) (hij : i ≠ j) (c : K) :
    ((transvectionGL i j hij c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.transvection i j c := rfl

omit [Finite K] [CharP K 2] in
private lemma levi_transvection_eq_eichler (i j : Fin 4) (hij : i ≠ j) (c : K) :
    levi 4 K (transvectionGL i j hij c) =
      eichler (quadPlus 4 K) (Pi.single (Sum.inl i) 1) ((-c) • Pi.single (Sum.inr j) 1) := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  rw [toMatrix'_levi, coe_transvectionGL, blockDiagInv_transvection hij c]

private noncomputable def eichlerE (a b : Fin 4) (s : K) :
    orthElementaryGroup (quadPlus 4 K) :=
  ⟨eichler (quadPlus 4 K) (Pi.single (Sum.inl a) 1) ((-s) • Pi.single (Sum.inr b) 1),
    eichler_mem_elementaryGroup _ _ _⟩

private lemma eichlerE_eq_leviE (a b : Fin 4) (hab : a ≠ b) (s : K) :
    eichlerE (K := K) a b s = leviE (transvectionGL a b hab s) :=
  Subtype.ext (levi_transvection_eq_eichler a b hab s).symm

omit [Finite K] [CharP K 2] in
private lemma levi_apply_eq (A : GL (Fin 4) K) (v : Fin 4 ⊕ Fin 4 → K) :
    levi 4 K A v = Sum.elim
      (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (v ∘ Sum.inl))
      (Matrix.transpose ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (v ∘ Sum.inr)) := by
  rw [levi_eq_matrixEquiv, matrixEquiv_apply, coe_leviGL, blockDiagInv,
    fromBlocks_mulVec_apply]
  simp

omit [Finite K] [CharP K 2] in
private lemma levi_inv_apply_eq (A : GL (Fin 4) K) (v : Fin 4 ⊕ Fin 4 → K) :
    ((levi 4 K A)⁻¹ : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v = Sum.elim
      (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (v ∘ Sum.inl))
      (Matrix.transpose ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (v ∘ Sum.inr)) := by
  rw [← map_inv, levi_apply_eq]
  simp

private lemma fstPart_homAct_leviE (A : GL (Fin 4) K)
    (f : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    fstPart (homAct (leviE A) f) = glDualAct A (fstPart f) := by
  refine AddMonoidHom.ext fun x => ?_
  change f (((levi 4 K A)⁻¹) (Sum.elim x (0 : Fin 4 → K))) =
    f (Sum.elim (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x) (0 : Fin 4 → K))
  rw [levi_inv_apply_eq]
  simp

private lemma sndPart_homAct_leviE (A : GL (Fin 4) K)
    (f : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    sndPart (homAct (leviE A) f) = glTransAct A (sndPart f) := by
  refine AddMonoidHom.ext fun y => ?_
  change f (((levi 4 K A)⁻¹) (Sum.elim (0 : Fin 4 → K) y)) =
    f (Sum.elim (0 : Fin 4 → K)
      (Matrix.transpose ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ y))
  rw [levi_inv_apply_eq]
  simp

omit [Finite K] [CharP K 2] in
private lemma fstPart_add (f g : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    fstPart (f + g) = fstPart f + fstPart g := by
  refine AddMonoidHom.ext fun x => ?_
  simp [fstPart]

omit [Finite K] [CharP K 2] in
private lemma fstPart_sub (f g : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    fstPart (f - g) = fstPart f - fstPart g := by
  refine AddMonoidHom.ext fun x => ?_
  simp [fstPart]

omit [Finite K] [CharP K 2] in
private lemma sndPart_add (f g : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    sndPart (f + g) = sndPart f + sndPart g := by
  refine AddMonoidHom.ext fun x => ?_
  simp [sndPart]

omit [Finite K] [CharP K 2] in
private lemma sndPart_sub (f g : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    sndPart (f - g) = sndPart f - sndPart g := by
  refine AddMonoidHom.ext fun x => ?_
  simp [sndPart]

omit [Finite K] [CharP K 2] in
private lemma homAct_sub (g : orthElementaryGroup (quadPlus 4 K))
    (f f' : (Fin 4 ⊕ Fin 4 → K) →+ Z) :
    homAct g (f - f') = homAct g f - homAct g f' := by
  refine AddMonoidHom.ext fun v => ?_
  simp [homAct, sub_eq_add_neg]

omit [Finite K] [CharP K 2] in
private lemma homAct_neg (g : orthElementaryGroup (quadPlus 4 K))
    (f : (Fin 4 ⊕ Fin 4 → K) →+ Z) : homAct g (-f) = -homAct g f := by
  refine AddMonoidHom.ext fun v => ?_
  simp [homAct]

private lemma exists_coboundary_levi_fst
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h)) :
    ∃ f1 : (Fin 4 → K) →+ Z, ∀ A : GL (Fin 4) K,
      fstPart (c (leviE A)) = glDualAct A f1 - f1 := by
  refine exists_eq_glDualAct_sub (fun A => fstPart (c (leviE A))) ?_
  intro A B
  rw [leviE_mul, hc, fstPart_add, fstPart_homAct_leviE]

private lemma exists_coboundary_levi_snd
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h)) :
    ∃ f2 : (Fin 4 → K) →+ Z, ∀ A : GL (Fin 4) K,
      sndPart (c (leviE A)) = glTransAct A f2 - f2 := by
  refine exists_eq_glTransAct_sub (fun A => sndPart (c (leviE A))) ?_
  intro A B
  rw [leviE_mul, hc, sndPart_add, sndPart_homAct_leviE]

private noncomputable def combine (f1 f2 : (Fin 4 → K) →+ Z) :
    (Fin 4 ⊕ Fin 4 → K) →+ Z where
  toFun v := f1 (v ∘ Sum.inl) + f2 (v ∘ Sum.inr)
  map_zero' := by simp
  map_add' v w := by
    have h1 : (v + w) ∘ Sum.inl = v ∘ Sum.inl + w ∘ Sum.inl := by
      ext i; simp
    have h2 : (v + w) ∘ Sum.inr = v ∘ Sum.inr + w ∘ Sum.inr := by
      ext i; simp
    rw [h1, h2, map_add, map_add]
    abel

omit [Finite K] [CharP K 2] in
private lemma fstPart_combine (f1 f2 : (Fin 4 → K) →+ Z) :
    fstPart (combine f1 f2) = f1 := by
  refine AddMonoidHom.ext fun x => ?_
  simp [fstPart, combine, inlHom]

omit [Finite K] [CharP K 2] in
private lemma sndPart_combine (f1 f2 : (Fin 4 → K) →+ Z) :
    sndPart (combine f1 f2) = f2 := by
  refine AddMonoidHom.ext fun x => ?_
  simp [sndPart, combine, inrHom]

private lemma exists_eq_levi_coboundary
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h)) :
    ∃ m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z, ∀ A : GL (Fin 4) K,
      c (leviE A) = homAct (leviE A) m₀ - m₀ := by
  obtain ⟨f1, hf1⟩ := exists_coboundary_levi_fst c hc
  obtain ⟨f2, hf2⟩ := exists_coboundary_levi_snd c hc
  refine ⟨combine f1 f2, fun A => ?_⟩
  refine addHom_ext_parts ?_ ?_
  · rw [fstPart_sub, fstPart_homAct_leviE, fstPart_combine, hf1]
  · rw [sndPart_sub, sndPart_homAct_leviE, sndPart_combine, hf2]

private noncomputable def shift
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z) (g : orthElementaryGroup (quadPlus 4 K)) :
    (Fin 4 ⊕ Fin 4 → K) →+ Z :=
  c g - (homAct g m₀ - m₀)

omit [Finite K] [CharP K 2] in
private lemma cocycle_one
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h)) :
    c (1 : orthElementaryGroup (quadPlus 4 K)) = 0 := by
  have h := hc 1 1
  rw [mul_one, homAct_one] at h
  have h' : c 1 + 0 = c 1 + c 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

omit [Finite K] [CharP K 2] in
private lemma shift_one
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h)) :
    shift c m₀ (1 : orthElementaryGroup (quadPlus 4 K)) = 0 := by
  rw [shift, cocycle_one c hc, homAct_one]
  abel

omit [Finite K] [CharP K 2] in
private lemma shift_cocycle
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h)) :
    ∀ g h, shift c m₀ (g * h) = shift c m₀ g + homAct g (shift c m₀ h) := by
  intro g h
  simp only [shift, hc, homAct_mul, homAct_sub]
  abel

private lemma shift_levi
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hm : ∀ A : GL (Fin 4) K, c (leviE A) = homAct (leviE A) m₀ - m₀)
    (A : GL (Fin 4) K) : shift c m₀ (leviE A) = 0 := by
  rw [shift, hm A, sub_self]

omit [Finite K] [CharP K 2] in
private lemma shift_inv_eq
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h))
    (g : orthElementaryGroup (quadPlus 4 K)) :
    shift c m₀ g⁻¹ = - homAct g⁻¹ (shift c m₀ g) := by
  have h1 := shift_cocycle c m₀ hc g g⁻¹
  rw [mul_inv_cancel, shift_one c m₀ hc] at h1
  have h2 : homAct g (shift c m₀ g⁻¹) = - shift c m₀ g := by
    rw [eq_neg_iff_add_eq_zero]
    rw [add_comm]
    exact h1.symm
  have h3 := congrArg (homAct g⁻¹) h2
  rw [homAct_neg, ← homAct_mul, inv_mul_cancel, homAct_one] at h3
  exact h3

omit [Finite K] [CharP K 2] in
private lemma shift_mul_eq_zero
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h))
    {g h : orthElementaryGroup (quadPlus 4 K)}
    (hg : shift c m₀ g = 0) (hh : shift c m₀ h = 0) : shift c m₀ (g * h) = 0 := by
  rw [shift_cocycle c m₀ hc, hg, hh, homAct_zero, add_zero]

omit [Finite K] [CharP K 2] in
private lemma shift_inv_eq_zero
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h))
    {g : orthElementaryGroup (quadPlus 4 K)} (hg : shift c m₀ g = 0) :
    shift c m₀ g⁻¹ = 0 := by
  rw [shift_inv_eq c m₀ hc, hg, homAct_zero, neg_zero]

omit [Finite K] [CharP K 2] in
private lemma transvection_mul_altUnit_mul_transpose_self (i j : Fin 4) (hij : i ≠ j) (s t : K) :
    Matrix.transvection i j s * (t • OrthogonalSplit.altUnit i j) *
      (Matrix.transvection i j s)ᵀ = t • OrthogonalSplit.altUnit i j := by
  simp [Matrix.transvection, OrthogonalSplit.altUnit, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_single,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hij, hij.symm,
    smul_eq_mul, mul_one, one_mul, smul_sub,
    mul_comm s t]
  abel

omit [Finite K] [CharP K 2] in
private lemma transvection_mul_altUnit_mul_transpose_disjoint (a b i j : Fin 4)
    (_hai : a ≠ i) (_haj : a ≠ j) (hbi : b ≠ i) (hbj : b ≠ j) (s t : K) :
    Matrix.transvection a b s * (t • OrthogonalSplit.altUnit i j) *
      (Matrix.transvection a b s)ᵀ = t • OrthogonalSplit.altUnit i j := by
  simp [Matrix.transvection, OrthogonalSplit.altUnit, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_single,
    Matrix.single_mul_single_of_ne, hbi, hbj,
    hbi.symm, hbj.symm, smul_eq_mul, mul_one, one_mul, smul_sub]

omit [Finite K] [CharP K 2] in
private lemma levi_mul_radRoot_mul_inv (A : GL (Fin 4) K) (i j : Fin 4) (t : K)
    (hC : (A : Matrix (Fin 4) (Fin 4) K) * (t • OrthogonalSplit.altUnit i j) *
      (A : Matrix (Fin 4) (Fin 4) K)ᵀ = t • OrthogonalSplit.altUnit i j) :
    levi 4 K A * ((radRoot 4 K i j t : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (levi 4 K A)⁻¹ =
      ((radRoot 4 K i j t : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := by
  rw [show ((radRoot 4 K i j t : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = radical 4 K
        (Multiplicative.ofAdd (t • OrthogonalSplit.altUnit i j)) from rfl,
    OrthogonalSplit.levi_mul_radical_mul_inv, hC]

private lemma leviE_mul_radRoot_mul_inv (A : GL (Fin 4) K) (i j : Fin 4) (t : K)
    (hC : (A : Matrix (Fin 4) (Fin 4) K) * (t • OrthogonalSplit.altUnit i j) *
      (A : Matrix (Fin 4) (Fin 4) K)ᵀ = t • OrthogonalSplit.altUnit i j) :
    leviE A * radRoot 4 K i j t * (leviE A)⁻¹ = radRoot 4 K i j t :=
  Subtype.ext (levi_mul_radRoot_mul_inv A i j t hC)

private lemma eichlerE_conj_radRoot_self (i j : Fin 4) (hij : i ≠ j) (s t : K) :
    eichlerE (K := K) i j s * radRoot 4 K i j t * (eichlerE (K := K) i j s)⁻¹ =
      radRoot 4 K i j t := by
  rw [eichlerE_eq_leviE i j hij s]
  exact leviE_mul_radRoot_mul_inv (transvectionGL i j hij s) i j t
    (by rw [coe_transvectionGL]; exact transvection_mul_altUnit_mul_transpose_self i j hij s t)

private lemma eichlerE_conj_radRoot_swap (i j : Fin 4) (hij : i ≠ j) (s t : K) :
    eichlerE (K := K) j i s * radRoot 4 K i j t * (eichlerE (K := K) j i s)⁻¹ =
      radRoot 4 K i j t := by
  rw [eichlerE_eq_leviE j i (Ne.symm hij) s]
  refine leviE_mul_radRoot_mul_inv (transvectionGL j i (Ne.symm hij) s) i j t ?_
  rw [coe_transvectionGL]
  have h := transvection_mul_altUnit_mul_transpose_self j i (Ne.symm hij) s (-t)
  rwa [OrthogonalSplit.altUnit_swap, smul_neg, neg_smul, neg_neg] at h

private lemma eichlerE_conj_radRoot_disjoint (a b i j : Fin 4) (hab : a ≠ b)
    (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i) (hbj : b ≠ j) (s t : K) :
    eichlerE (K := K) a b s * radRoot 4 K i j t * (eichlerE (K := K) a b s)⁻¹ =
      radRoot 4 K i j t := by
  rw [eichlerE_eq_leviE a b hab s]
  exact leviE_mul_radRoot_mul_inv (transvectionGL a b hab s) i j t
    (by rw [coe_transvectionGL]
        exact transvection_mul_altUnit_mul_transpose_disjoint a b i j hai haj hbi hbj s t)

omit [Finite K] [CharP K 2] in
private lemma homAct_eq_self_of_centralizes
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h))
    {g u : orthElementaryGroup (quadPlus 4 K)}
    (hg : shift c m₀ g = 0) (hconj : g * u * g⁻¹ = u) :
    homAct g (shift c m₀ u) = shift c m₀ u := by
  have h1 : shift c m₀ (g * u * g⁻¹) = homAct g (shift c m₀ u) := by
    rw [shift_cocycle c m₀ hc, shift_inv_eq_zero c m₀ hc hg, homAct_zero, add_zero,
      shift_cocycle c m₀ hc, hg, zero_add]
  rw [← h1, hconj]

private lemma shift_apply_smul_eq_zero
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h))
    (hm : ∀ A : GL (Fin 4) K, c (leviE A) = homAct (leviE A) m₀ - m₀)
    (i j : Fin 4) (t : K) (a b : Fin 4) (hab : a ≠ b) (s : K)
    (hconj : eichlerE (K := K) a b s * radRoot 4 K i j t * (eichlerE (K := K) a b s)⁻¹ =
      radRoot 4 K i j t) :
    shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inl a) 1) = 0 ∧
      shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inr b) 1) = 0 := by
  have hshift : shift c m₀ (eichlerE (K := K) a b s) = 0 := by
    rw [eichlerE_eq_leviE a b hab s]
    exact shift_levi c m₀ hm _
  have hfix : homAct (eichlerE (K := K) a b s) (shift c m₀ (radRoot 4 K i j t)) =
      shift c m₀ (radRoot 4 K i j t) :=
    homAct_eq_self_of_centralizes c m₀ hc hshift hconj
  have hfixed : ∀ v, shift c m₀ (radRoot 4 K i j t)
      ((eichler (quadPlus 4 K) (Pi.single (Sum.inl a) 1)
        ((-s) • Pi.single (Sum.inr b) 1)) v) = shift c m₀ (radRoot 4 K i j t) v := by
    intro v
    exact fixedBy_of_homAct hfix v
  exact ⟨fixed_eichler_kills_inl hab hfixed, fixed_eichler_kills_inr hab hfixed⟩

private lemma shift_radRoot_eq_zero_of
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h))
    (hm : ∀ A : GL (Fin 4) K, c (leviE A) = homAct (leviE A) m₀ - m₀)
    (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (t : K) :
    shift c m₀ (radRoot 4 K i j t) = 0 := by
  have hcover : ∀ x : Fin 4, x = i ∨ x = j ∨ x = k ∨ x = l := by
    have hcard : ({i, j, k, l} : Finset (Fin 4)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hij, hki.symm, hli.symm]),
        Finset.card_insert_of_notMem (by simp [hkj.symm, hlj.symm]),
        Finset.card_insert_of_notMem (by simp [hkl]), Finset.card_singleton]
    have huniv : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ :=
      Finset.eq_univ_of_card _ hcard
    intro x
    have hmem : x ∈ ({i, j, k, l} : Finset (Fin 4)) := huniv.symm ▸ Finset.mem_univ x
    simpa using hmem
  have hkill_ij : ∀ s : K, shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inl i) 1) = 0 ∧
      shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inr j) 1) = 0 := fun s =>
    shift_apply_smul_eq_zero c m₀ hc hm i j t i j hij s
      (eichlerE_conj_radRoot_self i j hij s t)
  have hkill_ji : ∀ s : K, shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inl j) 1) = 0 ∧
      shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inr i) 1) = 0 := fun s =>
    shift_apply_smul_eq_zero c m₀ hc hm i j t j i (Ne.symm hij) s
      (eichlerE_conj_radRoot_swap i j hij s t)
  have hkill_kl : ∀ s : K, shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inl k) 1) = 0 ∧
      shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inr l) 1) = 0 := fun s =>
    shift_apply_smul_eq_zero c m₀ hc hm i j t k l hkl s
      (eichlerE_conj_radRoot_disjoint k l i j hkl hki hkj hli hlj s t)
  have hkill_lk : ∀ s : K, shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inl l) 1) = 0 ∧
      shift c m₀ (radRoot 4 K i j t) (s • Pi.single (Sum.inr k) 1) = 0 := fun s =>
    shift_apply_smul_eq_zero c m₀ hc hm i j t l k (Ne.symm hkl) s
      (eichlerE_conj_radRoot_disjoint l k i j (Ne.symm hkl) hli hlj hki hkj s t)
  have hsingle : ∀ (x : Fin 4 ⊕ Fin 4) (u : K),
      shift c m₀ (radRoot 4 K i j t) (u • Pi.single x 1) = 0 := by
    intro x u
    rcases x with a | a
    · rcases hcover a with rfl | rfl | rfl | rfl
      · exact (hkill_ij u).1
      · exact (hkill_ji u).1
      · exact (hkill_kl u).1
      · exact (hkill_lk u).1
    · rcases hcover a with rfl | rfl | rfl | rfl
      · exact (hkill_ji u).2
      · exact (hkill_ij u).2
      · exact (hkill_lk u).2
      · exact (hkill_kl u).2
  refine AddMonoidHom.ext fun v => ?_
  have hv : v = ∑ c : Fin 4 ⊕ Fin 4, v c • Pi.single c 1 := (sum_single_eq v).symm
  rw [hv, map_sum]
  exact Finset.sum_eq_zero fun c _ => hsingle c (v c)

private lemma exists_complement_pair (i j : Fin 4) :
    ∃ k l : Fin 4, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j := by
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact ⟨2, 3, by decide, by decide, by decide, by decide, by decide⟩
    | exact ⟨0, 3, by decide, by decide, by decide, by decide, by decide⟩
    | exact ⟨0, 1, by decide, by decide, by decide, by decide, by decide⟩
    | exact ⟨1, 2, by decide, by decide, by decide, by decide, by decide⟩
    | exact ⟨0, 2, by decide, by decide, by decide, by decide, by decide⟩
    | exact ⟨1, 3, by decide, by decide, by decide, by decide, by decide⟩

private lemma shift_radRoot_eq_zero
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h))
    (hm : ∀ A : GL (Fin 4) K, c (leviE A) = homAct (leviE A) m₀ - m₀)
    (i j : Fin 4) (hij : i ≠ j) (t : K) :
    shift c m₀ (radRoot 4 K i j t) = 0 := by
  obtain ⟨k, l, hkl, hki, hkj, hli, hlj⟩ := exists_complement_pair i j
  exact shift_radRoot_eq_zero_of c m₀ hc hm i j k l hij hkl hki hkj hli hlj t

omit [Finite K] [CharP K 2] in
private lemma eichler_inl_inl_eq_radRoot (i j : Fin 4) (hij : i ≠ j) (s : K) :
    (⟨eichler (quadPlus 4 K) (Pi.single (Sum.inl i) 1) ((-s) • Pi.single (Sum.inl j) 1),
      eichler_mem_elementaryGroup _ _ _⟩ : orthElementaryGroup (quadPlus 4 K)) =
      radRoot 4 K i j s := by
  have hmat : LinearMap.toMatrix' ((eichler (quadPlus 4 K) (Pi.single (Sum.inl i) 1)
      ((-s) • Pi.single (Sum.inl j) 1) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K]
        (Fin 4 ⊕ Fin 4 → K)) : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      LinearMap.toMatrix' (((radRoot 4 K i j s : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
          (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := by
    rw [← OrthogonalSplit.blockUnip_single hij s, OrthogonalSplit.coe_radRoot,
      OrthogonalSplit.toMatrix'_radical, toAdd_ofAdd]
    simp [OrthogonalSplit.altUnit]
  exact Subtype.ext (LinearEquiv.toLinearMap_injective (LinearMap.toMatrix'.injective hmat))

private lemma shift_maxStabGens
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h))
    (hm : ∀ A : GL (Fin 4) K, c (leviE A) = homAct (leviE A) m₀ - m₀)
    {x : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hx : x ∈ maxStabGens 4 K) (hxE : x ∈ orthElementaryGroup (quadPlus 4 K)) :
    shift c m₀ ⟨x, hxE⟩ = 0 := by
  rw [OrthogonalSplit.maxStabGens, Set.mem_union, Set.mem_union, Set.mem_range] at hx
  rcases hx with (⟨d, hd⟩ | ⟨i, j, s, hij, hd⟩) | ⟨i, j, s, hijlt, hd⟩
  · rw [show (⟨x, hxE⟩ : orthElementaryGroup (quadPlus 4 K)) = leviE (diagGL d) from
      Subtype.ext (hd.symm.trans (torusElt_eq_levi d))]
    exact shift_levi c m₀ hm _
  · rw [show (⟨x, hxE⟩ : orthElementaryGroup (quadPlus 4 K)) =
        leviE (transvectionGL i j hij s) from
      Subtype.ext (hd.trans (levi_transvection_eq_eichler i j hij s).symm)]
    exact shift_levi c m₀ hm _
  · rw [show (⟨x, hxE⟩ : orthElementaryGroup (quadPlus 4 K)) = radRoot 4 K i j s from
      Subtype.ext (hd.trans (congrArg Subtype.val
        (eichler_inl_inl_eq_radRoot i j (ne_of_lt hijlt) s)))]
    exact shift_radRoot_eq_zero c m₀ hc hm i j (ne_of_lt hijlt) s

private lemma shift_eq_zero_of_mem_maxStab
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (m₀ : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h))
    (hm : ∀ A : GL (Fin 4) K, c (leviE A) = homAct (leviE A) m₀ - m₀)
    {g : orthElementaryGroup (quadPlus 4 K)}
    (hg : ((g : orthElementaryGroup (quadPlus 4 K)) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K]
      (Fin 4 ⊕ Fin 4 → K)) ∈ maxStab 4 K) :
    shift c m₀ g = 0 := by
  have hkE : maxStabGens 4 K ⊆ (orthElementaryGroup (quadPlus 4 K) : Set _) := by
    intro x hx
    rw [OrthogonalSplit.maxStabGens, Set.mem_union, Set.mem_union, Set.mem_range] at hx
    rcases hx with (⟨d, rfl⟩ | ⟨i, j, s, hij, rfl⟩) | ⟨i, j, s, hijlt, rfl⟩
    · exact torusElt_mem_orthElementaryGroup (r := 4) (K := K) (by norm_num) d
    · exact eichler_mem_elementaryGroup _ _ _
    · exact eichler_mem_elementaryGroup _ _ _
  have hclos : Subgroup.closure (maxStabGens 4 K) ≤ orthElementaryGroup (quadPlus 4 K) :=
    (Subgroup.closure_le _).2 hkE
  rw [maxStab_eq_closure] at hg
  have hmain : ∀ (x : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
      (hx : x ∈ Subgroup.closure (maxStabGens 4 K)),
      shift c m₀ ⟨x, hclos hx⟩ = 0 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x hx => shift c m₀ ⟨x, hclos hx⟩ = 0) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact shift_maxStabGens c m₀ hc hm hy (hclos (Subgroup.subset_closure hy))
    · rw [show (⟨1, hclos (Subgroup.one_mem (Subgroup.closure (maxStabGens 4 K)))⟩ :
          orthElementaryGroup (quadPlus 4 K)) = 1 from Subtype.ext rfl]
      exact shift_one c m₀ hc
    · intro x y hx hy hpx hpy
      rw [show (⟨x * y, hclos (Subgroup.mul_mem (Subgroup.closure (maxStabGens 4 K)) hx hy)⟩ :
          orthElementaryGroup (quadPlus 4 K)) = ⟨x, hclos hx⟩ * ⟨y, hclos hy⟩ from
        Subtype.ext rfl]
      exact shift_mul_eq_zero c m₀ hc hpx hpy
    · intro x hx hpx
      rw [show (⟨x⁻¹, hclos (Subgroup.inv_mem (Subgroup.closure (maxStabGens 4 K)) hx)⟩ :
          orthElementaryGroup (quadPlus 4 K)) = (⟨x, hclos hx⟩)⁻¹ from Subtype.ext rfl]
      exact shift_inv_eq_zero c m₀ hc hpx
  have hfin := hmain ((g : orthElementaryGroup (quadPlus 4 K)) :
    (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) hg
  rwa [show (⟨((g : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)), hclos hg⟩ :
      orthElementaryGroup (quadPlus 4 K)) = g from Subtype.ext rfl] at hfin

private lemma odd_index_maxStab :
    ¬ 2 ∣ ((maxStab 4 K).subgroupOf (orthElementaryGroup (quadPlus 4 K))).index := by
  obtain ⟨S, hS⟩ := posUnip_isSylow (r := 4) (K := K) 2 (by norm_num)
    (fun a ha => map_flag_top_ne_Xstar (r := 4) (K := K) (by norm_num) ha)
  have hnot : ¬ 2 ∣ ((posUnip 4 K).subgroupOf
      (orthElementaryGroup (quadPlus 4 K))).index := by
    rw [← hS]
    exact S.not_dvd_index
  have hle : ((posUnip 4 K).subgroupOf (orthElementaryGroup (quadPlus 4 K))) ≤
      ((maxStab 4 K).subgroupOf (orthElementaryGroup (quadPlus 4 K))) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (mem_posBorel.1 (posUnip_le_posBorel hx)).1
  exact fun h => hnot (h.trans (Subgroup.index_dvd_of_le hle))

end Main

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit in
theorem exists_eq_homAct_sub [Finite K] [CharP K 2]
    (c : orthElementaryGroup (quadPlus 4 K) → ((Fin 4 ⊕ Fin 4 → K) →+ Z))
    (hc : ∀ g h, c (g * h) = c g + homAct g (c h)) :
    ∃ f : (Fin 4 ⊕ Fin 4 → K) →+ Z, ∀ g, c g = homAct g f - f := by
  obtain ⟨m₀, hm⟩ := exists_eq_levi_coboundary c hc
  have hvan : ∀ g ∈ (maxStab 4 K).subgroupOf (orthElementaryGroup (quadPlus 4 K)),
      shift c m₀ g = 0 := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    exact shift_eq_zero_of_mem_maxStab c m₀ hc hm hg
  let : Module (ZMod 2) ((Fin 4 ⊕ Fin 4 → K) →+ Z) :=
    AddCommGroup.zmodModule (n := 2) (fun f => addHom_two_nsmul f)
  let : DistribMulAction (orthElementaryGroup (quadPlus 4 K))
      ((Fin 4 ⊕ Fin 4 → K) →+ Z) :=
    { smul := homAct
      one_smul := homAct_one
      mul_smul := fun g h f => homAct_mul g h f
      smul_zero := homAct_zero
      smul_add := homAct_add }
  obtain ⟨m₁, hm₁⟩ := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.exists_coboundary_of_odd_index
    ((maxStab 4 K).subgroupOf (orthElementaryGroup (quadPlus 4 K))) odd_index_maxStab
    (shift c m₀) (shift_cocycle c m₀ hc) hvan
  refine ⟨m₀ + m₁, fun g => ?_⟩
  have h1 := hm₁ g
  rw [shift] at h1
  rw [homAct_add]
  calc c g = (c g - (homAct g m₀ - m₀)) + (homAct g m₀ - m₀) := by abel
    _ = (homAct g m₁ - m₁) + (homAct g m₀ - m₀) := by rw [h1]; rfl
    _ = homAct g m₀ + homAct g m₁ - (m₀ + m₁) := by abel


theorem eq_zero_of_homAct_eq (f : (Fin 4 ⊕ Fin 4 → K) →+ Z)
    (hf : ∀ g : orthElementaryGroup (quadPlus 4 K), homAct g f = f) : f = 0 := by
  have hsingle : ∀ (c : Fin 4 ⊕ Fin 4) (t : K), f (t • Pi.single c 1) = 0 := by
    intro c t
    rcases c with a | a
    · obtain ⟨b, hb⟩ := exists_ne a
      exact fixed_eichler_kills_inl (f := f) (a := a) (b := b) hb.symm (s := t)
        (fixedBy_of_homAct (g := ⟨eichler (quadPlus 4 K) (Pi.single (Sum.inl a) 1)
          ((-t) • Pi.single (Sum.inr b) 1), eichler_mem_elementaryGroup _ _ _⟩) (hf _))
    · obtain ⟨b, hb⟩ := exists_ne a
      exact fixed_eichler_kills_inr (f := f) (a := b) (b := a) hb (s := t)
        (fixedBy_of_homAct (g := ⟨eichler (quadPlus 4 K) (Pi.single (Sum.inl b) 1)
          ((-t) • Pi.single (Sum.inr a) 1), eichler_mem_elementaryGroup _ _ _⟩) (hf _))
  refine AddMonoidHom.ext fun v => ?_
  have hv : v = ∑ c : Fin 4 ⊕ Fin 4, v c • Pi.single c 1 := (sum_single_eq v).symm
  rw [hv, map_sum]
  exact Finset.sum_eq_zero fun c _ => hsingle c (v c)


end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
