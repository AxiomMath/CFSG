module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDPair

public section

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] {n : ℕ}

section KLin

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]} {f : L[X]} {T : (Fin n → L) →ₗ[L] (Fin n → L)}

theorem comm_pow_of_comm {A : (Fin n → L) →ₗ[L] (Fin n → L)} (hA : ∀ x, A (s *ᵥ x) = s *ᵥ A x)
    (k : ℕ) (x : Fin n → L) : A ((s ^ k) *ᵥ x) = (s ^ k) *ᵥ A x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih, hA]

theorem comm_aeval_of_comm {A : (Fin n → L) →ₗ[L] (Fin n → L)} (hA : ∀ x, A (s *ᵥ x) = s *ᵥ A x)
    (q : L[X]) (x : Fin n → L) : A (aeval s q *ᵥ x) = aeval s q *ᵥ A x := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.add_mulVec, map_add, hp, hq, Matrix.add_mulVec]
  | monomial k c =>
    have hm : ∀ y, aeval s (monomial k c : L[X]) *ᵥ y = c • ((s ^ k) *ᵥ y) := by
      intro y
      rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        Matrix.smul_mulVec]
    rw [hm, map_smul, comm_pow_of_comm hA k x, hm]

theorem pow_root_comm [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)] {A : Vf s b F f →ₗ[L] Vf s b F f}
    (hA : ∀ y : Vf s b F f, AdjoinRoot.root f • A y = A (AdjoinRoot.root f • y))
    (k : ℕ) (y : Vf s b F f) : A ((AdjoinRoot.root f ^ k) • y) = (AdjoinRoot.root f ^ k) • A y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ← hA, ih, mul_smul]

theorem KLin_mk_comm [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]
    (A : Vf s b F f →ₗ[L] Vf s b F f)
    (hA : ∀ y : Vf s b F f, AdjoinRoot.root f • A y = A (AdjoinRoot.root f • y))
    (q : L[X]) (y : Vf s b F f) :
    A (AdjoinRoot.mk f q • y) = AdjoinRoot.mk f q • A y := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_smul, map_add, hp, hq, add_smul]
  | monomial k c =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      ← AdjoinRoot.algebraMap_eq, mul_smul, mul_smul, algebraMap_smul, algebraMap_smul,
      map_smul, pow_root_comm hA k y]

@[expose] noncomputable def KLin [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]
    (A : Vf s b F f →ₗ[L] Vf s b F f)
    (hA : ∀ y : Vf s b F f, AdjoinRoot.root f • A y = A (AdjoinRoot.root f • y)) :
    Vf s b F f →ₗ[AdjoinRoot f] Vf s b F f where
  toFun := A
  map_add' := A.map_add
  map_smul' c y := by
    induction c using AdjoinRoot.induction_on with
    | ih q => exact KLin_mk_comm A hA q y

theorem Pmat_comm_of_comm {T : (Fin n → L) →ₗ[L] (Fin n → L)} (hTs : ∀ x, T (s *ᵥ x) = s *ᵥ T x)
    (g : L[X]) (x : Fin n → L) : T (aeval s g *ᵥ x) = aeval s g *ᵥ T x :=
  comm_aeval_of_comm hTs g x

@[expose] noncomputable def restrV (hTs : ∀ x, T (s *ᵥ x) = s *ᵥ T x) :
    Vf s b F f →ₗ[L] Vf s b F f :=
  T.restrict (fun y hy => by
    rw [mem_Vf] at hy ⊢
    have hc : T (Pmat s b F f *ᵥ y) = Pmat s b F f *ᵥ T y :=
      comm_aeval_of_comm hTs (b f * gcF F f) y
    rw [hy] at hc
    exact hc.symm)

theorem coe_restrV (hTs : ∀ x, T (s *ᵥ x) = s *ᵥ T x) (y : Vf s b F f) :
    ((restrV hTs y : Vf s b F f) : Fin n → L) = T (y : Fin n → L) := rfl

theorem restrV_hA [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]
    (hTs : ∀ x, T (s *ᵥ x) = s *ᵥ T x) (y : Vf s b F f) :
    AdjoinRoot.root f • restrV hTs y = restrV hTs (AdjoinRoot.root f • y) := by
  apply Subtype.ext
  rw [coe_root_smul, coe_restrV, coe_restrV, coe_root_smul, hTs]

@[expose] noncomputable def KLinT [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]
    (hTs : ∀ x, T (s *ᵥ x) = s *ᵥ T x) : Vf s b F f →ₗ[AdjoinRoot f] Vf s b F f :=
  KLin (restrV hTs) (restrV_hA hTs)

theorem KLinT_apply [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]
    (hTs : ∀ x, T (s *ᵥ x) = s *ᵥ T x) (y : Vf s b F f) :
    ((KLinT hTs y : Vf s b F f) : Fin n → L) = T (y : Fin n → L) := rfl

theorem comm_inv_units (g : ((Fin n → L) →ₗ[L] (Fin n → L))ˣ)
    (hg : ∀ x, (g : (Fin n → L) →ₗ[L] (Fin n → L)) (s *ᵥ x) =
      s *ᵥ (g : (Fin n → L) →ₗ[L] (Fin n → L)) x) :
    ∀ x, (↑g⁻¹ : (Fin n → L) →ₗ[L] (Fin n → L)) (s *ᵥ x) =
      s *ᵥ (↑g⁻¹ : (Fin n → L) →ₗ[L] (Fin n → L)) x := by
  have e1 : ∀ z, (↑g : (Fin n → L) →ₗ[L] (Fin n → L)) ((↑g⁻¹ : (Fin n → L) →ₗ[L] (Fin n → L)) z) = z :=
    fun z => by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
  have e2 : ∀ z, (↑g⁻¹ : (Fin n → L) →ₗ[L] (Fin n → L)) ((↑g : (Fin n → L) →ₗ[L] (Fin n → L)) z) = z :=
    fun z => by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
  intro x
  have h2 : (↑g : (Fin n → L) →ₗ[L] (Fin n → L)) (s *ᵥ (↑g⁻¹ : (Fin n → L) →ₗ[L] (Fin n → L)) x) =
      s *ᵥ x := by
    rw [hg, e1]
  calc (↑g⁻¹ : (Fin n → L) →ₗ[L] (Fin n → L)) (s *ᵥ x)
      = (↑g⁻¹ : (Fin n → L) →ₗ[L] (Fin n → L)) ((↑g : (Fin n → L) →ₗ[L] (Fin n → L))
          (s *ᵥ (↑g⁻¹ : (Fin n → L) →ₗ[L] (Fin n → L)) x)) := by rw [h2]
    _ = s *ᵥ (↑g⁻¹ : (Fin n → L) →ₗ[L] (Fin n → L)) x := e2 _

end KLin


section Glin

abbrev Vend (L : Type) [Field L] (n : ℕ) : Type := (Fin n → L) →ₗ[L] (Fin n → L)

@[expose] def Glin (τ : L ≃+* L) (s : Matrix (Fin n) (Fin n) L) : Subgroup (Vend L n)ˣ where
  carrier := {g | (∀ x, (g.val : Vend L n) (s *ᵥ x) = s *ᵥ (g.val : Vend L n) x) ∧
      ∀ x y, hfm τ ((g.val : Vend L n) x) ((g.val : Vend L n) y) = hfm τ x y}
  one_mem' := ⟨fun x => rfl, fun x y => rfl⟩
  mul_mem' := by
    rintro g h ⟨hgs, hgu⟩ ⟨hhs, hhu⟩
    refine ⟨fun x => ?_, fun x y => ?_⟩
    · show ((g.val * h.val : Vend L n)) (s *ᵥ x) = s *ᵥ ((g.val * h.val : Vend L n)) x
      rw [Module.End.mul_apply, hhs, hgs, Module.End.mul_apply]
    · show hfm τ ((g.val * h.val : Vend L n) x) ((g.val * h.val : Vend L n) y) = hfm τ x y
      rw [Module.End.mul_apply, Module.End.mul_apply, hgu, hhu]
  inv_mem' := by
    rintro g ⟨hgs, hgu⟩
    refine ⟨comm_inv_units g hgs, fun x y => ?_⟩
    have e1 : ∀ z, (g.val : Vend L n) ((g⁻¹).val z) = z := fun z => by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    have h := hgu ((g⁻¹).val x) ((g⁻¹).val y)
    rw [e1, e1] at h
    exact h.symm

end Glin

section ResU

variable {τ : L ≃+* L} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {b : L[X] → L[X]} {f : L[X]}

theorem Glin_comm {g : (Vend L n)ˣ} (hg : g ∈ Glin τ s) :
    ∀ x, (g.val : Vend L n) (s *ᵥ x) = s *ᵥ (g.val : Vend L n) x := hg.1

theorem mul_inv_val_apply (g : (Vend L n)ˣ) (z : Fin n → L) :
    (g.val : Vend L n) ((g⁻¹).val z) = z := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Module.End.one_apply]

theorem inv_mul_val_apply (g : (Vend L n)ˣ) (z : Fin n → L) :
    (g⁻¹).val ((g.val : Vend L n) z) = z := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]

@[expose] noncomputable def resU [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]
    (g : (Vend L n)ˣ) (hg : g ∈ Glin τ s) :
    (Vf s b F f →ₗ[AdjoinRoot f] Vf s b F f)ˣ where
  val := KLinT (T := (g.val : Vend L n)) (Glin_comm hg)
  inv := KLinT (T := ((g⁻¹).val : Vend L n)) (comm_inv_units g (Glin_comm hg))
  val_inv := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    simp only [Module.End.mul_apply, Module.End.one_apply, KLinT_apply, mul_inv_val_apply]
  inv_val := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    simp only [Module.End.mul_apply, Module.End.one_apply, KLinT_apply, inv_mul_val_apply]

theorem coe_resU [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)] (g : (Vend L n)ˣ)
    (hg : g ∈ Glin τ s) (y : Vf s b F f) :
    ((resU g hg : (Vf s b F f →ₗ[AdjoinRoot f] Vf s b F f)ˣ).val y : Fin n → L) =
      (g.val : Vend L n) (y : Fin n → L) := by
  exact KLinT_apply _ y

end ResU

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
