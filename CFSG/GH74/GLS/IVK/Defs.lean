module

public import CFSG.GH74.GLS.Pattern
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG Blueprint CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open scoped MatrixGroups Pointwise

abbrev L2 (F : Type) [Field F] : Type := StatedProj (StatedSL 2 F)

abbrev SL2 (F : Type) [Field F] : Type := ↥(StatedSL 2 F)

@[expose] def L2Field (F : Type) [Field F] [Finite F] : Prop :=
  Odd (Nat.card F) ∧ 3 < Nat.card F

@[expose] noncomputable def L2.equivPSL (F : Type) [Field F] : L2 F ≃* PSL2 F :=
  (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm

@[expose] def innAut (K : Type) [Group K] : Subgroup (MulAut K) :=
  (MulAut.conj : K →* MulAut K).range

section Aut

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

@[expose] noncomputable def toPSL (e : K ≃* L2 F) : K ≃* PSL2 F := e.trans (L2.equivPSL F)

@[expose] noncomputable def fieldAutHom (e : K ≃* L2 F) : (F ≃+* F) →* MulAut K :=
  (MulAut.congr (toPSL e)).symm.toMonoidHom.comp (psl2FieldAut F)

@[expose] noncomputable def innDiagHom (e : K ≃* L2 F) : PGL2 F →* MulAut K :=
  (MulAut.congr (toPSL e)).symm.toMonoidHom.comp
    ((ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut F).toMonoidHom.comp
      (SemidirectProduct.inl : PGL2 F →* PGammaL2 F))

@[expose] noncomputable def fieldAutSub (e : K ≃* L2 F) : Subgroup (MulAut K) :=
  (fieldAutHom e).range

@[expose] noncomputable def innDiagSub (e : K ≃* L2 F) : Subgroup (MulAut K) :=
  (innDiagHom e).range

end Aut

@[expose] noncomputable def L2.mk (F : Type) [Field F] : SL2 F →* L2 F := QuotientGroup.mk' _

@[expose] noncomputable def slFixed {F : Type} [Field F] (σ : F ≃+* F) : Subgroup (SL2 F) :=
  MonoidHom.eqLocus ((Matrix.GeneralLinearGroup.map σ.toRingHom).comp (StatedSL 2 F).subtype)
    (StatedSL 2 F).subtype

@[expose] def slCentralizer {F : Type} [Field F] (g : GL (Fin 2) F) : Subgroup (SL2 F) :=
  (centralizer ({g} : Set (GL (Fin 2) F))).comap (StatedSL 2 F).subtype

@[expose] noncomputable def uHom (F : Type) [Field F] : Multiplicative F →* GL (Fin 2) F where
  toFun t := ⟨!![1, t.toAdd; 0, 1], !![1, -t.toAdd; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp, by
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]

@[expose] noncomputable def diagGL (F : Type) [Field F] : Subgroup (GL (Fin 2) F) :=
  ((Units.map (Matrix.diagonalRingHom (Fin 2) F).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin 2 => F)).symm.toMonoidHom).range

@[expose] def wGL (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp, by
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩

section Preds

variable {X : Type} [Group X]

@[expose] def invol (X : Type) [Group X] : Set X := {x | orderOf x = 2}

@[expose] def ConjUnder (A : Subgroup X) (x y : X) : Prop := ∃ a ∈ A, a * x * a⁻¹ = y

@[expose] def IsFourSubgroup (U : Subgroup X) : Prop :=
  IsElementaryAbelian 2 ↥U ∧ Nat.card ↥U = 4

@[expose] def IsDihedralOrder (Y : Type) [Group Y] (m : ℕ) : Prop :=
  ∃ k : ℕ, m = 2 * k ∧ 2 ≤ k ∧ Nonempty (Y ≃* DihedralGroup k)

@[expose] def IsDihedralTwoGroup (Y : Type) [Group Y] (n : ℕ) : Prop :=
  2 ≤ n ∧ IsDihedralOrder Y (2 ^ n)

end Preds

section Aut2

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

@[expose] def autNormalizer (A : Subgroup (MulAut K)) (X : Subgroup K) : Subgroup (MulAut K) :=
  A ⊓ MulAction.stabilizer (MulAut K) X

@[expose] def IsFAutL2 (α : MulAut K) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* L2 F), α ∈ fieldAutSub e

@[expose] def xu (u : MulAut K) : Subgroup K :=
  (pPrimeCore 2 ↥(fixedSubgroup K u)).map (fixedSubgroup K u).subtype

@[expose] def xuInn (u : MulAut K) : Subgroup (MulAut K) := (xu u).map (MulAut.conj : K →* MulAut K)

end Aut2

@[expose] def IsL2 (X : Type) [Group X] (P : ℕ → Prop) : Prop :=
  ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), P (Nat.card F₀) ∧ Nonempty (X ≃* L2 F₀)

@[expose] def IsPGL2 (X : Type) [Group X] (P : ℕ → Prop) : Prop :=
  ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), P (Nat.card F₀) ∧ Nonempty (X ≃* PGL2 F₀)

section Preds2

variable {X : Type} [Group X]

@[expose] def IsFrobeniusSplit (W D G : Subgroup X) : Prop :=
  W ≤ G ∧ D ≤ G ∧ (W.subgroupOf G).Normal ∧ W ⊔ D = G ∧ W ⊓ D = ⊥ ∧
    ∀ d ∈ D, d ≠ 1 → ∀ w ∈ W, d * w = w * d → w = 1

@[expose] def IsSemidihedralTwoGroup (Y : Type) [Group Y] (n : ℕ) : Prop :=
  4 ≤ n ∧ Nonempty (Y ≃* Open.SemidihedralGroup n)

@[expose] def IsQuaternionTwoGroup (Y : Type) [Group Y] (n : ℕ) : Prop :=
  3 ≤ n ∧ Nonempty (Y ≃* QuaternionGroup (2 ^ (n - 2)))

end Preds2

section Notation

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

structure L2Notation (e : K ≃* L2 F) where
  T : Sylow 2 (MulAut K)
  t : MulAut K
  t_mem : t ∈ (T : Subgroup (MulAut K))
  t_order : orderOf t = 2
  t_mem_diag : t ∈ innDiagSub e
  t_not_mem_inn : t ∉ innAut K
  T_inv : fieldAutSub e ≤ normalizer ((T : Subgroup (MulAut K)) : Set (MulAut K))
  R_cent : ∀ f ∈ (T : Subgroup (MulAut K)) ⊓ fieldAutSub e, orderOf f = 2 →
    ∀ x ∈ (T : Subgroup (MulAut K)) ⊓ innAut K, x * f = f * x
  F_odd_cent : ∀ f ∈ fieldAutSub e, Odd (orderOf f) → ∀ x ∈ (T : Subgroup (MulAut K)), x * f = f * x
  four_cent : ∃ U : Subgroup (MulAut K), U ≤ (T : Subgroup (MulAut K)) ⊓ innAut K ∧ IsFourSubgroup U ∧
    ∀ φ ∈ fieldAutSub e, ∀ u ∈ U, φ * u = u * φ

namespace L2Notation

variable {e : K ≃* L2 F} (N : L2Notation e)

@[expose] noncomputable def P : Subgroup (MulAut K) := (N.T : Subgroup (MulAut K)) ⊓ innAut K

@[expose] noncomputable def Pt : Subgroup (MulAut K) := (N.T : Subgroup (MulAut K)) ⊓ innDiagSub e

@[expose] noncomputable def R : Subgroup (MulAut K) := (N.T : Subgroup (MulAut K)) ⊓ fieldAutSub e

end L2Notation

end Notation

end CFSG.GH74.GLS.IVK
