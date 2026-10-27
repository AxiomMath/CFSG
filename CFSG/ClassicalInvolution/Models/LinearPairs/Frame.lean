module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ClassicalInvolution.Models

open Module

section AdaptedBasis

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {S : Type*} [DecidableEq S]

theorem exists_basis_adapted {n : ℕ} (E : S → Submodule K V) (hE : DirectSum.IsInternal E)
    (ε : Fin n → S) (hε : ∀ s, Nat.card {j // ε j = s} = finrank K (E s)) :
    ∃ b : Module.Basis (Fin n) K V, ∀ j, b j ∈ E (ε j) := by
  let v : ∀ s, Module.Basis (Fin (finrank K (E s))) K (E s) := fun s => Module.finBasis K (E s)
  let e : Fin n ≃ Σ s, Fin (finrank K (E s)) :=
    (Equiv.sigmaFiberEquiv ε).symm.trans
      (Equiv.sigmaCongrRight fun s => Finite.equivFinOfCardEq (hε s))
  refine ⟨(hE.collectedBasis v).reindex e.symm, fun j => ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm]
  exact hE.collectedBasis_mem v (e j)

theorem finrank_eq_sum_of_isInternal [Fintype S] (E : S → Submodule K V)
    (hE : DirectSum.IsInternal E) : finrank K V = ∑ s, finrank K (E s) := by
  let v : ∀ s, Module.Basis (Fin (finrank K (E s))) K (E s) := fun s => Module.finBasis K (E s)
  rw [Module.finrank_eq_card_basis (hE.collectedBasis v), Fintype.card_sigma]
  simp

end AdaptedBasis

section Joint

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable (K) in
@[expose] def signOf (b : Bool) : K := if b then 1 else -1

@[simp] theorem signOf_true : signOf K true = 1 := rfl

@[simp] theorem signOf_false : signOf K false = -1 := rfl

theorem signOf_mul_self (b : Bool) : signOf K b * signOf K b = 1 := by
  cases b <;> simp

@[expose] def jointEigenspace (f g : Module.End K V) (s : Bool × Bool) : Submodule K V :=
  f.eigenspace (signOf K s.1) ⊓ g.eigenspace (signOf K s.2)

theorem mem_jointEigenspace {f g : Module.End K V} {s : Bool × Bool} {v : V} :
    v ∈ jointEigenspace f g s ↔ f v = signOf K s.1 • v ∧ g v = signOf K s.2 • v := by
  simp [jointEigenspace]

@[expose] def jointProj (f g : Module.End K V) (s : Bool × Bool) : Module.End K V :=
  ((4 : K)⁻¹) • ((1 + signOf K s.1 • f) * (1 + signOf K s.2 • g))

variable {f g : Module.End K V}

theorem f_mul_jointProj (hf : f * f = 1) (s : Bool × Bool) :
    f * jointProj f g s = signOf K s.1 • jointProj f g s := by
  have hA : f * (1 + signOf K s.1 • f) = signOf K s.1 • (1 + signOf K s.1 • f) := by
    rw [mul_add, mul_one, mul_smul_comm, hf, smul_add, smul_smul, signOf_mul_self, one_smul,
      add_comm]
  unfold jointProj
  rw [mul_smul_comm, ← mul_assoc, hA, smul_mul_assoc, smul_comm]

theorem g_mul_jointProj (hg : g * g = 1) (hfg : f * g = g * f) (s : Bool × Bool) :
    g * jointProj f g s = signOf K s.2 • jointProj f g s := by
  have hB : g * (1 + signOf K s.2 • g) = signOf K s.2 • (1 + signOf K s.2 • g) := by
    rw [mul_add, mul_one, mul_smul_comm, hg, smul_add, smul_smul, signOf_mul_self, one_smul,
      add_comm]
  have hc : g * (1 + signOf K s.1 • f) = (1 + signOf K s.1 • f) * g := by
    rw [mul_add, mul_one, mul_smul_comm, ← hfg, add_mul, one_mul, smul_mul_assoc]
  unfold jointProj
  rw [mul_smul_comm, ← mul_assoc, hc, mul_assoc, hB, mul_smul_comm, smul_comm]

theorem four_ne_zero_of_two_ne_zero (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

theorem sum_jointProj (h2 : (2 : K) ≠ 0) : ∑ s, jointProj f g s = 1 := by
  have h4 := four_ne_zero_of_two_ne_zero h2
  have e1 : ∑ x : Bool, (1 + signOf K x • f) = (2 : K) • (1 : Module.End K V) := by
    rw [Fintype.sum_bool]
    simp only [signOf_true, signOf_false, one_smul, neg_smul]
    rw [two_smul]
    abel
  have e2 : ∑ y : Bool, (1 + signOf K y • g) = (2 : K) • (1 : Module.End K V) := by
    rw [Fintype.sum_bool]
    simp only [signOf_true, signOf_false, one_smul, neg_smul]
    rw [two_smul]
    abel
  calc ∑ s, jointProj f g s
      = (4 : K)⁻¹ • ∑ x : Bool, ∑ y : Bool, ((1 + signOf K x • f) * (1 + signOf K y • g)) := by
        rw [Fintype.sum_prod_type]
        simp only [jointProj, Finset.smul_sum]
    _ = (4 : K)⁻¹ • ((∑ x : Bool, (1 + signOf K x • f)) * (∑ y : Bool, (1 + signOf K y • g))) := by
        rw [Finset.sum_mul_sum]
    _ = 1 := by
        rw [e1, e2, smul_mul_smul_comm, mul_one, smul_smul]
        have : (4 : K)⁻¹ * (2 * 2) = 1 := by field_simp; norm_num
        rw [this, one_smul]

theorem jointProj_apply_of_mem (h2 : (2 : K) ≠ 0) {t : Bool × Bool} {v : V}
    (hv : v ∈ jointEigenspace f g t) (s : Bool × Bool) :
    jointProj f g s v = if s = t then v else 0 := by
  obtain ⟨hfv, hgv⟩ := mem_jointEigenspace.mp hv
  have h4 := four_ne_zero_of_two_ne_zero h2
  have key : jointProj f g s v = ((4 : K)⁻¹ * ((1 + signOf K s.1 * signOf K t.1) *
      (1 + signOf K s.2 * signOf K t.2))) • v := by
    simp only [jointProj, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.add_apply,
      Module.End.one_apply, map_add, map_smul, hfv, hgv, smul_smul]
    module
  rw [key]
  have h44 : (4 : K)⁻¹ * 4 = 1 := inv_mul_cancel₀ h4
  rcases s with ⟨_ | _, _ | _⟩ <;> rcases t with ⟨_ | _, _ | _⟩ <;> simp
  all_goals rw [show ((1 : K) + 1) * (1 + 1) = 4 by norm_num, h44, one_smul]

theorem jointProj_mem (hf : f * f = 1) (hg : g * g = 1) (hfg : f * g = g * f)
    (s : Bool × Bool) (v : V) : jointProj f g s v ∈ jointEigenspace f g s := by
  rw [mem_jointEigenspace]
  constructor
  · have := LinearMap.congr_fun (f_mul_jointProj (g := g) hf s) v
    simpa using this
  · have := LinearMap.congr_fun (g_mul_jointProj (f := f) hg hfg s) v
    simpa using this

theorem eq_sum_jointProj (h2 : (2 : K) ≠ 0) (v : V) : v = ∑ s, jointProj f g s v := by
  have := LinearMap.congr_fun (sum_jointProj (f := f) (g := g) h2) v
  simpa [LinearMap.sum_apply] using this.symm

theorem iSup_jointEigenspace (h2 : (2 : K) ≠ 0) (hf : f * f = 1) (hg : g * g = 1)
    (hfg : f * g = g * f) : ⨆ s, jointEigenspace f g s = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [eq_sum_jointProj (f := f) (g := g) h2 v]
  exact Submodule.sum_mem _ fun s _ =>
    Submodule.mem_iSup_of_mem s (jointProj_mem hf hg hfg s v)

theorem iSupIndep_jointEigenspace (h2 : (2 : K) ≠ 0) : iSupIndep (jointEigenspace f g) := by
  rw [iSupIndep_def]
  intro s
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ t, ⨆ (_ : t ≠ s), jointEigenspace f g t) ≤ LinearMap.ker (jointProj f g s) := by
    refine iSup₂_le fun t ht v hv => ?_
    rw [LinearMap.mem_ker, jointProj_apply_of_mem h2 hv, ite_eq_right (Ne.symm ht)]
  have h1 := hle hx'
  rw [LinearMap.mem_ker, jointProj_apply_of_mem h2 hx, ite_eq_left rfl] at h1
  exact h1

theorem isInternal_jointEigenspace (h2 : (2 : K) ≠ 0) (hf : f * f = 1) (hg : g * g = 1)
    (hfg : f * g = g * f) : DirectSum.IsInternal (jointEigenspace f g) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_jointEigenspace h2, iSup_jointEigenspace h2 hf hg hfg⟩

theorem eigenspace_eq_sup_jointEigenspace (h2 : (2 : K) ≠ 0) (hg : g * g = 1)
    (hfg : f * g = g * f) (a : Bool) :
    f.eigenspace (signOf K a) = jointEigenspace f g (a, true) ⊔ jointEigenspace f g (a, false) := by
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    have hgg : ∀ w, g (g w) = w := fun w => by
      simpa using LinearMap.congr_fun hg w
    have hgf : ∀ w, f (g w) = g (f w) := fun w => by
      simpa using LinearMap.congr_fun hfg w
    have hv' : v = (2 : K)⁻¹ • (v + g v) + (2 : K)⁻¹ • (v - g v) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul K v, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hv']
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mem_jointEigenspace]
      refine ⟨?_, ?_⟩
      · simp only [map_smul, map_add, hgf, hv]
        module
      · simp only [map_smul, map_add, hgg, signOf_true]
        module
    · rw [mem_jointEigenspace]
      refine ⟨?_, ?_⟩
      · simp only [map_smul, map_sub, hgf, hv]
        module
      · simp only [map_smul, map_sub, hgg, signOf_false]
        module
  · exact sup_le inf_le_left inf_le_left

theorem jointEigenspace_swap (f g : Module.End K V) (s : Bool × Bool) :
    jointEigenspace g f s.swap = jointEigenspace f g s :=
  inf_comm _ _

theorem disjoint_jointEigenspace (h2 : (2 : K) ≠ 0) (a : Bool) :
    Disjoint (jointEigenspace f g (a, true)) (jointEigenspace f g (a, false)) := by
  rw [Submodule.disjoint_def]
  intro x hx1 hx2
  rw [mem_jointEigenspace] at hx1 hx2
  have h := hx1.2.symm.trans hx2.2
  simp only [signOf_true, signOf_false, one_smul, neg_smul] at h
  have h' : (2 : K) • x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel x
  exact (smul_eq_zero.mp h').resolve_left h2

section FiniteDimensional

variable [FiniteDimensional K V]

theorem finrank_eigenspace_eq (h2 : (2 : K) ≠ 0) (hg : g * g = 1) (hfg : f * g = g * f)
    (a : Bool) :
    finrank K (f.eigenspace (signOf K a)) =
      finrank K (jointEigenspace f g (a, true)) + finrank K (jointEigenspace f g (a, false)) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (jointEigenspace f g (a, true))
    (jointEigenspace f g (a, false))
  rw [(disjoint_jointEigenspace h2 a).eq_bot, finrank_bot,
    ← eigenspace_eq_sup_jointEigenspace h2 hg hfg a] at h
  omega

theorem finrank_eigenspace_eq' (h2 : (2 : K) ≠ 0) (hf : f * f = 1) (hfg : f * g = g * f)
    (b : Bool) :
    finrank K (g.eigenspace (signOf K b)) =
      finrank K (jointEigenspace f g (true, b)) + finrank K (jointEigenspace f g (false, b)) := by
  have h := finrank_eigenspace_eq (f := g) (g := f) h2 hf hfg.symm b
  rw [show jointEigenspace g f (b, true) = jointEigenspace f g (true, b) from
    jointEigenspace_swap f g (true, b), show jointEigenspace g f (b, false) =
    jointEigenspace f g (false, b) from jointEigenspace_swap f g (false, b)] at h
  exact h

end FiniteDimensional

theorem eq_of_jointEigenspace_mixed_eq_bot (h2 : (2 : K) ≠ 0) (hf : f * f = 1) (hg : g * g = 1)
    (hfg : f * g = g * f) (h₁ : jointEigenspace f g (true, false) = ⊥)
    (h₂ : jointEigenspace f g (false, true) = ⊥) : f = g := by
  refine LinearMap.ext fun v => ?_
  have hv := eq_sum_jointProj (f := f) (g := g) h2 v
  calc f v = f (∑ s, jointProj f g s v) := congrArg f hv
    _ = ∑ s, f (jointProj f g s v) := map_sum _ _ _
    _ = ∑ s, g (jointProj f g s v) := ?_
    _ = g (∑ s, jointProj f g s v) := (map_sum _ _ _).symm
    _ = g v := congrArg g hv.symm
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs := jointProj_mem hf hg hfg s v
  rcases s with ⟨_ | _, _ | _⟩
  · obtain ⟨e1, e2⟩ := mem_jointEigenspace.mp hs
    rw [e1, e2]
  · rw [h₂] at hs
    rw [(Submodule.mem_bot K).mp hs, map_zero, map_zero]
  · rw [h₁] at hs
    rw [(Submodule.mem_bot K).mp hs, map_zero, map_zero]
  · obtain ⟨e1, e2⟩ := mem_jointEigenspace.mp hs
    rw [e1, e2]

end Joint

section Matrices

open Matrix
open scoped MatrixGroups

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def eigSpace (i : Matrix (Fin n) (Fin n) K) (c : K) : Submodule K (Fin n → K) :=
  Module.End.eigenspace (Matrix.toLin' i) c

theorem mem_eigSpace {i : Matrix (Fin n) (Fin n) K} {c : K} {v : Fin n → K} :
    v ∈ eigSpace i c ↔ i *ᵥ v = c • v := by
  simp [eigSpace]

theorem mem_eigSpace_neg_one {i : Matrix (Fin n) (Fin n) K} {v : Fin n → K} :
    v ∈ eigSpace i (-1) ↔ i *ᵥ v = -v := by
  rw [mem_eigSpace, neg_one_smul]

theorem mem_eigSpace_one {i : Matrix (Fin n) (Fin n) K} {v : Fin n → K} :
    v ∈ eigSpace i 1 ↔ i *ᵥ v = v := by
  rw [mem_eigSpace, one_smul]

@[expose] def jointEig (i₁ i₂ : Matrix (Fin n) (Fin n) K) (s : Bool × Bool) :
    Submodule K (Fin n → K) :=
  jointEigenspace (Matrix.toLin' i₁) (Matrix.toLin' i₂) s

theorem mem_jointEig {i₁ i₂ : Matrix (Fin n) (Fin n) K} {s : Bool × Bool} {v : Fin n → K} :
    v ∈ jointEig i₁ i₂ s ↔ i₁ *ᵥ v = signOf K s.1 • v ∧ i₂ *ᵥ v = signOf K s.2 • v := by
  simp [jointEig, mem_jointEigenspace]

theorem toLin'_mul_self {i : Matrix (Fin n) (Fin n) K} (h : i * i = 1) :
    Matrix.toLin' i * Matrix.toLin' i = 1 := by
  rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h, Matrix.toLin'_one]
  rfl

theorem toLin'_mul_comm {i₁ i₂ : Matrix (Fin n) (Fin n) K} (h : i₁ * i₂ = i₂ * i₁) :
    Matrix.toLin' i₁ * Matrix.toLin' i₂ = Matrix.toLin' i₂ * Matrix.toLin' i₁ := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, h]

theorem exists_sl_adapted {S : Type*} [DecidableEq S] (hn : 0 < n)
    (E : S → Submodule K (Fin n → K)) (hE : DirectSum.IsInternal E) (ε : Fin n → S)
    (hε : ∀ s, Nat.card {j // ε j = s} = finrank K (E s)) :
    ∃ P : SL(n, K), ∀ j, (fun a => (P : Matrix (Fin n) (Fin n) K) a j) ∈ E (ε j) := by
  obtain ⟨b, hb⟩ := exists_basis_adapted E hE ε hε
  let P0 : Matrix (Fin n) (Fin n) K := Matrix.of fun a j => b j a
  have hdet : IsUnit P0.det := by
    have : P0 = (Pi.basisFun K (Fin n)).toMatrix b := by
      ext a j
      simp [P0, Module.Basis.toMatrix_apply]
    rw [this, ← Module.Basis.det_apply]
    exact (Pi.basisFun K (Fin n)).isUnit_det b
  let last : Fin n := ⟨n - 1, by omega⟩
  let d : Fin n → K := Function.update 1 last (P0.det)⁻¹
  have hd : ∏ j, d j = (P0.det)⁻¹ :=
    (Fintype.prod_eq_single last fun j hj => by simp [d, hj]).trans (by simp [d])
  have hdet1 : (P0 * Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_diagonal, hd]
    exact mul_inv_cancel₀ hdet.ne_zero
  refine ⟨⟨P0 * Matrix.diagonal d, hdet1⟩, fun j => ?_⟩
  have : (fun a => (P0 * Matrix.diagonal d) a j) = d j • b j := by
    ext a
    simp [P0, Matrix.mul_diagonal, mul_comm]
  change (fun a => (P0 * Matrix.diagonal d) a j) ∈ E (ε j)
  rw [this]
  exact Submodule.smul_mem _ _ (hb j)

theorem exists_sl_frame (h2 : (2 : K) ≠ 0) (hn : 0 < n) {i₁ i₂ : Matrix (Fin n) (Fin n) K}
    (h₁ : i₁ * i₁ = 1) (h₂' : i₂ * i₂ = 1) (hc : i₁ * i₂ = i₂ * i₁) (ε : Fin n → Bool × Bool)
    (hε : ∀ s, Nat.card {j // ε j = s} = finrank K (jointEig i₁ i₂ s)) :
    ∃ P : SL(n, K),
      i₁ * (P : Matrix (Fin n) (Fin n) K) =
        (P : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun j => signOf K (ε j).1) ∧
      i₂ * (P : Matrix (Fin n) (Fin n) K) =
        (P : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun j => signOf K (ε j).2) := by
  have hint := isInternal_jointEigenspace h2 (toLin'_mul_self h₁) (toLin'_mul_self h₂')
    (toLin'_mul_comm hc)
  obtain ⟨P, hP⟩ := exists_sl_adapted hn (jointEig i₁ i₂) hint ε hε
  refine ⟨P, ?_, ?_⟩
  · ext a j
    rw [Matrix.mul_diagonal]
    have := congr_fun (mem_jointEig.mp (hP j)).1 a
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  · ext a j
    rw [Matrix.mul_diagonal]
    have := congr_fun (mem_jointEig.mp (hP j)).2 a
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this

end Matrices

end CFSG.ClassicalInvolution.Models
