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
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrth

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]

@[expose] noncomputable def rk1 (M : Matrix ι ι F) : ℕ := (M - 1).rank

theorem rank_mul_right_of_isUnit' (A : Matrix ι ι F) {U : Matrix ι ι F} (hU : IsUnit U) :
    (A * U).rank = A.rank :=
  Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)

theorem rank_mul_left_of_isUnit' (A : Matrix ι ι F) {U : Matrix ι ι F} (hU : IsUnit U) :
    (U * A).rank = A.rank :=
  Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)

theorem rk1_conj (g : (Matrix ι ι F)ˣ) (M : Matrix ι ι F) :
    rk1 ((g : Matrix ι ι F) * M * ((g⁻¹ : (Matrix ι ι F)ˣ) : Matrix ι ι F)) = rk1 M := by
  unfold rk1
  have : (g : Matrix ι ι F) * M * ((g⁻¹ : (Matrix ι ι F)ˣ) : Matrix ι ι F) - 1 =
      (g : Matrix ι ι F) * (M - 1) * ((g⁻¹ : (Matrix ι ι F)ˣ) : Matrix ι ι F) := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [this, rank_mul_right_of_isUnit' _ g⁻¹.isUnit, rank_mul_left_of_isUnit' _ g.isUnit]

theorem rk1_pow_nat_le (M : Matrix ι ι F) (m : ℕ) : rk1 (M ^ m) ≤ rk1 M := by
  unfold rk1
  have : M ^ m - 1 = (M - 1) * ∑ t ∈ Finset.range m, M ^ t := (mul_geom_sum M m).symm
  rw [this]
  exact Matrix.rank_mul_le_left _ _

theorem rk1_inv (u : (Matrix ι ι F)ˣ) :
    rk1 ((u⁻¹ : (Matrix ι ι F)ˣ) : Matrix ι ι F) = rk1 (u : Matrix ι ι F) := by
  unfold rk1
  have : ((u⁻¹ : (Matrix ι ι F)ˣ) : Matrix ι ι F) - 1 =
      (-((u⁻¹ : (Matrix ι ι F)ˣ) : Matrix ι ι F)) * ((u : Matrix ι ι F) - 1) := by
    rw [neg_mul, mul_sub, Units.inv_mul, mul_one]; abel
  rw [this, rank_mul_left_of_isUnit' _ u⁻¹.isUnit.neg]

theorem rk1_zpow_le (u : (Matrix ι ι F)ˣ) (ε : ℤ) :
    rk1 ((u ^ ε : (Matrix ι ι F)ˣ) : Matrix ι ι F) ≤ rk1 (u : Matrix ι ι F) := by
  rcases Int.eq_nat_or_neg ε with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, Units.val_pow_eq_pow_val]
    exact rk1_pow_nat_le _ _
  · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    refine (rk1_pow_nat_le _ _).trans ?_
    rw [rk1_inv]

theorem rank_le_card_of_rowSupport (N : Matrix ι ι F) (S : Finset ι)
    (h : ∀ a ∉ S, ∀ b, N a b = 0) : N.rank ≤ S.card := by
  classical
  have hle : LinearMap.range N.mulVecLin ≤
      Submodule.span F (Set.range fun a : S => (Pi.single (a : ι) (1 : F) : ι → F)) := by
    rintro _ ⟨v, rfl⟩
    simp only [Matrix.mulVecLin_apply]
    have : N.mulVec v = ∑ a ∈ S, N.mulVec v a • (Pi.single a (1 : F) : ι → F) := by
      ext c
      by_cases hc : c ∈ S
      · simp [Finset.sum_apply, Pi.single_apply, hc]
      · simp [Finset.sum_apply, Pi.single_apply, hc, Matrix.mulVec, dotProduct, h c hc]
    rw [this]
    exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩)
  calc N.rank = Module.finrank F (LinearMap.range N.mulVecLin) := rfl
    _ ≤ Module.finrank F (Submodule.span F (Set.range fun a : S =>
          (Pi.single (a : ι) (1 : F) : ι → F))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card S := finrank_range_le_card _
    _ = S.card := Fintype.card_coe S

theorem card_le_rank (N : Matrix ι ι F) (S : Finset ι)
    (hinj : ∀ v : ι → F, (∀ a ∉ S, v a = 0) → (∀ a ∈ S, N.mulVec v a = 0) → ∀ a, v a = 0) :
    S.card ≤ N.rank := by
  classical
  set K : Matrix S S F := N.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι) with hK
  have hKinj : Function.Injective K.mulVec := by
    have hlin : Function.Injective K.mulVecLin := by
      rw [injective_iff_map_eq_zero]
      intro w hw
      simp only [Matrix.mulVecLin_apply] at hw
      let v : ι → F := fun a => if h : a ∈ S then w ⟨a, h⟩ else 0
      have hvS : ∀ a ∉ S, v a = 0 := fun a ha => by simp [v, ha]
      have hvw : ∀ a : S, v a = w a := fun a => by simp [v, a.2]
      have hN : ∀ a ∈ S, N.mulVec v a = 0 := by
        intro a ha
        have h1 : K.mulVec w ⟨a, ha⟩ = 0 := congrFun hw ⟨a, ha⟩
        simp only [Matrix.mulVec, dotProduct, hK, Matrix.submatrix_apply] at h1 ⊢
        calc ∑ x, N a x * v x = ∑ x ∈ S, N a x * v x :=
              (Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => by
                simp [hvS b hb])).symm
          _ = ∑ x : S, N a x * v x := (Finset.sum_coe_sort S (fun b => N a b * v b)).symm
          _ = ∑ x : S, N a x * w x := by simp [hvw]
          _ = 0 := h1
      funext a
      have := hinj v hvS hN a
      simpa [hvw] using this
    exact hlin
  have hu : IsUnit K := Matrix.mulVec_injective_iff_isUnit.1 hKinj
  have h1 : K.rank = Fintype.card S := Matrix.rank_of_isUnit K hu
  have h2 : K.rank ≤ N.rank := Matrix.rank_submatrix_le N _ _
  rw [Fintype.card_coe] at h1
  omega

theorem card_add_le_rank_add (Ni Nj : Matrix ι ι F) (Si Sj : Finset ι) (hd : Disjoint Si Sj)
    (hi : ∀ a b, Ni a b ≠ 0 → a ∈ Si ∧ b ∈ Si) (hj : ∀ a b, Nj a b ≠ 0 → a ∈ Sj ∧ b ∈ Sj)
    (hinji : ∀ v : ι → F, (∀ a ∉ Si, v a = 0) → (∀ a ∈ Si, Ni.mulVec v a = 0) → ∀ a, v a = 0)
    (hinjj : ∀ v : ι → F, (∀ a ∉ Sj, v a = 0) → (∀ a ∈ Sj, Nj.mulVec v a = 0) → ∀ a, v a = 0) :
    Si.card + Sj.card ≤ (Ni + Nj).rank := by
  classical
  rw [← Finset.card_union_of_disjoint hd]
  refine card_le_rank _ _ fun v hvS hv => ?_
  have key : ∀ (Nx Ny : Matrix ι ι F) (Sx Sy : Finset ι), Disjoint Sx Sy →
      (∀ a b, Nx a b ≠ 0 → a ∈ Sx ∧ b ∈ Sx) → (∀ a b, Ny a b ≠ 0 → a ∈ Sy ∧ b ∈ Sy) →
      (∀ w : ι → F, (∀ a ∉ Sx, w a = 0) → (∀ a ∈ Sx, Nx.mulVec w a = 0) → ∀ a, w a = 0) →
      (∀ a ∈ Sx ∪ Sy, (Nx + Ny).mulVec v a = 0) → ∀ a ∈ Sx, v a = 0 := by
    intro Nx Ny Sx Sy hxy hx hy hinj hv' a haS
    let w : ι → F := fun b => if b ∈ Sx then v b else 0
    have hwS : ∀ b ∉ Sx, w b = 0 := fun b hb => by simp [w, hb]
    have hN : ∀ c ∈ Sx, Nx.mulVec w c = 0 := by
      intro c hc
      have h0 := hv' c (Finset.mem_union_left _ hc)
      simp only [Matrix.add_mulVec, Pi.add_apply] at h0
      have h1 : Ny.mulVec v c = 0 := by
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_eq_zero fun b _ => ?_
        by_cases hne : Ny c b = 0
        · simp [hne]
        · exact absurd (hy c b hne).1 (Finset.disjoint_left.1 hxy hc)
      have h2 : Nx.mulVec w c = Nx.mulVec v c := by
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hne : Nx c b = 0
        · simp [hne]
        · simp [w, (hx c b hne).2]
      rw [h2, ← h0, h1, add_zero]
    have := hinj w hwS hN a
    simpa [w, haS] using this
  intro a
  by_cases ha : a ∈ Si ∪ Sj
  · rcases Finset.mem_union.1 ha with h | h
    · exact key Ni Nj Si Sj hd hi hj hinji hv a h
    · refine key Nj Ni Sj Si hd.symm hj hi hinjj ?_ a h
      intro c hc
      rw [add_comm]
      exact hv c (by rwa [Finset.union_comm])
  · exact hvS a ha

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrth
