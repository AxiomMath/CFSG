module

public import CFSG.RankThree.PartOne.S11d.OrthLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2

theorem exists_supportedFixedDerived_conj {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0)
    {m : V ≃ₗ[K] V} (hm : m ∈ isometryCentralizer Q x) {k : ℕ} (hk : Odd k) (hmk : m ^ k = 1) :
    ∃ f ∈ supportedFixedDerived Q x, ∀ g ∈ supportedFixedDerived Q x,
      m * g * m⁻¹ = f * g * f⁻¹ := by
  obtain ⟨f, hf⟩ := restrictFixed_surjective hx (isometryRestrictFixed Q x ⟨m, hm⟩)
    (isometryRestrictFixed_mem_orthogonalGroup _)
  have hfk : f ^ k = 1 := by
    apply restrictFixed_injective hx
    have h1 : (⟨m, hm⟩ : ↥(isometryCentralizer Q x)) ^ k = 1 := Subtype.ext hmk
    rw [map_pow, hf, ← map_pow, h1, map_one, map_one]
  have hfD : (f : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x :=
    hx.mem_supportedFixedDerived_of_odd_pow hT f.2 hk (congrArg Subtype.val hfk)
  refine ⟨f, hfD, fun g hg => ?_⟩
  have hgB := supportedFixedDerived_le_supportedBlock hg
  have hgC : g ∈ isometryCentralizer Q x := supportedBlock_le_isometryCentralizer _ hgB
  have h1 : m * g * m⁻¹ ∈ supportedBlock Q x (X - 1) := conj_mem_supportedBlock hm hgB
  have h2 : (f : V ≃ₗ[K] V) * g * (f : V ≃ₗ[K] V)⁻¹ ∈ supportedBlock Q x (X - 1) :=
    mul_mem (mul_mem f.2 hgB) (inv_mem f.2)
  have e1 : restrictFixed Q x ⟨_, h1⟩ =
      isometryRestrictFixed Q x (⟨m, hm⟩ * ⟨g, hgC⟩ * ⟨m, hm⟩⁻¹) := rfl
  have e2 : restrictFixed Q x ⟨_, h2⟩ = restrictFixed Q x (f * ⟨g, hgB⟩ * f⁻¹) := rfl
  have e3 : isometryRestrictFixed Q x ⟨g, hgC⟩ = restrictFixed Q x ⟨g, hgB⟩ := rfl
  have key : restrictFixed Q x ⟨_, h1⟩ = restrictFixed Q x ⟨_, h2⟩ := by
    rw [e1, e2, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hf, e3]
  exact congrArg Subtype.val (restrictFixed_injective hx key)

theorem exists_fixedComponentImage_conj {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {x y : orthDerived Q} (hx3 : orderOf x = 3)
    (hT : ∃ U : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) u = 0)
    (hxy : Commute x y) (hy3 : y ^ 3 = 1) :
    ∃ j ∈ fixedComponentImage Q (x : V ≃ₗ[K] V), ∀ z ∈ fixedComponentImage Q (x : V ≃ₗ[K] V),
      piOrth Q y * z * (piOrth Q y)⁻¹ = j * z * j⁻¹ := by
  have hpl : (3 : ℕ) ≠ ringChar K := by
    rw [ringChar.eq K 2]
    norm_num
  have hx := oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3
  have hm : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) :=
    Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup y.2,
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hxy.eq.symm)⟩
  obtain ⟨f, hf, hconj⟩ := exists_supportedFixedDerived_conj hx hT hm (by decide)
    (congrArg Subtype.val hy3)
  have hfΩ : f ∈ orthDerived Q := hx.supportedFixedDerived_le_orthDerived hf
  refine ⟨piOrth Q ⟨f, hfΩ⟩, ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  have hgy : y * g * y⁻¹ = ⟨f, hfΩ⟩ * g * ⟨f, hfΩ⟩⁻¹ :=
    Subtype.ext (hconj _ (Subgroup.mem_subgroupOf.mp hg))
  rw [← map_inv, ← map_mul, ← map_mul, hgy, map_mul, map_mul, map_inv]

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
