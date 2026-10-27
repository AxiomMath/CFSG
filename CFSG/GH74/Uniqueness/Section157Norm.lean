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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Sec157

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem comm_mem_of_sq_mem {P N : Subgroup X} (hPN : ∀ g ∈ P, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (hsq : ∀ x ∈ P, x * x ∈ N) : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ N := by
  intro a ha b hb
  have h1 : a * b * (a * b) ∈ N := hsq _ (P.mul_mem ha hb)
  have h2 : a⁻¹ * a⁻¹ ∈ N := by
    have := N.inv_mem (hsq a ha)
    rwa [mul_inv_rev] at this
  have h3 : b⁻¹ * b⁻¹ ∈ N := by
    have := N.inv_mem (hsq b hb)
    rwa [mul_inv_rev] at this
  have h4 : b⁻¹ * (a⁻¹ * a⁻¹) * b⁻¹⁻¹ ∈ N := hPN b⁻¹ (P.inv_mem hb) _ h2
  have e : a * b * a⁻¹ * b⁻¹ =
      (a * b * (a * b)) * (b⁻¹ * (a⁻¹ * a⁻¹) * b⁻¹⁻¹) * (b⁻¹ * b⁻¹) := by group
  rw [e]
  exact N.mul_mem (N.mul_mem h1 h4) h3

theorem exists_invariant_index_two {M N P A : Subgroup X} {u : X}
    (hNM : ∀ g ∈ M, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (hPM : ∀ g ∈ M, ∀ x ∈ P, g * x * g⁻¹ ∈ P)
    (hNP : N ≤ P) (hPM' : P ≤ M) (hAM : A ≤ M) (hodd : Odd (Nat.card A))
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ N) (huP : u ∈ P) (huN : u ∉ N)
    (hu2 : u * u ∈ N) (huA : ∀ a ∈ A, a * u * a⁻¹ = u)
    (hfix : ∀ x ∈ P, (∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ N) → x ∈ N ∨ u * x ∈ N) :
    ∃ P₀ : Subgroup X, N ≤ P₀ ∧ P₀ ≤ P ∧ u ∉ P₀ ∧ (∀ x ∈ P, x ∈ P₀ ∨ u * x ∈ P₀) ∧
      Nat.card P = 2 * Nat.card P₀ ∧
      ∀ g ∈ M, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → ∀ x ∈ P₀, g * x * g⁻¹ ∈ P₀ := by
  classical
  have hNM' : N ≤ M := hNP.trans hPM'
  have hNn : (N.subgroupOf M).Normal :=
    (normal_subgroupOf_iff hNM').mpr fun h k hh hk => hNM k hk h hh
  have hPn : (P.subgroupOf M).Normal :=
    (normal_subgroupOf_iff hPM').mpr fun h k hh hk => hPM k hk h hh
  let mk : ↥M →* ↥M ⧸ N.subgroupOf M := QuotientGroup.mk' _
  have hmk : ∀ a b : ↥M, mk a = mk b ↔ (a : X)⁻¹ * (b : X) ∈ N := by
    intro a b
    refine (QuotientGroup.eq (s := N.subgroupOf M)).trans ?_
    rw [mem_subgroupOf]
    rfl
  let Pb : Subgroup (↥M ⧸ N.subgroupOf M) := (P.subgroupOf M).map mk
  have hPb : Pb.Normal := Normal.map hPn mk (QuotientGroup.mk'_surjective _)
  have hcommPb : ∀ a b : ↥Pb, a * b = b * a := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show mk a * mk b = mk b * mk a
    rw [← map_mul, ← map_mul, hmk]
    have ha' : (a : X) ∈ P := mem_subgroupOf.mp ha
    have hb' : (b : X) ∈ P := mem_subgroupOf.mp hb
    have := hcomm _ (P.inv_mem hb') _ (P.inv_mem ha')
    simpa [mul_assoc] using this
  let _ : CommGroup ↥Pb := { (inferInstance : Group ↥Pb) with mul_comm := hcommPb }
  let ρ : ↥M →* MulAut ↥Pb := (MulAut.conjNormal (H := Pb)).comp mk
  have hρ : ∀ (g : ↥M) (y : ↥Pb), ((ρ g y : ↥Pb) : ↥M ⧸ N.subgroupOf M) =
      mk g * (y : ↥M ⧸ N.subgroupOf M) * (mk g)⁻¹ := fun g y => MulAut.conjNormal_apply _ _
  let _ : Fintype ↥A := Fintype.ofFinite _
  let π : ↥Pb →* ↥Pb :=
    { toFun := fun y => ∏ a : ↥A, ρ ⟨(a : X), hAM a.2⟩ y
      map_one' := by simp
      map_mul' := by intro y z; simp [Finset.prod_mul_distrib] }
  have hπ : ∀ y, π y = ∏ a : ↥A, ρ ⟨(a : X), hAM a.2⟩ y := fun y => rfl
  have hπright : ∀ (b : X) (hb : b ∈ A) (y : ↥Pb), π (ρ ⟨b, hAM hb⟩ y) = π y := by
    intro b hb y
    rw [hπ, hπ]
    refine Fintype.prod_equiv (Equiv.mulRight (⟨b, hb⟩ : ↥A)) _ _ (fun a => ?_)
    show ρ ⟨(a : X), hAM a.2⟩ (ρ ⟨b, hAM hb⟩ y) =
      ρ (⟨(a : X), hAM a.2⟩ * ⟨b, hAM hb⟩) y
    rw [map_mul]
    rfl
  have hπconj : ∀ (g : X) (hg : g ∈ M), (∀ a ∈ A, g * a * g⁻¹ ∈ A) → ∀ y : ↥Pb,
      π (ρ ⟨g, hg⟩ y) = ρ ⟨g, hg⟩ (π y) := by
    intro g hg hgA y
    let e : ↥A → ↥A := fun a => ⟨g * (a : X) * g⁻¹, hgA a a.2⟩
    have he : Function.Injective e := by
      intro a b hab
      have h2 : g * (a : X) * g⁻¹ = g * (b : X) * g⁻¹ := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
    rw [hπ, hπ, map_prod]
    refine (Fintype.prod_bijective e (Finite.injective_iff_bijective.mp he) _ _ (fun a => ?_)).symm
    have h1 : (⟨g, hg⟩ : ↥M) * ⟨(a : X), hAM a.2⟩ =
        ⟨(e a : X), hAM (e a).2⟩ * ⟨g, hg⟩ := by
      apply Subtype.ext
      show g * (a : X) = (g * (a : X) * g⁻¹) * g
      group
    calc ρ ⟨g, hg⟩ (ρ ⟨(a : X), hAM a.2⟩ y) = ρ (⟨g, hg⟩ * ⟨(a : X), hAM a.2⟩) y := by
          rw [map_mul]; rfl
      _ = ρ (⟨(e a : X), hAM (e a).2⟩ * ⟨g, hg⟩) y := by rw [h1]
      _ = ρ ⟨(e a : X), hAM (e a).2⟩ (ρ ⟨g, hg⟩ y) := by rw [map_mul]; rfl
  have hπfix : ∀ (a : X) (ha : a ∈ A) (y : ↥Pb), ρ ⟨a, hAM ha⟩ (π y) = π y := by
    intro a ha y
    have h1 := hπconj a (hAM ha) (fun b hb => A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) y
    rw [← h1, hπright a ha y]
  let incl : ↥P →* ↥M := Subgroup.inclusion hPM'
  have hιmem : ∀ x : ↥P, (mk.comp incl) x ∈ Pb := fun x => ⟨incl x, mem_subgroupOf.mpr x.2, rfl⟩
  let ι : ↥P →* ↥Pb := (mk.comp incl).codRestrict Pb hιmem
  have hιsurj : ∀ w : ↥Pb, ∃ z : ↥P, ι z = w := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨(a : X), mem_subgroupOf.mp ha⟩, rfl⟩
  have hιconj : ∀ (g : X) (hg : g ∈ M) (x : ↥P),
      ι ⟨g * (x : X) * g⁻¹, hPM g hg x x.2⟩ = ρ ⟨g, hg⟩ (ι x) := by
    intro g hg x
    apply Subtype.ext
    rw [hρ]
    show mk (incl _) = mk ⟨g, hg⟩ * mk (incl x) * (mk ⟨g, hg⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hι_one : ∀ x : ↥P, ι x = 1 ↔ (x : X) ∈ N := by
    intro x
    constructor
    · intro h
      have h1 : mk (incl x) = 1 := congrArg Subtype.val h
      exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := N.subgroupOf M) (incl x)).mp h1)
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := N.subgroupOf M) (incl x)).mpr (mem_subgroupOf.mpr h)
  have hu_fix : ∀ (a : X) (ha : a ∈ A), ρ ⟨a, hAM ha⟩ (ι ⟨u, huP⟩) = ι ⟨u, huP⟩ := by
    intro a ha
    rw [← hιconj a (hAM ha) ⟨u, huP⟩]
    congr 1
    exact Subtype.ext (huA a ha)
  have hιu2 : ι ⟨u, huP⟩ * ι ⟨u, huP⟩ = 1 := by
    rw [← map_mul]
    exact (hι_one _).mpr hu2
  have hιu1 : ι ⟨u, huP⟩ ≠ 1 := fun h => huN ((hι_one _).mp h)
  have hπu : π (ι ⟨u, huP⟩) = ι ⟨u, huP⟩ := by
    rw [hπ]
    have hfixu : ∀ a : ↥A, ρ ⟨(a : X), hAM a.2⟩ (ι ⟨u, huP⟩) = ι ⟨u, huP⟩ :=
      fun a => hu_fix a a.2
    rw [Finset.prod_congr rfl (fun a _ => hfixu a), Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    obtain ⟨m, hm⟩ := hodd
    have hsq : ι ⟨u, huP⟩ ^ 2 = 1 := by rw [pow_two]; exact hιu2
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have hval : ∀ x : ↥P, π (ι x) = 1 ∨ π (ι x) = ι ⟨u, huP⟩ := by
    intro x
    obtain ⟨z, hz⟩ := hιsurj (π (ι x))
    have hzfix : ∀ a ∈ A, (z : X)⁻¹ * (a * (z : X) * a⁻¹) ∈ N := by
      intro a ha
      have h1 := hπfix a ha (ι x)
      rw [← hz, ← hιconj a (hAM ha) z] at h1
      have h2 : mk (incl z) = mk (incl ⟨a * (z : X) * a⁻¹, hPM a (hAM ha) z z.2⟩) :=
        (congrArg Subtype.val h1).symm
      exact (hmk _ _).mp h2
    rcases hfix z z.2 hzfix with h | h
    · left
      rw [← hz]
      exact (hι_one z).mpr h
    · right
      rw [← hz]
      have h1 : ι ⟨u, huP⟩ * ι z = 1 := by
        rw [← map_mul]
        exact (hι_one _).mpr h
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_eq_of_mul_eq_one_right hιu2
  refine ⟨(π.comp ι).ker.map P.subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨⟨x, hNP hx⟩, ?_, rfl⟩
    show π (ι ⟨x, hNP hx⟩) = 1
    rw [(hι_one _).mpr hx, map_one]
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · rintro ⟨y, hy, hyu⟩
    have hy' : y = ⟨u, huP⟩ := Subtype.ext hyu
    subst hy'
    have h1 : π (ι ⟨u, huP⟩) = 1 := hy
    rw [hπu] at h1
    exact hιu1 h1
  · intro x hx
    rcases hval ⟨x, hx⟩ with h | h
    · exact Or.inl ⟨⟨x, hx⟩, h, rfl⟩
    · refine Or.inr ⟨⟨u * x, P.mul_mem huP hx⟩, ?_, rfl⟩
      show π (ι ⟨u * x, P.mul_mem huP hx⟩) = 1
      have e : (⟨u * x, P.mul_mem huP hx⟩ : ↥P) = ⟨u, huP⟩ * ⟨x, hx⟩ := rfl
      rw [e, map_mul, map_mul, h, hπu]
      exact hιu2
  · have hidx : (π.comp ι).ker.index = 2 := by
      rw [index_eq_two_iff]
      refine ⟨⟨u, huP⟩, fun b => ?_⟩
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, hπu]
      rcases hval b with h | h
      · rw [h]
        simp [hιu1]
      · rw [h, hιu2]
        simp [hιu1]
    have h1 := Subgroup.card_mul_index (π.comp ι).ker
    rw [hidx] at h1
    rw [card_map_of_injective P.subtype_injective, ← h1]
    ring
  · intro g hg hgA x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨g * (y : X) * g⁻¹, hPM g hg y y.2⟩, ?_, rfl⟩
    show π (ι ⟨g * (y : X) * g⁻¹, hPM g hg y y.2⟩) = 1
    have h1 : π (ι y) = 1 := hy
    rw [hιconj g hg y, hπconj g hg hgA, h1, map_one]

end Sec157

end CFSG.GH74.Uniqueness
