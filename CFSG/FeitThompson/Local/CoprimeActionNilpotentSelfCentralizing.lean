module

public import CFSG.FeitThompson.Foundations.NilpotentNormalizerCondition
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Local.PointwiseStabilizerSelfCentralizingPGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup MulAction

variable {N : Type*} [Group N]

theorem normalizer_le_fixedPoints_subgroup_of_coprime [Finite N] (B : Subgroup (MulAut N)) {n : ℕ}
    (hcop : n.Coprime (Nat.card N)) (hBn : ∀ b ∈ B, b ^ n = 1)
    (hself : centralizer (FixedPoints.subgroup B N : Set N) ≤ FixedPoints.subgroup B N) :
    normalizer (FixedPoints.subgroup B N : Set N) ≤ FixedPoints.subgroup B N := by
  set F := FixedPoints.subgroup B N with hF
  intro x hx
  rw [hF, mem_fixedPoints_subgroup_mulAut_iff]
  intro b hb
  have he : ∀ f ∈ F, (b : MulAut N) f = f := fun f hf =>
    mem_fixedPoints_subgroup_mulAut_iff.mp hf b hb
  have hyF : x⁻¹ * (b : MulAut N) x ∈ F := by
    refine hself ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hxf : x * f * x⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hx f).mp hf
    have h1 : (b : MulAut N) (x * f * x⁻¹) = x * f * x⁻¹ := he _ hxf
    rw [map_mul, map_mul, map_inv, he f hf] at h1
    have h2 : (x⁻¹ * (b : MulAut N) x) * f * (x⁻¹ * (b : MulAut N) x)⁻¹ = f := by
      calc (x⁻¹ * (b : MulAut N) x) * f * (x⁻¹ * (b : MulAut N) x)⁻¹
          = x⁻¹ * ((b : MulAut N) x * f * ((b : MulAut N) x)⁻¹) * x := by group
        _ = x⁻¹ * (x * f * x⁻¹) * x := by rw [h1]
        _ = f := by group
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hay : (b : MulAut N) (x⁻¹ * (b : MulAut N) x) = x⁻¹ * (b : MulAut N) x := he _ hyF
  have hpow := apply_pow_eq_mul_pow hay n
  rw [hBn b hb] at hpow
  have hxx : x = x * (x⁻¹ * (b : MulAut N) x) ^ n := by simpa using hpow
  have hyn : (x⁻¹ * (b : MulAut N) x) ^ n = 1 := left_eq_mul.mp hxx
  have hy1 : x⁻¹ * (b : MulAut N) x = 1 :=
    orderOf_eq_one_iff.mp
      ((Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hyn) hcop).eq_one_of_dvd
        (orderOf_dvd_natCard _))
  exact (inv_mul_eq_one.mp hy1).symm

theorem fixedPoints_subgroup_eq_top_of_isNilpotent_of_centralizer_le [Finite N]
    [Group.IsNilpotent N] (B : Subgroup (MulAut N)) {n : ℕ}
    (hcop : n.Coprime (Nat.card N)) (hBn : ∀ b ∈ B, b ^ n = 1)
    (hself : centralizer (FixedPoints.subgroup B N : Set N) ≤ FixedPoints.subgroup B N) :
    FixedPoints.subgroup B N = ⊤ := by
  by_contra hne
  have hlt := Group.normalizerCondition_of_isNilpotent (G := N) _ (lt_of_le_of_ne le_top hne)
  exact hlt.ne (le_antisymm le_normalizer
    (normalizer_le_fixedPoints_subgroup_of_coprime B hcop hBn hself))

theorem fixedPoints_range_eq_top_of_coprime_of_isNilpotent [Finite N] [Group.IsNilpotent N]
    {A : Type*} [Group A] [Finite A] (φ : A →* MulAut N)
    (hcop : (Nat.card A).Coprime (Nat.card N))
    (hself : centralizer (FixedPoints.subgroup φ.range N : Set N) ≤
      FixedPoints.subgroup φ.range N) :
    FixedPoints.subgroup φ.range N = ⊤ := by
  refine fixedPoints_subgroup_eq_top_of_isNilpotent_of_centralizer_le φ.range
    (n := Nat.card A) hcop ?_ hself
  rintro b ⟨a, rfl⟩
  rw [← map_pow, pow_card_eq_one', map_one]

theorem eq_one_of_coprime_of_isNilpotent_of_centralizer_le [Finite N] [Group.IsNilpotent N]
    {A : Type*} [Group A] [Finite A] (φ : A →* MulAut N)
    (hcop : (Nat.card A).Coprime (Nat.card N))
    (hself : centralizer (FixedPoints.subgroup φ.range N : Set N) ≤
      FixedPoints.subgroup φ.range N) (a : A) :
    φ a = 1 := by
  have htop := fixedPoints_range_eq_top_of_coprime_of_isNilpotent φ hcop hself
  ext x
  have hx : x ∈ FixedPoints.subgroup φ.range N := htop ▸ mem_top x
  simpa using mem_fixedPoints_subgroup_mulAut_iff.mp hx (φ a) ⟨a, rfl⟩

theorem IsCentralSeries.fixedPoints_range_eq_top_of_coprime [Finite N] {X : ℕ → Subgroup N}
    {r : ℕ} (hX : IsCentralSeries X r) {A : Type*} [Group A] [Finite A] (φ : A →* MulAut N)
    (hcop : (Nat.card A).Coprime (Nat.card N))
    (hself : centralizer (FixedPoints.subgroup φ.range N : Set N) ≤
      FixedPoints.subgroup φ.range N) :
    FixedPoints.subgroup φ.range N = ⊤ :=
  have : Group.IsNilpotent N := hX.isNilpotent
  _root_.CFSG.FeitThompson.fixedPoints_range_eq_top_of_coprime_of_isNilpotent
    φ hcop hself

theorem fixedPoints_subgroup_eq_top_of_coprime_of_isNilpotent [Finite N] [Group.IsNilpotent N]
    {A : Type*} [Group A] [Finite A] [MulDistribMulAction A N]
    (hcop : (Nat.card A).Coprime (Nat.card N))
    (hself : centralizer (FixedPoints.subgroup A N : Set N) ≤ FixedPoints.subgroup A N) :
    FixedPoints.subgroup A N = ⊤ := by
  rw [fixedPoints_subgroup_eq_toMulAut_range (A := A) (P := N)] at hself ⊢
  exact fixedPoints_range_eq_top_of_coprime_of_isNilpotent _ hcop hself

theorem smul_eq_self_of_coprime_of_isNilpotent [Finite N] [Group.IsNilpotent N]
    {A : Type*} [Group A] [Finite A] [MulDistribMulAction A N]
    (hcop : (Nat.card A).Coprime (Nat.card N))
    (hself : centralizer (FixedPoints.subgroup A N : Set N) ≤ FixedPoints.subgroup A N)
    (a : A) (x : N) :
    a • x = x := by
  have htop := fixedPoints_subgroup_eq_top_of_coprime_of_isNilpotent (A := A) (N := N) hcop hself
  have hx : x ∈ FixedPoints.subgroup A N := htop ▸ mem_top x
  exact (FixedPoints.mem_subgroup A N x).mp hx a

end

end CFSG.FeitThompson
