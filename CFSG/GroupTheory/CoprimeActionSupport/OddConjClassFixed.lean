module

public import CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints

open scoped Pointwise

private theorem conjClass_conj_mem_P {G : Type*} [Group G] {P : Subgroup G} {x p z : G}
    (hp : p ∈ P) (hz : ∃ q ∈ P, z = q * x * q⁻¹) :
    ∃ q ∈ P, p * z * p⁻¹ = q * x * q⁻¹ := by
  obtain ⟨q, hq, rfl⟩ := hz
  exact ⟨p * q, P.mul_mem hp hq, by group⟩

private theorem conjClass_conj_mem_R {G : Type*} [Group G] {P R : Subgroup G} {x r z : G}
    (hRP : R ≤ Subgroup.normalizer (P : Set G))
    (hx : ∀ r ∈ R, ∃ p ∈ P, r * x * r⁻¹ = p * x * p⁻¹) (hr : r ∈ R)
    (hz : ∃ q ∈ P, z = q * x * q⁻¹) :
    ∃ q ∈ P, r * z * r⁻¹ = q * x * q⁻¹ := by
  obtain ⟨q, hq, rfl⟩ := hz
  obtain ⟨q', hq', hq'x⟩ := hx r hr
  have hrq : r * q * r⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hRP hr) q).mp hq
  refine ⟨(r * q * r⁻¹) * q', P.mul_mem hrq hq', ?_⟩
  calc r * (q * x * q⁻¹) * r⁻¹
      = (r * q * r⁻¹) * (r * x * r⁻¹) * (r * q * r⁻¹)⁻¹ := by group
    _ = (r * q * r⁻¹) * (q' * x * q'⁻¹) * (r * q * r⁻¹)⁻¹ := by rw [hq'x]
    _ = ((r * q * r⁻¹) * q') * x * ((r * q * r⁻¹) * q')⁻¹ := by group

private theorem conjClass_conj_mem_sup {G : Type*} [Group G] {P R : Subgroup G} {x h z : G}
    (hRP : R ≤ Subgroup.normalizer (P : Set G))
    (hx : ∀ r ∈ R, ∃ p ∈ P, r * x * r⁻¹ = p * x * p⁻¹) (hh : h ∈ P ⊔ R)
    (hz : ∃ q ∈ P, z = q * x * q⁻¹) :
    ∃ q ∈ P, h * z * h⁻¹ = q * x * q⁻¹ := by
  have hPR : (P : Set G) * (R : Set G) = ((P ⊔ R : Subgroup G) : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left P R hRP).symm
  have hh' : h ∈ ((P ⊔ R : Subgroup G) : Set G) := hh
  obtain ⟨p, hp, r, hr, hpr⟩ := hPR ▸ hh'
  obtain ⟨q, hq, hqz⟩ := conjClass_conj_mem_P hp (conjClass_conj_mem_R hRP hx hr hz)
  refine ⟨q, hq, ?_⟩
  rw [← hpr]
  calc (p * r) * z * (p * r)⁻¹ = p * (r * z * r⁻¹) * p⁻¹ := by group
    _ = q * x * q⁻¹ := hqz

theorem exists_conj_fixed {G : Type*} [Group G] [Finite G] {P R : Subgroup G}
    (hP : IsPGroup 2 P) (hR : Odd (Nat.card R)) (hRP : R ≤ Subgroup.normalizer (P : Set G))
    {x : G} (hx : ∀ r ∈ R, ∃ p ∈ P, r * x * r⁻¹ = p * x * p⁻¹) :
    ∃ p ∈ P, ∀ r ∈ R, r * (p * x * p⁻¹) * r⁻¹ = p * x * p⁻¹ := by
  classical
  set X : Set G := {z | ∃ p ∈ P, z = p * x * p⁻¹} with hX
  have hxX : x ∈ X := ⟨1, P.one_mem, by simp⟩
  let H : Subgroup G := P ⊔ R
  haveI : Finite X := Finite.of_injective (Subtype.val : X → G) Subtype.val_injective
  haveI : Nonempty X := ⟨⟨x, hxX⟩⟩
  letI : MulAction H X :=
    { smul := fun h z =>
        ⟨(h : G) * z.1 * (h : G)⁻¹, conjClass_conj_mem_sup hRP hx h.2 z.2⟩
      one_smul := fun z => Subtype.ext (by
        change (1 : G) * z.1 * (1 : G)⁻¹ = z.1
        group)
      mul_smul := fun a b z => Subtype.ext (by
        change ((a : G) * (b : G)) * z.1 * ((a : G) * (b : G))⁻¹ =
          (a : G) * ((b : G) * z.1 * (b : G)⁻¹) * (a : G)⁻¹
        group) }
  have htrans : ∀ z w : X, ∃ s : P.subgroupOf H, s.val • z = w := by
    intro z w
    obtain ⟨p, hp, hzp⟩ := z.2
    obtain ⟨q, hq, hzw⟩ := w.2
    have hmem : q * p⁻¹ ∈ P := P.mul_mem hq (P.inv_mem hp)
    refine ⟨⟨⟨q * p⁻¹, Subgroup.mem_sup_left hmem⟩, Subgroup.mem_subgroupOf.mpr hmem⟩, ?_⟩
    apply Subtype.ext
    change (q * p⁻¹) * z.1 * (q * p⁻¹)⁻¹ = w.1
    rw [hzp, hzw]
    group
  have hS : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  have hB : Odd (Nat.card (R.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact hR
  haveI : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le (Subgroup.le_normalizer) hRP)
  have hSB : P.subgroupOf H ⊔ R.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  obtain ⟨z, hz⟩ := exists_fixed (S := P.subgroupOf H) (B := R.subgroupOf H)
    hS hB hSB (↥X) htrans
  obtain ⟨p, hp, hzp⟩ := z.2
  refine ⟨p, hp, fun r hr => ?_⟩
  have hmem : (⟨r, Subgroup.mem_sup_right hr⟩ : H) ∈ R.subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr hr
  have h : r * z.1 * r⁻¹ = z.1 := by
    have h' := congrArg Subtype.val (hz ⟨⟨r, Subgroup.mem_sup_right hr⟩, hmem⟩)
    change r * z.1 * r⁻¹ = z.1 at h'
    exact h'
  rw [← hzp]
  exact h

end CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints
