module

public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.GroupTheory

open Subgroup

variable {H : Type*} [Group H] [Finite H]

private noncomputable def normalizerToQuotient (N S : Subgroup H) [N.Normal] :
    Subgroup.normalizer (S : Set H) →*
      Subgroup.normalizer ((S.map (QuotientGroup.mk' N)) : Set (H ⧸ N)) where
  toFun x := ⟨(QuotientGroup.mk' N) (x : H),
    Subgroup.le_normalizer_map (QuotientGroup.mk' N) ⟨x, x.2, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; rfl

private noncomputable def normalizerQuotientMap (N S : Subgroup H) [N.Normal] :
    Subgroup.normalizer (S : Set H) →*
      TauCeti.Subgroup.normalizerQuotient (S.map (QuotientGroup.mk' N)) :=
  (TauCeti.Subgroup.normalizerQuotientMk (S.map (QuotientGroup.mk' N))).comp
    (normalizerToQuotient N S)

private theorem normalizerQuotientMap_ker (N S : Subgroup H) [N.Normal] (hNS : N ≤ S) :
    (normalizerQuotientMap N S).ker = S.subgroupOf (Subgroup.normalizer (S : Set H)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hx' : (QuotientGroup.mk' N) (x : H) ∈ S.map (QuotientGroup.mk' N) := by
      change (TauCeti.Subgroup.normalizerQuotientMk (S.map (QuotientGroup.mk' N)))
        ((normalizerToQuotient N S) x) = 1 at hx
      rw [TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff] at hx
      simpa only [normalizerToQuotient, MonoidHom.coe_mk, OneHom.coe_mk,
        Subgroup.coe_subtype, QuotientGroup.mk'_apply] using hx
    obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.mp hx'
    have hsm' : (QuotientGroup.mk' N) s = (QuotientGroup.mk' N) (x : H) := by
      simpa using hsm
    have hmem : (x : H) / s ∈ N := by
      have h1 : (QuotientGroup.mk' N) ((x : H) / s) = (1 : H ⧸ N) := by
        rw [map_div]
        change (QuotientGroup.mk' N) (x : H) / (QuotientGroup.mk' N) s = 1
        rw [← hsm']
        simp
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hxs : (x : H) = ((x : H) / s) * s := by simp [div_eq_mul_inv, mul_assoc]
    rw [hxs]
    exact S.mul_mem (hNS hmem) hs
  · intro hx
    have hxS : (x : H) ∈ S := hx
    change (TauCeti.Subgroup.normalizerQuotientMk (S.map (QuotientGroup.mk' N)))
      ((normalizerToQuotient N S) x) = 1
    rw [TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff]
    exact Subgroup.mem_map_of_mem _ hxS

private theorem normalizerToQuotient_surjective (N S : Subgroup H) [N.Normal] (hNS : N ≤ S) :
    Function.Surjective (normalizerToQuotient N S) := by
  rintro ⟨y, hy⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hy' : QuotientGroup.mk g ∈
      Subgroup.normalizer ((S.map (QuotientGroup.mk' N)) : Set (H ⧸ N)) := hy
  have hle : S.map (MulAut.conj g).toMonoidHom ≤ S := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    change g * x * g⁻¹ ∈ S
    have hx' : (QuotientGroup.mk' N) (g * x * g⁻¹) ∈ S.map (QuotientGroup.mk' N) := by
      have hmem := ((Subgroup.mem_normalizer_iff.mp hy' (QuotientGroup.mk x)).mp
        (Subgroup.mem_map_of_mem _ hx))
      simpa using hmem
    obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.mp hx'
    have hsm' : (QuotientGroup.mk' N) s = (QuotientGroup.mk' N) (g * x * g⁻¹) := by
      simpa using hsm
    have hmem : (g * x * g⁻¹) / s ∈ N := by
      have h1 : (QuotientGroup.mk' N) ((g * x * g⁻¹) / s) = (1 : H ⧸ N) := by
        rw [map_div]
        change (QuotientGroup.mk' N) (g * x * g⁻¹) / (QuotientGroup.mk' N) s = 1
        rw [hsm']
        simp
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hxs : g * x * g⁻¹ = ((g * x * g⁻¹) / s) * s := by
      simp [div_eq_mul_inv, mul_assoc]
    rw [hxs]
    exact S.mul_mem (hNS hmem) hs
  have heq : S.map (MulAut.conj g).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact ⟨⟨g, Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq⟩, Subtype.ext rfl⟩

noncomputable def normalizerQuotient_quotientEquiv (N S : Subgroup H) [N.Normal] (hNS : N ≤ S) :
    TauCeti.Subgroup.normalizerQuotient S ≃*
      TauCeti.Subgroup.normalizerQuotient (S.map (QuotientGroup.mk' N)) :=
  (QuotientGroup.quotientMulEquivOfEq (normalizerQuotientMap_ker N S hNS).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (normalizerQuotientMap N S)
      ((TauCeti.Subgroup.normalizerQuotientMk_surjective _).comp
        (normalizerToQuotient_surjective N S hNS)))

end CFSG.GroupTheory

