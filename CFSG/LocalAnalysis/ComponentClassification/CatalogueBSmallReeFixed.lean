module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeOuterInvolutions
public import CFSG.Walter.Ree.Model.Fusion

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (isQuasisimple_congr p_component_isomorphism_transport)

theorem small_Ree_involution_fixed_p_components (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    (α : MulAut (ReeTag.G2.reeGamma K a)) (hα : orderOf α = 2) (p : ℕ) (hp : p.Prime)
    (L : Subgroup (fixedSubgroup α)) (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨-, hinner⟩ := small_Ree_automorphism_involutions_inner a ha K hK
  obtain ⟨z, ⟨hz2, rfl⟩, -⟩ := hinner α hα
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, hfus⟩ := small_Ree_prime_field_involution_fusion a K hK w₀ hw₀
  obtain ⟨g, hgΓ, hgz⟩ := hfus z z.2 (by rw [Subgroup.orderOf_coe]; exact hz2)
  have hF : (fixedSubgroup (MulAut.conj z)).map (ReeTag.G2.reeGamma K a).subtype =
      ReeTag.G2.reeGamma K a ⊓ Subgroup.centralizer ({(z : ModGL ReeTag.G2.tag K)} : Set _) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h : z * y * z⁻¹ = y := hy
      have h' : y * z = z * y := by
        calc y * z = z * y * z⁻¹ * z := by rw [h]
          _ = z * y := by group
      exact congrArg Subtype.val h'
    · intro hx
      obtain ⟨hxΓ, hxz⟩ := Subgroup.mem_inf.1 hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hxz
      refine ⟨⟨x, hxΓ⟩, ?_, rfl⟩
      change z * ⟨x, hxΓ⟩ * z⁻¹ = ⟨x, hxΓ⟩
      apply Subtype.ext
      change (z : ModGL ReeTag.G2.tag K) * x * (z : ModGL ReeTag.G2.tag K)⁻¹ = x
      rw [← hxz]
      group
  have hC : (ReeTag.G2.reeGamma K a ⊓
      Subgroup.centralizer ({(z : ModGL ReeTag.G2.tag K)} : Set _)).map
        (MulAut.conj g).toMonoidHom = smallReeInvCentralizer a K := by
    ext x
    rw [smallReeInvCentralizer]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyΓ, hyz⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyz
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · change g * y * g⁻¹ ∈ ReeTag.G2.reeGamma K a
        exact (ReeTag.G2.reeGamma K a).mul_mem ((ReeTag.G2.reeGamma K a).mul_mem hgΓ hyΓ)
          ((ReeTag.G2.reeGamma K a).inv_mem hgΓ)
      · rw [Subgroup.mem_centralizer_singleton_iff, ← hgz]
        change g * y * g⁻¹ * (g * (z : ModGL ReeTag.G2.tag K) * g⁻¹) =
          g * (z : ModGL ReeTag.G2.tag K) * g⁻¹ * (g * y * g⁻¹)
        calc g * y * g⁻¹ * (g * (z : ModGL ReeTag.G2.tag K) * g⁻¹) =
            g * (y * (z : ModGL ReeTag.G2.tag K)) * g⁻¹ := by group
          _ = g * ((z : ModGL ReeTag.G2.tag K) * y) * g⁻¹ := by rw [hyz]
          _ = g * (z : ModGL ReeTag.G2.tag K) * g⁻¹ * (g * y * g⁻¹) := by group
    · intro hx
      obtain ⟨hxΓ, hxt⟩ := Subgroup.mem_inf.1 hx
      rw [Subgroup.mem_centralizer_singleton_iff, ← hgz] at hxt
      refine ⟨g⁻¹ * x * g, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
      · exact (ReeTag.G2.reeGamma K a).mul_mem
          ((ReeTag.G2.reeGamma K a).mul_mem ((ReeTag.G2.reeGamma K a).inv_mem hgΓ) hxΓ) hgΓ
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc g⁻¹ * x * g * (z : ModGL ReeTag.G2.tag K) =
            g⁻¹ * (x * (g * (z : ModGL ReeTag.G2.tag K) * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * (z : ModGL ReeTag.G2.tag K) * g⁻¹) * x) * g := by rw [hxt]
          _ = (z : ModGL ReeTag.G2.tag K) * (g⁻¹ * x * g) := by group
      · change g * (g⁻¹ * x * g) * g⁻¹ = x
        group
  let e : fixedSubgroup (MulAut.conj z) ≃* smallReeInvCentralizer a K :=
    ((fixedSubgroup (MulAut.conj z)).equivMapOfInjective (ReeTag.G2.reeGamma K a).subtype
        (ReeTag.G2.reeGamma K a).subtype_injective).trans
      ((MulEquiv.subgroupCongr hF).trans
        (((ReeTag.G2.reeGamma K a ⊓
            Subgroup.centralizer ({(z : ModGL ReeTag.G2.tag K)} : Set _)).equivMapOfInjective
          (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
          (MulEquiv.subgroupCongr hC)))
  have hL' := ((p_component_isomorphism_transport p hp e).1 L).1 hL
  have hq := (small_Ree_torus_involution_centralizer_p_components a K hK).2.1 p hp _ hL'
  exact (isQuasisimple_congr (L.equivMapOfInjective e.toMonoidHom e.injective)).2 hq

end CFSG.ComponentClassification.CatalogueBSmallRee
