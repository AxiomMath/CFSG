module

public import CFSG.LieType.ChevTwo.OppCl.Toolkit

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section Lift

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

private def permOfRep (ρ : H →* Module.End F V) : H →* Equiv.Perm V where
  toFun h :=
    { toFun := fun v => ρ h v
      invFun := fun v => ρ h⁻¹ v
      left_inv := fun v => by
        show ρ h⁻¹ (ρ h v) = v
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := fun v => by
        show ρ h (ρ h⁻¹ v) = v
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp

private theorem permOfRep_injective (ρ : H →* Module.End F V) (hinj : Function.Injective ρ) :
    Function.Injective (permOfRep ρ) := by
  intro a b hab
  apply hinj
  ext v
  exact congrArg (fun f : Equiv.Perm V => f v) hab

private theorem conj_permOfRep (ρ : H →* Module.End F V) (r : Equiv.Perm V) (g h : H)
    (hgh : ∀ v, r (ρ g v) = ρ h (r v)) : r * permOfRep ρ g * r⁻¹ = permOfRep ρ h := by
  ext v
  show r (ρ g (r⁻¹ v)) = ρ h v
  rw [hgh, show r (r⁻¹ v) = v from r.apply_symm_apply v]

theorem exists_fixed_coset_H [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : H →* Module.End F V) (hinj : Function.Injective ρ)
    (Rh : Subgroup (Equiv.Perm V)) (hR : IsPGroup p Rh) (hN : ∀ r ∈ Rh, NormH ρ r)
    (G N : Subgroup H) (hNG : N ≤ G) (hNn : (N.subgroupOf G).Normal) (hN2 : IsPGroup 2 N)
    (hG : ∀ r ∈ Rh, ∀ g ∈ G, ∀ h : H, (∀ v, r (ρ g v) = ρ h (r v)) → h ∈ G)
    (g : H) (hgG : g ∈ G)
    (hg : ∀ r ∈ Rh, ∀ h : H, (∀ v, r (ρ g v) = ρ h (r v)) → g⁻¹ * h ∈ N) :
    ∃ c ∈ G, CommR ρ Rh c ∧ c⁻¹ * g ∈ N := by
  have hinjP : Function.Injective (permOfRep ρ) := permOfRep_injective ρ hinj
  have hG' : ∀ r ∈ Rh, ∀ x ∈ G.map (permOfRep ρ), r * x * r⁻¹ ∈ G.map (permOfRep ρ) := by
    rintro r hr _ ⟨g₀, hg₀, rfl⟩
    obtain ⟨h', hh'⟩ := hN r hr g₀
    rw [conj_permOfRep ρ r g₀ h' hh']
    exact Subgroup.mem_map_of_mem _ (hG r hr g₀ hg₀ h' hh')
  have hNn' : ((N.map (permOfRep ρ)).subgroupOf (G.map (permOfRep ρ))).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨g₀, hg₀, hxg⟩ := x.2
    obtain ⟨n₀, hn₀, hnn⟩ := hn
    have hc := hNn.conj_mem ⟨n₀, hNG hn₀⟩ (Subgroup.mem_subgroupOf.mpr hn₀) ⟨g₀, hg₀⟩
    rw [Subgroup.mem_subgroupOf] at hc
    refine ⟨g₀ * n₀ * g₀⁻¹, hc, ?_⟩
    rw [map_mul, map_mul, map_inv, hxg, hnn]
    rfl
  have hg' : ∀ r ∈ Rh, (permOfRep ρ g)⁻¹ * (r * permOfRep ρ g * r⁻¹) ∈ N.map (permOfRep ρ) := by
    intro r hr
    obtain ⟨h', hh'⟩ := hN r hr g
    rw [conj_permOfRep ρ r g h' hh', ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (hg r hr h' hh')
  obtain ⟨c', ⟨c, hcG, rfl⟩, hcomm, hcoset⟩ := exists_fixed_coset p hp2 Rh hR
    (G.map (permOfRep ρ)) hG' (N.map (permOfRep ρ)) (Subgroup.map_mono hNG) hNn'
    (hN2.map (permOfRep ρ)) (permOfRep ρ g) (Subgroup.mem_map_of_mem _ hgG) hg'
  refine ⟨c, hcG, fun r hr v => ?_, ?_⟩
  · exact congrArg (fun f : Equiv.Perm V => f v) (hcomm r hr)
  · rw [← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hinjP] at hcoset
    exact hcoset

end Lift

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
