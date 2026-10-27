module

public import CFSG.LieType.ChevTwo.OppCl.FormsCasesUrad
public import CFSG.LieType.ChevTwo.OppCl.FormsCasesLift

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section CaseM

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

variable {Φ : ReflForm F V} {Sing : V → Prop} {TS : Submodule F V → Prop}
  {ρ : H →* Module.End F V} {p : ℕ} [Fact p.Prime]
  {Rh : Subgroup (Equiv.Perm V)} {X : ℕ → Submodule F V} {m : ℕ} {M W' : Submodule F V}

theorem lift_mid_core (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (a : V →ₗ[F] V)
    (hac : ∀ r ∈ Rh, ∀ v, r (a v) = a (r v)) (u₀ : H) (hu₀ : u₀ ∈ Urad Φ ρ W')
    (hlead : ∀ w ∈ X m, ρ u₀ w - w - a w ∈ W') :
    ∃ y ∈ Urad Φ ρ W', CommR ρ Rh y ∧ ∀ w ∈ X m, ρ y w - w - a w ∈ W' := by
  have hW'ti : Φ.IsTotallyIsotropic W' := C.hTS _ C.hsplit.ts_W'
  have memU : ∀ {u : H}, u ∈ Urad Φ ρ W' ↔
      (∀ v ∈ W', ρ u v = v) ∧ ∀ v ∈ Φ.perp W', ρ u v - v ∈ W' :=
    fun {_} => mem_Urad_iff hW'ti C.hρ
  have fixW : ∀ {u : H}, u ∈ Urad Φ ρ W' → ∀ v ∈ W', ρ u v = v :=
    fun hu => (memU.mp hu).1
  have subP : ∀ {u : H}, u ∈ Urad Φ ρ W' → ∀ v, ρ u v - v ∈ Φ.perp W' := by
    intro u hu v
    unfold Urad at hu
    have h3 := ((mem_flagKernel ρ).mp hu).2 2 v
      (by rw [fw_of_ge (by omega)]; exact Submodule.mem_top)
    rwa [fw_two] at h3
  have hinv : ∀ (g : H) (v : V), ρ g⁻¹ (ρ g v) = v := fun g v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ (g : H) (v : V), ρ g (ρ g⁻¹ v) = v := fun g v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hrinv : ∀ (r : Equiv.Perm V) (v : V), r (r⁻¹ v) = v := fun r v => r.apply_symm_apply v
  obtain ⟨N, memN⟩ : ∃ N : Subgroup H, ∀ u, u ∈ N ↔
      (u ∈ Urad Φ ρ W' ∧ ∀ w ∈ X m, ρ u w - w ∈ W') :=
    ⟨{ carrier := {u | u ∈ Urad Φ ρ W' ∧ ∀ w ∈ X m, ρ u w - w ∈ W'}
       one_mem' := by
         refine ⟨one_mem _, fun w _ => ?_⟩
         simp
       mul_mem' := by
         rintro u₁ u₂ ⟨hu₁, hu₁'⟩ ⟨hu₂, hu₂'⟩
         refine ⟨mul_mem hu₁ hu₂, fun w hw => ?_⟩
         have e : ρ (u₁ * u₂) w - w = (ρ u₁ w - w) + ρ u₁ (ρ u₂ w - w) := by
           rw [map_mul, Module.End.mul_apply, map_sub]
           abel
         rw [e, fixW hu₁ _ (hu₂' w hw)]
         exact add_mem (hu₁' w hw) (hu₂' w hw)
       inv_mem' := by
         rintro u ⟨hu, hu'⟩
         refine ⟨inv_mem hu, fun w hw => ?_⟩
         have h1 := fixW (inv_mem hu) _ (hu' w hw)
         rw [map_sub, hinv u w] at h1
         have h2 : ρ u⁻¹ w - w = -(ρ u w - w) := by
           calc ρ u⁻¹ w - w = -(w - ρ u⁻¹ w) := by abel
             _ = -(ρ u w - w) := by rw [h1]
         rw [h2]
         exact neg_mem (hu' w hw) }, fun u => Iff.rfl⟩
  have hNG : N ≤ Urad Φ ρ W' := fun u hu => ((memN u).mp hu).1
  have hNn : (N.subgroupOf (Urad Φ ρ W')).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnU, hnN⟩ := (memN _).mp hn
    have hgU : (g : H) ∈ Urad Φ ρ W' := g.2
    show (g : H) * (n : H) * (g : H)⁻¹ ∈ N
    refine (memN _).mpr ⟨mul_mem (mul_mem hgU hnU) (inv_mem hgU), fun w hw => ?_⟩
    have hδ : ρ (g : H)⁻¹ w - w ∈ Φ.perp W' := subP (inv_mem hgU) w
    have hn1 := hnN w hw
    have hn2 := (memU.mp hnU).2 _ hδ
    have he : ρ (n : H) (ρ (g : H)⁻¹ w) - ρ (g : H)⁻¹ w ∈ W' := by
      have key : ρ (n : H) (ρ (g : H)⁻¹ w) - ρ (g : H)⁻¹ w =
          (ρ (n : H) w - w) + (ρ (n : H) (ρ (g : H)⁻¹ w - w) - (ρ (g : H)⁻¹ w - w)) := by
        rw [map_sub]
        abel
      rw [key]
      exact add_mem hn1 hn2
    have key2 : ρ ((g : H) * (n : H) * (g : H)⁻¹) w - w =
        ρ (g : H) (ρ (n : H) (ρ (g : H)⁻¹ w) - ρ (g : H)⁻¹ w) := by
      rw [map_sub, hinv' (g : H) w, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply]
    rw [key2, fixW hgU _ he]
    exact he
  have hN2 : IsPGroup 2 N := (urad_isPGroup (Φ := Φ) (U := W') C.hinj).to_le hNG
  have hG : ∀ r ∈ Rh, ∀ g ∈ Urad Φ ρ W', ∀ h : H,
      (∀ v, r (ρ g v) = ρ h (r v)) → h ∈ Urad Φ ρ W' := by
    intro r hr g hg h hgh
    have hr' : r⁻¹ ∈ Rh := inv_mem hr
    have hPinv : ∀ v ∈ Φ.perp W', r⁻¹ v ∈ Φ.perp W' :=
      perp_invariant Φ Rh C.hiso W' C.hW'inv r⁻¹ hr'
    have hhv : ∀ v, ρ h v = r (ρ g (r⁻¹ v)) := fun v => by
      have h1 := hgh (r⁻¹ v)
      rw [hrinv r v] at h1
      exact h1.symm
    refine memU.mpr ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [hhv v, fixW hg _ (C.hW'inv r⁻¹ hr' v hv), hrinv r v]
    · have h1 : ρ g (r⁻¹ v) - r⁻¹ v ∈ W' := (memU.mp hg).2 _ (hPinv v hv)
      have h2 : r (ρ g (r⁻¹ v) - r⁻¹ v) ∈ W' := C.hW'inv r hr _ h1
      have h3 : ρ h v - v = r (ρ g (r⁻¹ v) - r⁻¹ v) := by
        rw [hhv v, semilin_sub (C.hs hr), hrinv r v]
      rw [h3]
      exact h2
  have hg : ∀ r ∈ Rh, ∀ h : H, (∀ v, r (ρ u₀ v) = ρ h (r v)) → u₀⁻¹ * h ∈ N := by
    intro r hr h hrh
    have hh : h ∈ Urad Φ ρ W' := hG r hr u₀ hu₀ h hrh
    refine (memN _).mpr ⟨mul_mem (inv_mem hu₀) hh, fun w hw => ?_⟩
    have hr' : r⁻¹ ∈ Rh := inv_mem hr
    have hw₁ : r⁻¹ w ∈ X m := C.hXinv r⁻¹ hr' m w hw
    have hl₁ := C.hW'inv r hr _ (hlead _ hw₁)
    have hl₀ := hlead w hw
    have hhw : ρ h w = r (ρ u₀ (r⁻¹ w)) := by
      have h1 := hrh (r⁻¹ w)
      rw [hrinv r w] at h1
      exact h1.symm
    have e2 : r (ρ u₀ (r⁻¹ w) - r⁻¹ w - a (r⁻¹ w)) = ρ h w - w - a w := by
      rw [semilin_sub (C.hs hr), semilin_sub (C.hs hr), hac r hr, hrinv r w, hhw]
    rw [e2] at hl₁
    have hdiff : ρ h w - ρ u₀ w ∈ W' := by
      have key : ρ h w - ρ u₀ w = (ρ h w - w - a w) - (ρ u₀ w - w - a w) := by abel
      rw [key]
      exact sub_mem hl₁ hl₀
    have e1 : ρ (u₀⁻¹ * h) w - w = ρ u₀⁻¹ (ρ h w - ρ u₀ w) := by
      rw [map_sub, hinv u₀ w, map_mul, Module.End.mul_apply]
    rw [e1, fixW (inv_mem hu₀) _ hdiff]
    exact hdiff
  obtain ⟨c, hcG, hcomm, hcN⟩ := exists_fixed_coset_H p hp2 ρ C.hinj Rh C.hR C.hN
    (Urad Φ ρ W') N hNG hNn hN2 hG u₀ hu₀ hg
  refine ⟨c, hcG, hcomm, fun w hw => ?_⟩
  have hδ : ρ c⁻¹ (ρ u₀ w) - w ∈ W' := by
    have h1 := ((memN _).mp hcN).2 w hw
    rwa [map_mul, Module.End.mul_apply] at h1
  have hfix := fixW hcG _ hδ
  rw [map_sub, hinv' c (ρ u₀ w)] at hfix
  have hδ' : ρ u₀ w - ρ c w ∈ W' := by
    rw [hfix]
    exact hδ
  have key : ρ c w - w - a w = (ρ u₀ w - w - a w) - (ρ u₀ w - ρ c w) := by abel
  rw [key]
  exact sub_mem (hlead w hw) hδ'

end CaseM

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
