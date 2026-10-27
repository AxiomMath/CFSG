module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightNormalizer

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

theorem pCore_perm_eq_bot_zero {m : ℕ} (hm : m = 0 ∨ m = 1 ∨ m = 3 ∨ 5 ≤ m) :
    CFSG.pCore 2 (Perm (Fin m)) = ⊥ := by
  rcases hm with rfl | hm
  · exact Subsingleton.elim _ _
  · exact pCore_perm_eq_bot (by omega)

theorem normal_isPGroup_le_Wr {r s : ℕ} (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r)
    (hs : s = 0 ∨ s = 1 ∨ s = 3 ∨ 5 ≤ s) (U : Subgroup (Perm (OmegaE r s))) (hU : IsPGroup 2 U)
    (hUN : ∀ g ∈ U, g ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))))
    (hnorm : ∀ h ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))), ∀ u ∈ U,
      h * u * h⁻¹ ∈ U) : U ≤ Wr r s := by
  classical
  let ι : ↥(wStab (Fin r) Bool) × Perm (Fin s) →* Perm (OmegaE r s) :=
    (Perm.sumCongrHom (Fin r × Bool) (Fin s)).comp
      (MonoidHom.prodMap (wStab (Fin r) Bool).subtype (MonoidHom.id _))
  have hι : ∀ x, ι x = Perm.sumCongr x.1.1 x.2 := fun x => rfl
  have hιinj : Function.Injective ι := by
    intro x y h
    have h1 := Perm.sumCongrHom_injective (α := Fin r × Bool) (β := Fin s)
      (show Perm.sumCongrHom (Fin r × Bool) (Fin s) (x.1.1, x.2) =
        Perm.sumCongrHom (Fin r × Bool) (Fin s) (y.1.1, y.2) from h)
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    exact Prod.ext (Subtype.ext e1) e2
  have hιN : ∀ x, ι x ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := fun x => by
    rw [hι]; exact sumCongr_mem_normalizer x.1.2 x.2
  let Uh : Subgroup (↥(wStab (Fin r) Bool) × Perm (Fin s)) := U.comap ι
  have hUh2 : IsPGroup 2 Uh := hU.comap_of_injective ι hιinj
  have hUhn : Uh.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show ι (g * n * g⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (hιN g) _ hn
  let Φ : ↥(wStab (Fin r) Bool) × Perm (Fin s) →* Perm (Fin r) × Perm (Fin s) :=
    MonoidHom.prodMap (wStabAction (Fin r)) (MonoidHom.id _)
  have hΦ : Function.Surjective Φ := by
    rintro ⟨π, τ⟩
    refine ⟨(⟨wLift π, wLift_mem_wStab π⟩, τ), Prod.ext ?_ rfl⟩
    refine Equiv.ext fun a => ?_
    have := wStabAction_apply (ι := Fin r) ⟨wLift π, wLift_mem_wStab π⟩ (a, false)
    show wStabAction (Fin r) ⟨wLift π, wLift_mem_wStab π⟩ a = π a
    simpa [wLift_apply] using this
  have hbot : CFSG.pCore 2 (Perm (Fin r) × Perm (Fin s)) = ⊥ :=
    pCore_prod_eq_bot (pCore_perm_eq_bot (by omega)) (pCore_perm_eq_bot_zero hs)
  have hle : Uh.map Φ ≤ CFSG.pCore 2 (Perm (Fin r) × Perm (Fin s)) :=
    le_sSup ⟨Subgroup.Normal.map hUhn Φ hΦ, hUh2.map Φ⟩
  rw [hbot] at hle
  intro u hu
  obtain ⟨σ1, h1, σ2, rfl⟩ := mem_normalizer_Wr_iff.1 (hUN u hu)
  have hx : (⟨σ1, h1⟩, σ2) ∈ Uh := by
    show ι (⟨σ1, h1⟩, σ2) ∈ U
    rw [hι]; exact hu
  have h0 : Φ (⟨σ1, h1⟩, σ2) = 1 := by
    have : Φ (⟨σ1, h1⟩, σ2) ∈ (⊥ : Subgroup _) := hle ⟨_, hx, rfl⟩
    simpa using this
  have hσ2 : σ2 = 1 := by
    have := congrArg Prod.snd h0
    simpa [Φ] using this
  have hσ1 : σ1 ∈ blockFix (Fin r) := by
    intro p
    have h4 : wStabAction (Fin r) ⟨σ1, h1⟩ = 1 := congrArg Prod.fst h0
    have h3 := wStabAction_apply (ι := Fin r) ⟨σ1, h1⟩ p
    rw [h4] at h3
    exact h3.symm
  refine ⟨σ1, hσ1, ?_⟩
  rw [hσ2]
  rfl

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
