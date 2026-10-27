module

public import CFSG.LieType.AschbacherSeitz.RootGroupTransport
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.LieType.Steinberg.Exceptional.Universal

public section

namespace CFSG.LieType.AschbacherSeitz

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6
open CFSG.LieType.Steinberg.Exceptional

theorem exists_involution_mem_ggRootSub
    {U G : Type} [Group U] [Group G] {Δ : UniversalRootDatum U} {ψ : U →* G}
    {γ : Fin Δ.rank → ℤ} (hγ : γ ∈ Δ.roots) (u : U)
    (hker : ψ.ker ≤ Subgroup.center U)
    (hsq : ∀ x ∈ Δ.rootGroup γ, x * x = 1)
    (hne : Δ.rootGroup γ ≠ ⊥)
    (hdisj : Δ.rootGroup γ ⊓ Subgroup.center U = ⊥) :
    ∃ r ∈ ggRootSub Δ ψ γ u, orderOf r = 2 := by
  obtain ⟨⟨x, hx⟩, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hx1 : x ≠ 1 := fun h => hxne (Subtype.ext h)
  let y : U := u * x * u⁻¹
  have hy_mem : y ∈ (Δ.rootGroup γ).map (MulAut.conj u).toMonoidHom :=
    ⟨x, hx, by simp [y, MulAut.conj_apply]⟩
  have hysq : y * y = 1 := by
    dsimp only [y]
    calc (u * x * u⁻¹) * (u * x * u⁻¹) = u * (x * x) * u⁻¹ := by group
      _ = 1 := by rw [hsq x hx]; group
  have hψne : ψ y ≠ 1 := by
    intro h
    have hyker : y ∈ ψ.ker := by simpa [MonoidHom.mem_ker] using h
    have hycen : y ∈ Subgroup.center U := hker hyker
    have hxcen : x ∈ Subgroup.center U := by
      have hc := (inferInstance : (Subgroup.center U).Normal).conj_mem y hycen u⁻¹
      rwa [inv_inv, show u⁻¹ * y * u = x by dsimp only [y]; group] at hc
    have hmem : x ∈ Δ.rootGroup γ ⊓ Subgroup.center U := ⟨hx, hxcen⟩
    rw [hdisj] at hmem
    exact hx1 (Subgroup.mem_bot.1 hmem)
  refine ⟨ψ y, ⟨y, hy_mem, rfl⟩, ?_⟩
  have hψsq : ψ y * ψ y = 1 := by rw [← map_mul, hysq, map_one]
  exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using hψsq) hψne

end CFSG.LieType.AschbacherSeitz

end
