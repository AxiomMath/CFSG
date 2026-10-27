module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.Universal.RootData
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem conjSub_rootPair_le
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (i : Fin D.rank) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    conjSub (n i) (D.rootGroup γ ⊔ D.rootGroup (-γ)) ≤
      D.rootGroup (weylAction D.isFiniteType
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) γ) ⊔
      D.rootGroup (-(weylAction D.isFiniteType
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) γ)) := by
  have hγ' : -γ ∈ D.roots := OfCartan.neg_mem_roots D.isFiniteType hγ
  unfold conjSub
  rw [Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hct.conj_mem i γ hγ x hx
  · rintro _ ⟨x, hx, rfl⟩
    have := hct.conj_mem i (-γ) hγ' x hx
    rwa [map_neg] at this

theorem commutes_mono {A B A' B' : Subgroup K} (h : Commutes A B) (hA : A' ≤ A) (hB : B' ≤ B) :
    Commutes A' B' := fun x hx y hy => h x (hA hx) y (hB hy)

theorem conjSub_eq_of_commutes_mem {g : K} {L B : Subgroup K} (hg : g ∈ L) (h : Commutes L B) :
    conjSub g B = B := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hb
    have e : x = g⁻¹ * x * g := by
      have h1 := h g hg _ hb
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = (g⁻¹ * x * g) * g * g⁻¹ := by rw [h1]
        _ = g⁻¹ * x * g := by group
    rwa [← e] at hb
  · intro hx
    have h1 := h g⁻¹ (L.inv_mem hg) x hx
    have e : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = x * g⁻¹ * g := by rw [h1]
        _ = x := by group
    rwa [e]

end CFSG.ClassicalInvolution.RouteD.Exotic
