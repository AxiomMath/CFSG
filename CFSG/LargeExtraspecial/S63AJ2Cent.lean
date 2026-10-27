module

public import CFSG.LargeExtraspecial.AS35CS63J2E
public import CFSG.LargeExtraspecial.S63AJ2CentModel

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S63

theorem j2CentInput : J2CentInput := by
  intro Y _ hY s hs N hNC hNn hN2 hsN hN16
  obtain ⟨e₀⟩ := hY
  let e : Y ≃* Sporadic.Schreier.j2P := e₀.trans Sporadic.Schreier.j2PermEquiv
  let ι : Y →* Equiv.Perm (Fin 315) := Sporadic.Schreier.j2P.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hrange : ι.range = Sporadic.Schreier.j2P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  have hτP : ι s ∈ Sporadic.Schreier.j2P := hrange ▸ ⟨s, rfl⟩
  have hτ : orderOf (ι s) = 2 := by rw [orderOf_injective ι hι, hs]
  have hC : (centralizer ({s} : Set Y)).map ι =
      Sporadic.Schreier.j2P ⊓ centralizer ({ι s} : Set (Equiv.Perm (Fin 315))) := by
    rw [Sporadic.SmallOddCore.map_centralizer_eq_inf hι, hrange, Set.image_singleton]
  have h := centConcl_j2P hτP hτ
  rw [← hC] at h
  obtain ⟨h1, h2, h3⟩ := CentConcl.of_map hι h N hNC hNn hN2 hsN hN16
  refine ⟨h1, h2, fun x hx => h3 ⟨?_, hx⟩⟩
  exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hx) s hsN).symm

end S63

end CFSG.LargeExtraspecial
