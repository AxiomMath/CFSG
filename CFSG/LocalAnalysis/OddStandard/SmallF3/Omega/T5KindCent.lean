module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFInduces
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem t5_induces_one_of_central {G : Type} [Group G] {L : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    {s : G} {x : ProjSim Q} (hx : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hc : s ∈ centralizer (L : Set G)) : x = 1 := by
  refine ff_induces_unique hQ h5 e hx ?_
  refine ⟨hx.1, fun l l' hl => ?_⟩
  have hcomm : (l : G) * s = s * (l : G) := Subgroup.mem_centralizer_iff.mp hc (l : G) l.2
  have hl' : l' = l := Subtype.ext (by rw [hl, ← hcomm, mul_inv_cancel_right])
  rw [hl', map_one, MulAut.one_apply]

theorem asc82Tab5_kind_ne_central_of :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
        (Kind5 L s 1 ∨ Kind5 L s 2 ∨ Kind5 L s 3 ∨ Kind5 L s 4 ∨ Kind5 L s 5) →
          s ∉ centralizer (L : Set G)
  := by
  intro G _ _ L _ s _ _ hk hc
  rcases hk with hk | hk | hk | hk | hk
  · obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, _, hind, y, hyx, hy⟩ :=
      (hk : InducesTypeSome L s 6 (-1) 4 (-1))
    have hx1 : x = 1 := t5_induces_one_of_central hQ (by omega) e hind hc
    exact hy.1 (projOrthToProjSim_injective (hyx.trans (hx1.trans (map_one _).symm)))
  · obtain ⟨α, V, _, _, _, Q, hQ, e, x, hdim, _, hind, y, hyx, hy⟩ :=
      (hk : ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α)
    have hx1 : x = 1 := t5_induces_one_of_central hQ (by omega) e hind hc
    exact hy.1 (projOrthToProjSim_injective (hyx.trans (hx1.trans (map_one _).symm)))
  · obtain ⟨α, V, _, _, _, Q, hQ, e, x, hdim, _, hind, y, hyx, hy⟩ :=
      (hk : ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α)
    have hx1 : x = 1 := t5_induces_one_of_central hQ (by omega) e hind hc
    exact hy.1 (projOrthToProjSim_injective (hyx.trans (hx1.trans (map_one _).symm)))
  · obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, _, hind, y, hyx, hy⟩ :=
      (hk : InducesProjective L 6 (-1) s)
    have hx1 : x = 1 := t5_induces_one_of_central hQ (by omega) e hind hc
    exact hy.1 (projOrthToProjSim_injective (hyx.trans (hx1.trans (map_one _).symm)))
  · obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, _, hind, _, hnot⟩ :=
      (hk : InducesOutsideGStar L 6 (-1) s)
    have hx1 : x = 1 := t5_induces_one_of_central hQ (by omega) e hind hc
    exact hnot ⟨1, by rw [map_one, hx1]⟩

end CFSG.OddStandard.SmallF3.Omega
