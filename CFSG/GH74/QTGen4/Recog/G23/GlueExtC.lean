
module

public import CFSG.GH74.QTGen4.Recog.G23.GlueExtCBase

public import CFSG.GH74.QTGen4.Recog.G23.GlueExt
public import CFSG.GH74.QTGen4.Recog.G23.GlueExtB
public meta import CFSG.Certificates.CosetTablePresented
public meta import CFSG.GH74.QTGen4.Recog.G23.Words
public meta import CFSG.GH74.QTGen4.Recog.G23.GlueExt
public meta import CFSG.GH74.QTGen4.Recog.G23.GlueExtB

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.CosetTable

theorem exists_iso_PG_Hc : ∃ ψ : PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5 ≃* Hc,
    ∀ i, ((ψ (PresentedGroup.of i) : Hc) : Equiv.Perm (Fin 32)) = f5 i := by
  have : Finite (PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5) := g23H5_card_le.1
  have hrange : ∀ x, φ5 x ∈ Hc := fun x => by
    rw [← range_φ5]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let ψ0 : PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5 →* Hc := φ5.codRestrict Hc hrange
  have hsurj : Function.Surjective ψ0 := by
    intro y
    have hy : (y : Equiv.Perm (Fin 32)) ∈ φ5.range := by
      rw [range_φ5]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hbij : Function.Bijective ψ0 :=
    hsurj.bijective_of_nat_card_le (by rw [Hc_card]; exact g23H5_card_le.2)
  refine ⟨MulEquiv.ofBijective ψ0 hbij, fun i => ?_⟩
  exact φ5_of i

end CFSG.GH74.QTGen4.Recog.G23
