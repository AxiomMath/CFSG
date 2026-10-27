module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCData

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem OuterData.of_model {Y R : Type*} [Group Y] [Group R] [Finite (MulAut Y)]
    (e : R ≃* MulAut Y) (K : Subgroup R) (hK : IsPGroup 2 K) (hidx : ¬ 2 ∣ K.index)
    (t : Y) (r : R) (hr : e r = MulAut.conj t) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (h4 : ∃ g : Y, g * g * (g * g) = t) (hrK : r ∈ K)
    (hcen : ∀ y ∈ K, (∀ x ∈ K, x * y = y * x) ↔ (y = 1 ∨ y = r)) : OuterData Y := by
  refine OuterData.of_sylow (K.map e.toMonoidHom) ?_ ?_ ⟨t, ht2, ht1, h4, ⟨r, hrK, hr⟩, ?_⟩
  · exact hK.of_equiv (K.equivMapOfInjective e.toMonoidHom e.injective)
  · have h : (K.map e.toMonoidHom).index = K.index := Subgroup.index_map_equiv (H := K) e
    rw [h]
    exact hidx
  · rintro _ ⟨y, hy, rfl⟩
    have hA : (∀ β ∈ K.map e.toMonoidHom, β * e y = e y * β) ↔ ∀ x ∈ K, x * y = y * x := by
      constructor
      · intro hall x hx
        have h1 := hall (e x) ⟨x, hx, rfl⟩
        rw [← map_mul, ← map_mul] at h1
        exact e.injective h1
      · rintro hall _ ⟨x, hx, rfl⟩
        change e x * e y = e y * e x
        rw [← map_mul, ← map_mul, hall x hx]
    have hB : (y = 1 ∨ y = r) ↔ (e y = 1 ∨ e y = MulAut.conj t) := by
      rw [← hr]
      constructor
      · rintro (h | h)
        · exact Or.inl (by rw [h, map_one])
        · exact Or.inr (by rw [h])
      · rintro (h | h)
        · exact Or.inl (e.injective (h.trans (map_one e).symm))
        · exact Or.inr (e.injective h)
    exact hA.trans ((hcen y hy).trans hB)

end CFSG.EvenSporadicStandard.Fin76b
