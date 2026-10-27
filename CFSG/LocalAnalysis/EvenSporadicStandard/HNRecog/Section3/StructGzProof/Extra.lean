module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.MapShape

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem structGz_isPlusExtraspecial_map {C G : Type} [Group C] [Group G] {f : C →* G}
    (hf : Function.Injective f) {m : ℕ} {D : Subgroup C} (h : IsPlusExtraspecial m D) :
    IsPlusExtraspecial m (D.map f) := by
  obtain ⟨hExt, hcard, E, hED, hEel, hEcard⟩ := h
  obtain ⟨hEel', hEcard'⟩ := isElemTwo_map_of_injective hf ⟨hEel, hEcard⟩
  exact ⟨TwoHSData.isExtraspecial_of_mulEquiv (Subgroup.equivMapOfInjective D f hf) hExt,
    by rw [Subgroup.card_map_of_injective hf, hcard],
    E.map f, Subgroup.map_mono hED, hEel', hEcard'⟩

theorem structGz_isMinusExtraspecial_map {C G : Type} [Group C] [Group G] {f : C →* G}
    (hf : Function.Injective f) {m : ℕ} {D : Subgroup C} (h : IsMinusExtraspecial m D) :
    IsMinusExtraspecial m (D.map f) := by
  obtain ⟨hExt, hcard, hno⟩ := h
  refine ⟨TwoHSData.isExtraspecial_of_mulEquiv (Subgroup.equivMapOfInjective D f hf) hExt,
    by rw [Subgroup.card_map_of_injective hf, hcard], ?_⟩
  rintro ⟨E', hE'D, hE'el, hE'card⟩
  let E : Subgroup C := E'.comap f
  have hE'range : E' ≤ f.range := hE'D.trans (Subgroup.map_le_range f D)
  have hE'map : E.map f = E' := Subgroup.map_comap_eq_self hE'range
  have hED : E ≤ D := by
    rw [← Subgroup.map_le_map_iff_of_injective hf, hE'map]
    exact hE'D
  have hEcard : Nat.card E = 2 ^ (m + 1) := by
    rw [← Subgroup.card_map_of_injective (K := E) hf, hE'map, hE'card]
  have hEel : CFSG.Open.IsElemAbelian 2 E := by
    refine ⟨?_, ?_⟩
    · haveI : IsMulCommutative ↥E' := hE'el.1
      refine isMulCommutative_iff.mpr fun a b => ?_
      apply Subtype.ext
      apply hf
      show f ((a : C) * (b : C)) = f ((b : C) * (a : C))
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (mul_comm' (M := ↥E')
        (⟨f (a : C), Subgroup.mem_comap.mp a.2⟩ : ↥E')
        (⟨f (b : C), Subgroup.mem_comap.mp b.2⟩ : ↥E'))
    · intro x hx
      apply hf
      rw [map_pow, map_one]
      exact hE'el.2 (f x) (Subgroup.mem_comap.mp hx)
  exact hno ⟨E, hED, hEel, hEcard⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
