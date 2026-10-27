module

public import CFSG.LocalAnalysis.Mason73.Fusion32

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem exists_extremal_conj {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) (l : L4Model n) :
    ∃ μ : L4Model n, (∃ g : G, g * ι l * g⁻¹ = ι μ) ∧
      IsSylowOf 2 (ι.range ⊓ centralizer {ι μ}) (centralizer {ι μ}) ∧
      ∀ ν : L4Model n, (∃ g : G, g * ι l * g⁻¹ = ι ν) →
        Nat.card (centralizer {ν}) ≤ Nat.card (centralizer {μ}) := by
  classical
  haveI : Fintype (L4Model n) := Fintype.ofFinite _
  set s := Finset.univ.filter fun ν : L4Model n => ∃ g : G, g * ι l * g⁻¹ = ι ν
  have hne : s.Nonempty := ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, 1, by group⟩⟩
  obtain ⟨μ, hμs, hμ⟩ := s.exists_max_image (fun ν => Nat.card (centralizer {ν})) hne
  obtain ⟨-, gμ, hgμ⟩ := Finset.mem_filter.1 hμs
  have hmax : ∀ ν : L4Model n, (∃ g : G, g * ι l * g⁻¹ = ι ν) →
      Nat.card (centralizer {ν}) ≤ Nat.card (centralizer {μ}) := fun ν hν =>
    hμ ν (Finset.mem_filter.2 ⟨Finset.mem_univ _, hν⟩)
  refine ⟨μ, ⟨gμ, hgμ⟩, GHarris.isSylowOf_of_card_le hS ⟨μ, rfl⟩ fun g hg => ?_, hmax⟩
  obtain ⟨ν, hν⟩ := hg
  rw [← hν, card_range_inf_centralizer hι, card_range_inf_centralizer hι]
  exact hmax ν ⟨g⁻¹ * gμ, by rw [hν, ← hgμ]; group⟩

theorem exists_elementary_of_conj_extremal {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) {l μ : L4Model n}
    (hμ : IsSylowOf 2 (ι.range ⊓ centralizer {ι μ}) (centralizer {ι μ})) {g : G}
    (hg : g * ι l * g⁻¹ = ι μ) (E : Subgroup (L4Model n)) (hE : ∀ x ∈ E, x * x = 1)
    (hEl : E ≤ centralizer {l}) :
    ∃ E' : Subgroup (L4Model n), (∀ x ∈ E', x * x = 1) ∧ E' ≤ centralizer {μ} ∧
      Nat.card E' = Nat.card E := by
  obtain ⟨k, -, hk⟩ := GHarris.exists_conj_extremal (S := ι.range) hS.isPGroup hμ
    (u := ι l) (h := g) (by rw [← hg]; group)
  set φ : L4Model n →* G := (MulAut.conj k⁻¹).toMonoidHom.comp ι with hφ
  have hφapp : ∀ x, φ x = k⁻¹ * ι x * k := fun x => by simp [hφ]
  have hφinj : Function.Injective φ := fun x y h => hι (by
    rw [hφapp, hφapp] at h
    simpa using h)
  have himg : ∀ x ∈ E, φ x ∈ (ι.range ⊓ centralizer {ι μ} : Subgroup G) := by
    intro x hx
    rw [hφapp]
    refine hk _ (Subgroup.mem_inf.2 ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩)
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hEl hx)]
  have hle : E.map φ ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_inf.1 (himg x hx)).1
  refine ⟨(E.map φ).comap ι, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hy)
    apply hι
    rw [map_mul, ← hxy, ← map_mul, hE x hx, map_one, map_one]
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hy)
    have hc := (Subgroup.mem_inf.1 (himg x hx)).2
    rw [hxy, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hc
    exact Subgroup.mem_centralizer_singleton_iff.2 (hι hc)
  · rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hle,
      Subgroup.card_map_of_injective hφinj]

theorem card_le_eight_of_le_centralizer_s01 (hn : 3 ≤ n) {g : L4Model n}
    (hg : (piT g : Perm (Fin 4)) = swap 0 1) (E : Subgroup (L4Model n))
    (hE : ∀ x ∈ E, x * x = 1) (hEg : E ≤ centralizer {g}) : Nat.card E ≤ 8 := by
  set c := tT (n := n) (by omega)
  set f : L4Model n →* L4Model n := (MulAut.conj c).toMonoidHom with hf
  have hfapp : ∀ x, f x = c * x * c⁻¹ := fun x => by simp [hf]
  have hfinj : Function.Injective f := MulEquiv.injective _
  have hpi : (piT (c * g * c⁻¹) : Perm (Fin 4)) = swap 2 3 := by
    rw [map_mul, map_mul, map_inv]
    change (piT c : Perm (Fin 4)) * (piT g : Perm (Fin 4)) * (piT c : Perm (Fin 4))⁻¹ = _
    rw [hg, show (piT c : Perm (Fin 4)) = swap 0 2 * swap 1 3 from rfl]
    decide
  have h := card_le_eight_of_le_centralizer hn hpi (E.map f) ?_ ?_
  · rwa [Subgroup.card_map_of_injective hfinj] at h
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hfapp]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hEg hx)
    calc c * x * c⁻¹ * (c * g * c⁻¹) = c * (x * g) * c⁻¹ := by group
      _ = c * (g * x) * c⁻¹ := by rw [this]
      _ = c * g * c⁻¹ * (c * x * c⁻¹) := by group

end CFSG.LocalAnalysis.Mason73
