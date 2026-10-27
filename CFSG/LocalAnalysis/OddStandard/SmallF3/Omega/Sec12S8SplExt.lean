module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplExtA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplExtB

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem s8_split_ext {G : Type} [Group G] {V : Subgroup G} (hcomm : ∀ a b : ↥V, a * b = b * a)
    {Γ : Type} [Group Γ] [Finite Γ] (ι : ↥V →* Γ) (ρ : Γ →* MulAut ↥V)
    (hι : Function.Injective ι) (hker : ρ.ker = ι.range)
    (hequi : ∀ (γ : Γ) (a : ↥V), γ * ι a * γ⁻¹ = ι (ρ γ a)) (hwr : Sec128WrNat V ρ.range) :
    ∃ K : Subgroup Γ, K ⊓ ι.range = ⊥ ∧ K ⊔ ι.range = ⊤ := by
  obtain ⟨Z, V1, V2, τ, hZ, hZidx, hsp, hτY, hτZ, hτV⟩ := hwr
  have hsup : V1 ⊔ V2 = ⊤ := by
    obtain ⟨_, _, _, hs, _⟩ := hsp
    exact hs
  obtain ⟨φ1, φ2, α, β, h⟩ := s8_ext_data hcomm ι ρ hι hker hequi hZ hsp
  have hG0 : (Z.comap ρ).index = 2 := by
    rw [Subgroup.index_comap]
    exact hZidx
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hτY
  have htG0 : t ∉ Z.comap ρ := by
    rw [Subgroup.mem_comap, ht]
    exact hτZ
  have hιmem : ∀ a : ↥V, ι a ∈ Z.comap ρ := by
    intro a
    have h1 : ι a ∈ ρ.ker := by
      rw [hker]
      exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp h1]
    exact Subgroup.one_mem Z
  have hmapLe : ∀ W : Subgroup ↥V, W.map ι ≤ Z.comap ρ := by
    intro W x hx
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hιmem a
  have hv : (V1.map ι).map (MulAut.conj t).toMonoidHom = V2.map ι := by
    have hcomp : (MulAut.conj t).toMonoidHom.comp ι = ι.comp (τ : ↥V ≃* ↥V).toMonoidHom := by
      ext a
      show t * ι a * t⁻¹ = ι (τ a)
      rw [hequi t a, ht]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hτV]
  obtain ⟨K, hK1, hK2⟩ := s8_glue_data h (hmapLe V1) (hmapLe V2) hG0 htG0 hv
  have hrange : V1.map ι ⊔ V2.map ι = ι.range := by
    rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map]
  rw [hrange] at hK1 hK2
  exact ⟨K, hK1, hK2⟩

end CFSG.OddStandard.SmallF3.Omega
