module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L47Transfer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.Quasithin.Background.A1cTransferVariants

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4F_thompson_hom [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {t : G} (ht : orderOf t = 2) {T : Subgroup G} (hT : IsSylow2Of T ⊤) (htT : t ∈ T)
    (ψ : ↥T →* ℤˣ)
    (hψ : ∀ (g : G) (hg : g ∈ T), (∃ x : G, g = x⁻¹ * t * x) → ψ ⟨g, hg⟩ = -1) : False := by
  classical
  have hψt : ψ ⟨t, htT⟩ = -1 := hψ t htT ⟨1, by simp⟩
  have hsurj : Function.Surjective ψ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one ψ⟩
    · exact ⟨⟨t, htT⟩, hψt⟩
  have hindex : ψ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  let T₀ : Subgroup G := ψ.ker.map T.subtype
  have hsub : T₀.subgroupOf T = ψ.ker :=
    Subgroup.comap_map_eq_self_of_injective T.subtype_injective ψ.ker
  have hQP : T₀ ≤ T := Subgroup.map_subtype_le ψ.ker
  have hQidx : T₀.relIndex T = 2 := by
    show (T₀.subgroupOf T).index = 2
    rw [hsub, hindex]
  have hQu : ∀ x ∈ (⊤ : Subgroup G), x⁻¹ * t * x ∉ T₀ := by
    intro x _ hx
    have hgT : x⁻¹ * t * x ∈ T := hQP hx
    have hker : (⟨x⁻¹ * t * x, hgT⟩ : ↥T) ∈ ψ.ker := by
      rw [← hsub]
      exact Subgroup.mem_subgroupOf.mpr hx
    have h1 : ψ ⟨x⁻¹ * t * x, hgT⟩ = 1 := MonoidHom.mem_ker.mpr hker
    have hm1 : ψ ⟨x⁻¹ * t * x, hgT⟩ = -1 := hψ (x⁻¹ * t * x) hgT ⟨x, rfl⟩
    have hne : (1 : ℤˣ) ≠ -1 := by
      rw [Int.units_ne_iff_eq_neg]
      simp
    exact hne (h1.symm.trans hm1)
  obtain ⟨N, _, hNn, hsq, htN⟩ :=
    CFSG.Quasithin.thompson_transfer_exists_normal_subgroup
      (X := ⊤) (P := T) (Q := T₀) le_top hT.2.1 hT.2.2 hQP hQidx (Subgroup.mem_top t) ht hQu
  exact sec4_simple_squares hG hnab hNn hsq htN

end CFSG.OddStandard.SmallF3.Omega
