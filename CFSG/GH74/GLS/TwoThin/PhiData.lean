module

public import CFSG.GH74.GLS.TwoThin.Bridge
public import CFSG.GH74.GLS.TwoThin.Cover

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G] {y : G}

theorem exists_phi {K Λ : Subgroup G} (hΛK : Λ ≤ K) (hΛY : Λ ≤ centralizer ({y} : Set G))
    (hcov : ∀ k ∈ K, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o) :
    ∃ φ : ↥((Λ.subgroupOf (centralizer ({y} : Set G))).map
          (barMk ↥(centralizer ({y} : Set G)))) →* (↥K ⧸ pPrimeCore 2 ↥K),
      Function.Surjective φ ∧ Odd (Nat.card φ.ker) ∧
      ∀ (a : G) (ha : a ∈ Λ),
        φ ⟨barMk ↥(centralizer ({y} : Set G)) ⟨a, hΛY ha⟩,
          ⟨⟨a, hΛY ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩⟩ = hatMap hΛK ⟨a, ha⟩ := by
  set Y' := centralizer ({y} : Set G) with hY'
  let e : ↥(Λ.subgroupOf Y') ≃* ↥Λ := Subgroup.subgroupOfEquivOfLe hΛY
  let ψ : ↥(Λ.subgroupOf Y') →* (↥K ⧸ pPrimeCore 2 ↥K) := (hatMap hΛK).comp e.toMonoidHom
  have hψs : Function.Surjective ψ := (hatMap_surjective hΛK hcov).comp e.surjective
  have hψo : Odd (Nat.card ψ.ker) := by
    have h1 : ψ.ker = (hatMap hΛK).ker.comap e.toMonoidHom := (MonoidHom.comap_ker _ _).symm
    rw [h1]
    exact (odd_card_ker_hatMap hΛK).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ e.injective)
  let ρ : ↥(Λ.subgroupOf Y') →* ↥((Λ.subgroupOf Y').map (barMk ↥Y')) :=
    ((barMk ↥Y').comp (Λ.subgroupOf Y').subtype).codRestrict _ fun l => ⟨l, l.2, rfl⟩
  have hρs : Function.Surjective ρ := by
    intro k
    obtain ⟨c, hc, hck⟩ := k.2
    exact ⟨⟨c, hc⟩, Subtype.ext hck⟩
  have hρo : Odd (Nat.card ρ.ker) := by
    have h1 : ρ.ker = ((barMk ↥Y').domRestrict (Λ.subgroupOf Y')).ker :=
      MonoidHom.ker_codRestrict _ _ _
    rw [h1]
    exact OddKernel.odd_card_restriction_kernel (barMk ↥Y') odd_card_ker_barMk _
  have hker : ρ.ker ≤ ψ.ker :=
    normal_odd_le_ker ψ hψs (pPrimeCore_quotient_eq_bot ↥K) ρ.ker hρo
  obtain ⟨φ, hφs, hφo, hφρ⟩ := exists_odd_quotient_of_ker_le ρ hρs ψ hψs hker hψo
  refine ⟨φ, hφs, hφo, fun a ha => ?_⟩
  exact hφρ ⟨⟨a, hΛY ha⟩, Subgroup.mem_subgroupOf.mpr ha⟩

end CFSG.GH74.GLS.TwoThin
