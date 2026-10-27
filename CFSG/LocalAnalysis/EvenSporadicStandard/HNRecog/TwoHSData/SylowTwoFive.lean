module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

private theorem factorization_100_two : (100 : ℕ).factorization 2 = 2 := by
  rw [show (100 : ℕ) = 2 ^ 2 * 25 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_closure_of_sylow_two {G : Type*} [Group G] [Finite G] {a ρ u : G}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hacen : ∀ g : G, g * a = a * g) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hau : a ≠ u) (huρ : u * ρ = ρ * u)
    (hcard : Nat.card ↥(centralizer ({ρ} : Set G)) = 100)
    (T : Sylow 2 ↥(centralizer ({ρ} : Set G))) :
    ∃ u' : G, IsConj u u' ∧
      (T : Subgroup ↥(centralizer ({ρ} : Set G))).map (centralizer ({ρ} : Set G)).subtype =
        closure ({a, u'} : Set G) := by
  let C : Subgroup G := centralizer ({ρ} : Set G)
  have haC : a ∈ C := by
    change a ∈ centralizer ({ρ} : Set G)
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hacen ρ
  have huC : u ∈ C := by
    change u ∈ centralizer ({ρ} : Set G)
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact huρ.symm
  let V : Subgroup G := closure ({a, u} : Set G)
  have hVC : V ≤ C := by
    rw [show V = closure ({a, u} : Set G) from rfl, Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact haC
    · exact huC
  have hau' : a * u = u * a := (hacen u).symm
  have hVcard : Nat.card V = 4 := by
    rw [show V = closure ({a, u} : Set G) from rfl]
    exact card_closure_pair ha2 hu2 hau' ha1 hu1 hau
  have hfac : (Nat.card C).factorization 2 = 2 := by
    rw [show Nat.card C = (100 : ℕ) from hcard]
    exact factorization_100_two
  have hS'card : Nat.card (V.subgroupOf C) = 2 ^ (Nat.card C).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv, hVcard, hfac]
    norm_num
  let S' : Sylow 2 C := Sylow.ofCard (V.subgroupOf C) hS'card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S' T
  refine ⟨(g : G) * u * (g : G)⁻¹, isConj_iff.mpr ⟨(g : G), rfl⟩, ?_⟩
  have hS'coe : (S' : Subgroup C) = V.subgroupOf C := rfl
  have hfa : (MulAut.conj (g : G)).toMonoidHom a = a := by
    change MulAut.conj (g : G) a = a
    simp [MulAut.conj_apply, hacen (g : G)]
  have hfu : (MulAut.conj (g : G)).toMonoidHom u = (g : G) * u * (g : G)⁻¹ := by
    change MulAut.conj (g : G) u = (g : G) * u * (g : G)⁻¹
    rw [MulAut.conj_apply]
  have himg : (MulAut.conj (g : G)).toMonoidHom '' ({a, u} : Set G) =
      ({a, (g : G) * u * (g : G)⁻¹} : Set G) := by
    rw [Set.image_insert_eq, Set.image_singleton, hfa, hfu]
  rw [← hg, Sylow.coe_subgroup_smul, hS'coe, Subgroup.conj_smul_subgroupOf hVC g,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.conj_smul_le_of_le hVC g)]
  change V.map (MulAut.conj (g : G)).toMonoidHom = closure ({a, (g : G) * u * (g : G)⁻¹} : Set G)
  rw [show V = closure ({a, u} : Set G) from rfl, MonoidHom.map_closure, himg]

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
