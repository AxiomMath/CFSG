module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_subgroup_card_four_of_isElemAbelian {U : Subgroup G}
    (hU : IsElemAbelian 2 U) (h2 : 2 < Nat.card U) :
    ∃ U' : Subgroup G, U' ≤ U ∧ IsElemAbelian 2 U' ∧ Nat.card U' = 2 ^ 2 := by
  obtain ⟨n, hn⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_card_eq_pow_of_isElemAbelian
    Nat.prime_two hU
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn, pow_one] at h1
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card U := by
    rw [hn]
    exact pow_dvd_pow 2 hn2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨K.map U.subtype, Subgroup.map_subtype_le K,
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hU (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective U.subtype_injective, hK]

theorem exists_codim_twoRank (h336 : I336UsedAt) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B T : Subgroup G} (hB : IsElemAbelian p B) (hT : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTB : (⁅T, B⁆ : Subgroup G) ≠ ⊥)
    (hQ8 : p = 3 → IsEmpty (T ≃* QuaternionGroup 2)) :
    ∃ (E : Subgroup G) (k : ℕ), E ≤ B ∧ 1 ≤ k ∧ Nat.card E * p ^ k = Nat.card B ∧
      (⁅T ⊓ Subgroup.centralizer (E : Set G), B⁆ : Subgroup G) ≠ ⊥ ∧
      ∃ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer (E : Set G) ∧ IsElemAbelian 2 U ∧
        Nat.card U = 2 ^ (k + 1) := by
  by_cases h : ∃ A : Subgroup G, A ≤ B ∧ Nat.card A * p = Nat.card B ∧
      (⁅T ⊓ Subgroup.centralizer (A : Set G), B⁆ : Subgroup G) ≠ ⊥ ∧
      ∃ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 2 U ∧
        2 < Nat.card U
  · obtain ⟨A, hAB, hA, hcomm, U, hU, hUe, hUcard⟩ := h
    obtain ⟨U', hU'U, hU'e, hU'card⟩ := exists_subgroup_card_four_of_isElemAbelian hUe hUcard
    refine ⟨A, 1, hAB, le_refl 1, by rw [pow_one]; exact hA, hcomm, U', hU'U.trans hU, hU'e, ?_⟩
    norm_num [hU'card]
  · have hneg : ∀ D₀ : Subgroup G, D₀ ≤ B → Nat.card D₀ * p = Nat.card B →
        (⁅T ⊓ Subgroup.centralizer (D₀ : Set G), B⁆ : Subgroup G) ≠ ⊥ →
        ∀ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer (D₀ : Set G) →
          IsElemAbelian 2 U → Nat.card U ≤ 2 := by
      intro A hAB hA hcomm U hU hUe
      by_contra hlt
      exact h ⟨A, hAB, hA, hcomm, U, hU, hUe, by omega⟩
    obtain ⟨hp3, hcase⟩ := h336 G p hp hp2 T B hT hB hBT hTB hneg
    subst hp3
    rcases hcase with hne | ⟨E, hEB, hE9, hcomm, U, hU, hUe, hU8⟩
    · exfalso
      obtain ⟨e⟩ := hne
      haveI := hQ8 rfl
      exact IsEmpty.false e
    · refine ⟨E, 2, hEB, by norm_num, ?_, hcomm, U, hU, hUe, ?_⟩
      · norm_num [← hE9]
      · norm_num [hU8]

end CFSG.LocalAnalysis.GLTheoremA.P55
