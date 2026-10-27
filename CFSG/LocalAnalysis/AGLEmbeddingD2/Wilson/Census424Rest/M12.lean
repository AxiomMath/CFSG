module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofSpor
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporM12
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.SolvableKit

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint
open CFSG.GH74.M12.Hyp (G12)
open scoped commutatorElement

open CFSG.RankThree.PartTwo.Toolkit.M12 (E F A A')

theorem z_mem_E : ⁅CFSG.RankThree.PartTwo.Toolkit.M12.x, CFSG.RankThree.PartTwo.Toolkit.M12.y⁆ ∈ E :=
  Subgroup.subset_closure (Or.inl rfl)

theorem isSolvable_centralizer_of_mem_nine
    {B : Subgroup G12} (hB : B = E ∨ B = F ∨ B = A ∨ B = A') {v : G12} (hv : v ∈ B)
    (hv1 : v ≠ 1) : Group.IsSolvable (Subgroup.centralizer ({v} : Set G12)) := by
  have h54 : ∀ u : G12, Nat.card (Subgroup.centralizer ({u} : Set G12)) = 54 →
      Group.IsSolvable (Subgroup.centralizer ({u} : Set G12)) := fun u h =>
    isSolvable_of_card_dvd_two_three (a := 1) (b := 3) (by rw [h]; norm_num)
  have hN : ∀ u : G12, Nonempty (Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G12) : Set G12) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) →
      Group.IsSolvable (Subgroup.centralizer ({u} : Set G12)) := fun u ⟨e⟩ =>
    isSolvable_centralizer_of_normalizer_equiv u e
  have hZE : v ∈ (Subgroup.center CFSG.RankThree.PartTwo.Toolkit.M12.P0).map
      CFSG.RankThree.PartTwo.Toolkit.M12.P0.subtype → v ∈ E := by
    intro h
    rw [CFSG.RankThree.PartTwo.Toolkit.M12.center_P0] at h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.zpow_mem _ z_mem_E k
  rcases hB with rfl | rfl | rfl | rfl
  · exact h54 v (Item434SporGen.card_centralizer_E hv hv1)
  · exact h54 v (Item434SporGen.card_centralizer_F hv hv1)
  · by_cases hZ : v ∈ (Subgroup.center CFSG.RankThree.PartTwo.Toolkit.M12.P0).map
        CFSG.RankThree.PartTwo.Toolkit.M12.P0.subtype
    · exact h54 v (Item434SporGen.card_centralizer_E (hZE hZ) hv1)
    · exact hN v (CFSG.RankThree.PartTwo.Toolkit.M12.na_A hv hZ)
  · by_cases hZ : v ∈ (Subgroup.center CFSG.RankThree.PartTwo.Toolkit.M12.P0).map
        CFSG.RankThree.PartTwo.Toolkit.M12.P0.subtype
    · exact h54 v (Item434SporGen.card_centralizer_E (hZE hZ) hv1)
    · exact hN v (CFSG.RankThree.PartTwo.Toolkit.M12.na_A' hv hZ)


theorem census424_of_m12
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.Carrier .M12) : Census424 X := by
  intro D c d K h
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e' : X ≃* G12 := e with he'
  set D' : Subgroup G12 := D.map e'.toMonoidHom with hD'
  have hD'9 : Nat.card D' = 9 := by
    rw [hD', Subgroup.card_map_of_injective e'.injective, h.card_eq]
  have hD'p : IsPGroup 3 D' := IsPGroup.of_card (n := 2) (by rw [hD'9]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card Res423Two.card_P0_eq hD'p
  set P' := D'.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hmem : P' ∈ {B : Subgroup G12 | B ≤ CFSG.RankThree.PartTwo.Toolkit.M12.P0 ∧ Nat.card B = 9} :=
    ⟨Item434AltPerm.map_conj_inv_le hg,
      by rw [hP', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD'9]⟩
  rw [CFSG.RankThree.PartTwo.Toolkit.M12.nine_eq] at hmem
  let ψ : X ≃* G12 := e'.trans (MulAut.conj g⁻¹)
  have hcP : ψ c ∈ P' := ⟨e' c, ⟨c, h.c_mem, rfl⟩, rfl⟩
  have hc1 : ψ c ≠ 1 := fun h1 => h.c_ne_one (ψ.injective (h1.trans (map_one ψ).symm))
  have hB : P' = E ∨ P' = F ∨ P' = A ∨ P' = A' := by
    rcases hmem with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  exact Item424Res2.not_isSolvable_centralizer h
    (Item424Res2.isSolvable_centralizer_of_mulEquiv ψ c
      (isSolvable_centralizer_of_mem_nine hB hcP hc1))

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
