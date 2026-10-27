module

public import CFSG.LieType.BorelTits.RadicalLinear.Main
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

open Matrix
open CFSG.Open (StatedProj StatedSL)

theorem radicalTwoSubgroup_statedProj (r : ℕ) (K : Type) [Field K] [Finite K]
    (hK : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f) (U : Subgroup (StatedProj (StatedSL r K)))
    (hU : U ≠ ⊥)
    (hrad : CFSG.inSubgroup (CFSG.pCore 2)
      (Subgroup.normalizer (U : Set (StatedProj (StatedSL r K)))) = U) :
    ∃ (k : ℕ) (m : Fin k → ℕ) (hk : 2 ≤ k), (∀ i, 1 ≤ m i) ∧ ∑ i, m i = r ∧
      Nat.card ↥(Subgroup.center ↥U) =
        Nat.card K ^ (m ⟨0, by omega⟩ * m ⟨k - 1, by omega⟩) ∧
      Nat.card U = Nat.card K ^ ((r ^ 2 - ∑ i, m i ^ 2) / 2) ∧
      ∀ S : Subgroup (↥(Subgroup.normalizer (U : Set (StatedProj (StatedSL r K)))) ⧸
          U.subgroupOf (Subgroup.normalizer (U : Set (StatedProj (StatedSL r K))))),
        S.Normal → CFSG.IsQuasisimple S →
          ∃ i, 2 ≤ m i ∧ ¬ (m i = 2 ∧ Nat.card K = 2) ∧
            ∃ Z' : Subgroup S, Z' ≤ Subgroup.center S ∧ ∃ _ : Z'.Normal,
              Nonempty ((S ⧸ Z') ≃* StatedProj (StatedSL (m i) K)) := by
  classical
  obtain ⟨f, hf, hcard⟩ := hK
  haveI : CharP K 2 := by
    let _ : Fintype K := Fintype.ofFinite K
    have h2dvd : 2 ∣ Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hcard]
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [pow_succ]
      exact dvd_mul_left 2 (2 ^ g)
    have hchar : ringChar K = 2 :=
      FiniteField.even_card_iff_char_two.mpr (Nat.mod_eq_zero_of_dvd h2dvd)
    have h := ringChar.charP K
    rwa [hchar] at h
  let N : Subgroup (StatedSL r K) :=
    (CFSG.Open.StatedScalars (Fin r) K).subgroupOf (StatedSL r K)
  let eSL := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL r K
  let π : SpecialLinearGroup (Fin r) K →* StatedProj (StatedSL r K) :=
    (QuotientGroup.mk' N).comp eSL.toMonoidHom
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨x, rfl⟩ := eSL.surjective z
    exact ⟨x, rfl⟩
  have hker : π.ker = Subgroup.center (SpecialLinearGroup (Fin r) K) := by
    have hN : N = (Subgroup.center (SpecialLinearGroup (Fin r) K)).map eSL.toMonoidHom :=
      (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars r K).symm
    calc π.ker = Subgroup.comap eSL.toMonoidHom (QuotientGroup.mk' N).ker := rfl
      _ = Subgroup.comap eSL.toMonoidHom N := by rw [QuotientGroup.ker_mk' N]
      _ = Subgroup.center (SpecialLinearGroup (Fin r) K) := by
            rw [hN]
            exact Subgroup.comap_map_eq_self_of_injective eSL.injective _
  obtain ⟨ℓ, hk, hZ, hUcard, hQ⟩ :=
    exists_levels_of_radical (K := K) (ι := Fin r) (G := StatedProj (StatedSL r K))
      π hπ hker U hU hrad
  refine ⟨levelsCard ℓ, levelCount ℓ, hk, fun i => one_le_levelCount ℓ i, ?_, hZ, ?_, ?_⟩
  · exact (sum_levelCount ℓ).trans (Fintype.card_fin r)
  · simpa only [Fintype.card_fin] using hUcard
  · intro S hSn hS
    obtain ⟨i, h2, hne, Z', hZ', hZn, ⟨e⟩⟩ := hQ S hSn hS
    refine ⟨i, h2, hne, Z', hZ', hZn, ⟨?_⟩⟩
    let e1 : ProjectiveSpecialLinearGroup (Block ℓ (levels ℓ i)) K ≃*
        ProjectiveSpecialLinearGroup (Fin (levelCount ℓ i)) K :=
      Classical.choice (nonempty_projectiveSpecialLinearGroup_equiv (K := K)
        (Fintype.equivFinOfCardEq (card_subtype_eq_levelCount ℓ i)))
    exact e.trans (e1.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      (levelCount ℓ i) K))

end CFSG.LieType.BorelTits.RadicalLinear
