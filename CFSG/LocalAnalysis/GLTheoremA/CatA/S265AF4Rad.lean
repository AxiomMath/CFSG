module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsParabolic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.StandardType.TableBF4TwoInputs

private theorem parabolicRadicalRoots_coe (s : Finset (Fin Tag.F4.rank)) :
    parabolicRadicalRoots Tag.F4 (s : Set (Fin Tag.F4.rank)) =
      {α | IsRoot Tag.F4 α ∧ (0 < height α ∧ ∃ j, j ∉ s ∧ α j ≠ 0)} := by
  ext α
  simp only [parabolicRadicalRoots, parabolicPosRoots, parabolicRoots, Set.mem_diff,
    Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_coe]
  constructor
  · rintro ⟨⟨hr, hh⟩, hn⟩
    refine ⟨hr, hh, ?_⟩
    by_contra hc
    push Not at hc
    exact hn ⟨⟨hr, hc⟩, hr, hh⟩
  · rintro ⟨hr, hh, j, hj, hα⟩
    exact ⟨⟨hr, hh⟩, fun h => hα (h.1.2 j hj)⟩

section Roots


private theorem ncard_radicalRoots_coatom {i : Fin Tag.F4.rank} (hi : i.val = 0 ∨ i.val = 3) :
    (parabolicRadicalRoots Tag.F4
      (maskSet .F4 (f4CoatomMask i) : Set (Fin Tag.F4.rank))).ncard = 15 := by
  rcases hi with h | h
  · obtain rfl : i = ⟨0, by decide⟩ := Fin.ext h
    rw [parabolicRadicalRoots_coe, ncard_setOf_isRoot_and]
    decide +kernel
  · obtain rfl : i = ⟨3, by decide⟩ := Fin.ext h
    rw [parabolicRadicalRoots_coe, ncard_setOf_isRoot_and]
    decide +kernel

end Roots

section Radical


theorem exists_radical_of_normalizes_F4two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {V A : Subgroup (adjointGroup Tag.F4 K)} (hV : V ≠ ⊥)
    (hV2 : IsPGroup 2 V) (hAV : A ≤ Subgroup.normalizer (V : Set (adjointGroup Tag.F4 K)))
    (h27 : 27 ∣ Nat.card A) :
    ∃ R : Subgroup (adjointGroup Tag.F4 K), Nat.card R = 2 ^ 15 ∧
      A ≤ Subgroup.normalizer (R : Set (adjointGroup Tag.F4 K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨J, g, hJ, hmem⟩ := exists_conj_mem_parabolic_of_normalizes hV hV2 hAV
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  obtain ⟨M, hM⟩ : ∃ M : Set (Fin Tag.F4.rank),
      M = (maskSet .F4 (f4CoatomMask i) : Set (Fin Tag.F4.rank)) := ⟨_, rfl⟩
  have hJM : parabolicSubgroup .F4 K J ≤ parabolicSubgroup .F4 K M :=
    ((standard_parabolic_cells .F4 K).2.2.2.1 J M).2 fun k hk => by
      rw [hM]
      exact_mod_cast f4CoatomMask_cover i k fun h => hi (h ▸ hk)
  have hAM : ∀ a ∈ A, ((g⁻¹ * a * g : adjointGroup Tag.F4 K) : ModGL .F4 K) ∈
      parabolicSubgroup .F4 K M := fun a ha => hJM (hmem a ha)
  have hi03 : i.val = 0 ∨ i.val = 3 := by
    by_contra hne
    have hi4 := i.2
    change i.val < 4 at hi4
    refine not_dvd_card_parabolic hK (i := i) (by omega) ?_
    rw [← hM, show (3 : ℕ) ^ 3 = 27 by norm_num]
    refine h27.trans ?_
    have hle : (A.map (MulAut.conj g⁻¹).toMonoidHom).map (adjointGroup .F4 K).subtype ≤
        parabolicSubgroup .F4 K M := by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      simpa [MulAut.conj_apply] using hAM a ha
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (adjointGroup .F4 K).subtype_injective,
      Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective] at hdvd
  have hQC : parabolicRadical .F4 K M ≤ adjointGroup .F4 K :=
    ((parabolicRadical_le_posUnipotent M).trans (posUnipotent_le_parabolicSubgroup M)).trans
      (parabolicSubgroup_le_adjointGroup .F4 K M)
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : Subgroup (adjointGroup Tag.F4 K),
      R₀ = (parabolicRadical .F4 K M).comap (adjointGroup .F4 K).subtype := ⟨_, rfl⟩
  have hmap : R₀.map (adjointGroup .F4 K).subtype = parabolicRadical .F4 K M := by
    rw [hR₀]
    exact Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
  have hcard : Nat.card R₀ = 2 ^ 15 := by
    rw [← Subgroup.card_map_of_injective (adjointGroup .F4 K).subtype_injective, hmap,
      card_parabolicRadical, hK, hM, ncard_radicalRoots_coatom hi03]
  have hN : A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.normalizer (R₀ : Set (adjointGroup Tag.F4 K)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hR₀]
    refine Subgroup.le_normalizer_comap _ ?_
    rw [Subgroup.mem_comap]
    exact parabolicSubgroup_le_normalizer_parabolicRadical M
      (by simpa [MulAut.conj_apply] using hAM a ha)
  refine ⟨R₀.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hcard]
  · rw [← Subgroup.map_equiv_normalizer_eq]
    intro a ha
    refine ⟨g⁻¹ * a * g, hN ⟨a, ha, ?_⟩, ?_⟩ <;> simp [MulAut.conj_apply, mul_assoc]

end Radical

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
