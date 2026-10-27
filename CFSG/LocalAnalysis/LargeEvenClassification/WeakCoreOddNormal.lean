module

public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeHyperplaneGeneration
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreTwoSubgroups

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem coprime_plane_centralizers_generate {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (Plane Invariant : Subgroup Ambient)
    (helementary : IsElemAbelian prime Plane) (hcard : Nat.card Plane = prime ^ 2)
    (hnormalizes : Plane ≤ Subgroup.normalizer (Invariant : Set Ambient))
    (hcoprime : ¬prime ∣ Nat.card Invariant) :
    (⨆ involution : {element : Plane // element ≠ 1},
      Invariant ⊓ Subgroup.centralizer {involution.val.val}) = Invariant := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : CommGroup Plane := { (inferInstance : Group Plane) with
    mul_comm := @mul_comm' Plane _ helementary.1 }
  have hstable : ∀ conjugator : Plane, ∀ element : Ambient, element ∈ Invariant →
      conjugator.val * element * conjugator.val⁻¹ ∈ Invariant := by
    intro conjugator element helement
    exact (Subgroup.mem_normalizer_iff.mp (hnormalizes conjugator.property) element).mp helement
  let action := invariantSubgroupConjugation Plane.subtype Invariant hstable
  have hexponent : ∀ element : Plane, element ^ prime = 1 := by
    intro element
    apply Subtype.ext
    exact helementary.2 element element.property
  have hgenerates := coprime_hyperplane_fixed_generation hprime (IsPGroup.of_card hcard)
    hexponent action hcoprime
  let CentralizerSpan := ⨆ element : {element : Plane // element ≠ 1},
    Invariant ⊓ Subgroup.centralizer {element.val.val}
  have hspanLe : hyperplaneFixedSpan prime action ≤ CentralizerSpan.comap Invariant.subtype := by
    apply iSup_le
    intro Fixers
    let MappedFixers := Fixers.val.map Plane.subtype
    have hmappedRank : 1 ≤ pRank prime MappedFixers := by
      have hbound := elementary_hyperplane_rank_lower hprime Plane helementary hcard
        Fixers.val Fixers.property
      change 2 ≤ pRank prime MappedFixers + 1 at hbound
      omega
    have hmappedLe : MappedFixers ≤ Plane := by
      intro element helement
      obtain ⟨source, _, rfl⟩ := helement
      exact source.property
    have hmappedPGroup : IsPGroup prime MappedFixers :=
      ((IsPGroup.of_card hcard).to_subgroup Fixers.val).map Plane.subtype
    have hmappedNe : MappedFixers ≠ ⊥ := by
      intro hzero
      obtain ⟨exponent, hfixerCard⟩ := hmappedPGroup.exists_card_eq
      have hfixerElementary := elementary_subgroup_of_le Plane MappedFixers helementary hmappedLe
      have hrank := elementary_pRank_card hprime.one_lt MappedFixers hfixerElementary hfixerCard
      have hexponentOne : prime ^ exponent = 1 := hfixerCard.symm.trans (Subgroup.card_eq_one.mpr hzero)
      have hexponentZero : exponent = 0 := Nat.pow_eq_one.mp hexponentOne |>.resolve_left hprime.ne_one
      rw [hrank, hexponentZero] at hmappedRank
      omega
    obtain ⟨fixer, hfixer, hfixerNe⟩ := (Subgroup.bot_or_exists_ne_one MappedFixers).resolve_left hmappedNe
    obtain ⟨source, hsource, hsourceEq⟩ := hfixer
    have hsourceNe : source ≠ 1 := by
      intro hone
      apply hfixerNe
      rw [hone] at hsourceEq
      exact hsourceEq.symm
    have hfixedLe : Invariant ⊓ Subgroup.centralizer {source.val} ≤ CentralizerSpan :=
      le_iSup_of_le ⟨source, hsourceNe⟩ le_rfl
    intro element helement
    apply hfixedLe
    refine ⟨element.property, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hfixed := congrArg (fun entry : Invariant => entry.val) (helement ⟨source, hsource⟩)
    change source.val * element.val * source.val⁻¹ = element.val at hfixed
    exact ((mul_inv_eq_iff_eq_mul).mp hfixed).symm
  apply le_antisymm (iSup_le fun _ => inf_le_left)
  intro element helement
  exact hspanLe (hgenerates.symm ▸ (show (⟨element, helement⟩ : Invariant) ∈ (⊤ : Subgroup Invariant)
    from Subgroup.mem_top _))

end CFSG.LargeEvenClassification.Helpers
