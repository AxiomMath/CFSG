module

public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsFull
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsSectionBoundsGenerators

public section

open scoped IsMulCommutative

namespace CFSG.LargeEvenClassification.Helpers

theorem macwilliams_subgroup_generators
    {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (U : Subgroup S) :
    ∃ X : Finset U, X.card ≤ 4 ∧ Subgroup.closure (X : Set U) = ⊤ := by
  obtain ⟨ambient, hcard, hgenerates⟩ := macwilliams_four_generators hpgroup hnoEight U
  obtain ⟨X, hXcard, hXgenerates⟩ :=
    subgroup_generators_of_ambient_generators U ambient hgenerates
  exact ⟨X, hXcard.le.trans hcard, hXgenerates⟩

theorem macwilliams_elementary_section_card_le_sixteen
    {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (U : Subgroup S) (R : Subgroup U) [R.Normal]
    (hQ : CFSG.IsElementaryAbelian 2 (U ⧸ R)) :
    Nat.card (U ⧸ R) ≤ 16 := by
  obtain ⟨X, hcard, hgenerates⟩ := macwilliams_subgroup_generators hpgroup hnoEight U
  have hbound := elementary_surjection_card_le_pow_generators_of_isElementaryAbelian
    Nat.prime_two hQ (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R) X hgenerates
  exact hbound.trans (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hcard)

theorem macwilliams_elementary_section_card_le_sixteen_of_exponent
    {S : Type*} [Group S] [Finite S] (hpgroup : IsPGroup 2 S)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (U : Subgroup S) (R : Subgroup U) [R.Normal]
    (hcommutative : IsMulCommutative (U ⧸ R))
    (hexponent : ∀ element : U ⧸ R, element ^ 2 = 1) :
    Nat.card (U ⧸ R) ≤ 16 := by
  apply macwilliams_elementary_section_card_le_sixteen hpgroup hnoEight U R
  exact
    { toIsMulCommutative := hcommutative
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hexponent }

theorem macwilliams_elementary_section_card_le_sixteen_of_isElemAbelian
    {S : Type*} [Group S] [Finite S] (hpgroup : IsPGroup 2 S)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (U : Subgroup S) (R : Subgroup U) [R.Normal]
    (hQ : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup (U ⧸ R))) :
    Nat.card (U ⧸ R) ≤ 16 := by
  have hcommutative : IsMulCommutative (U ⧸ R) := by
    apply IsMulCommutative.of_comm
    intro first second
    exact congrArg Subtype.val
      (@mul_comm' (⊤ : Subgroup (U ⧸ R)) _ hQ.1
        ⟨first, Subgroup.mem_top first⟩ ⟨second, Subgroup.mem_top second⟩)
  exact macwilliams_elementary_section_card_le_sixteen_of_exponent hpgroup hnoEight U R
    hcommutative (fun element => hQ.2 element (Subgroup.mem_top element))

theorem macwilliams_elementary_section_finrank_le_four
    {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (U : Subgroup S) (R : Subgroup U) [R.Normal]
    (hQ : CFSG.IsElementaryAbelian 2 (U ⧸ R)) :
    let _ : CFSG.IsElementaryAbelian 2 (U ⧸ R) := hQ
    Module.finrank (ZMod 2) (Additive (U ⧸ R)) ≤ 4 := by
  let : CFSG.IsElementaryAbelian 2 (U ⧸ R) := hQ
  obtain ⟨X, hcard, hgenerates⟩ := macwilliams_subgroup_generators hpgroup hnoEight U
  exact (quotient_frattini_dimension_le_generators (prime := 2)
    (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R) X hgenerates).trans hcard

theorem macwilliams_section_group_rank_le_four
    {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (U : Subgroup S) (R : Subgroup U) [R.Normal] :
    Group.rank (U ⧸ R) ≤ 4 := by
  obtain ⟨X, hcard, hgenerates⟩ := macwilliams_subgroup_generators hpgroup hnoEight U
  exact (Group.rank_le_of_surjective (QuotientGroup.mk' R)
    (QuotientGroup.mk'_surjective R)).trans ((Group.rank_le hgenerates).trans hcard)

theorem macwilliams_section_pGeneratorRank_le_four
    {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (U : Subgroup S) (R : Subgroup U) [R.Normal] :
    pGeneratorRank 2 (U ⧸ R) ≤ 4 := by
  classical
  obtain ⟨X, hcard, hgenerates⟩ := macwilliams_subgroup_generators hpgroup hnoEight U
  let quotient := QuotientGroup.mk' R
  let images := X.image quotient
  have himages : Subgroup.closure (images : Set (U ⧸ R)) = ⊤ := by
    rw [Finset.coe_image, ← MonoidHom.map_closure, hgenerates]
    exact Subgroup.map_top_of_surjective quotient (QuotientGroup.mk'_surjective R)
  exact (pGeneratorRank_le_generators Nat.prime_two
    ((hpgroup.to_subgroup U).to_quotient R) images himages).trans
      (Finset.card_image_le.trans hcard)

end CFSG.LargeEvenClassification.Helpers
