module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PolynomialCoefficients
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Spectral

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem idempotentCoeff_central (m : Ideal BlocksAlgInt) (G : Type)
    [Group G] [Finite G] {characters : Set (G → ℂ)}
    (hcharacters : BlocksAdmissible m G characters) :
    BlocksIsCentralR m (BlocksIdempotentCoeff G characters) :=
  ⟨hcharacters.2, idempotentCoeff_conj hcharacters.1⟩

theorem admissible_irr (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] : BlocksAdmissible m G (BlocksIrr G) := by
  classical
  refine ⟨Set.Subset.rfl, ?_⟩
  have hequal : BlocksIdempotentCoeff G (BlocksIrr G) = identityCoefficients := by
    apply sub_eq_zero.mp
    apply centralChar_separates G
    · intro element conjugator
      simp only [Pi.sub_apply, idempotentCoeff_conj Set.Subset.rfl,
        (identityCoefficients_central m hm).2 element conjugator]
    · intro character hcharacter
      rw [centralChar_sub, centralChar_idempotentCoeff Set.Subset.rfl hcharacter,
        centralChar_identityCoefficients hcharacter, ite_eq_left hcharacter, sub_self]
  intro element
  rw [hequal]
  exact (identityCoefficients_central m hm).1 element

theorem admissible_inter (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {left right : Set (G → ℂ)}
    (hleft : BlocksAdmissible m G left) (hright : BlocksAdmissible m G right) :
    BlocksAdmissible m G (left ∩ right) := by
  classical
  have hsubset : left ∩ right ⊆ BlocksIrr G := fun _ hmember => hleft.1 hmember.1
  have hequal : BlocksIdempotentCoeff G (left ∩ right) =
      coefficientConvolution (BlocksIdempotentCoeff G left) (BlocksIdempotentCoeff G right) := by
    apply sub_eq_zero.mp
    apply centralChar_separates G
    · intro element conjugator
      simp only [Pi.sub_apply, idempotentCoeff_conj hsubset,
        (coefficientConvolution_central m hm (idempotentCoeff_central m G hleft)
          (idempotentCoeff_central m G hright)).2 element conjugator]
    · intro character hcharacter
      rw [centralChar_sub, centralChar_convolution hcharacter _ _
        (idempotentCoeff_central m G hleft).2 (idempotentCoeff_central m G hright).2,
        centralChar_idempotentCoeff hsubset hcharacter,
        centralChar_idempotentCoeff hleft.1 hcharacter,
        centralChar_idempotentCoeff hright.1 hcharacter]
      by_cases hleftMember : character ∈ left <;>
        by_cases hrightMember : character ∈ right <;>
        simp [hleftMember, hrightMember]
  refine ⟨hsubset, ?_⟩
  intro element
  rw [hequal]
  exact (coefficientConvolution_central m hm (idempotentCoeff_central m G hleft)
    (idempotentCoeff_central m G hright)).1 element

theorem admissible_diff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {left right : Set (G → ℂ)}
    (hleft : BlocksAdmissible m G left) (hright : BlocksAdmissible m G right) :
    BlocksAdmissible m G (left \ right) := by
  classical
  have hsubset : left \ right ⊆ BlocksIrr G := fun _ hmember => hleft.1 hmember.1
  have hinter := admissible_inter m hm G hleft hright
  have hequal : BlocksIdempotentCoeff G (left \ right) =
      BlocksIdempotentCoeff G left - BlocksIdempotentCoeff G (left ∩ right) := by
    apply sub_eq_zero.mp
    apply centralChar_separates G
    · intro element conjugator
      simp only [Pi.sub_apply, idempotentCoeff_conj hsubset,
        idempotentCoeff_conj hleft.1, idempotentCoeff_conj hinter.1]
    · intro character hcharacter
      rw [centralChar_sub, centralChar_sub,
        centralChar_idempotentCoeff hsubset hcharacter,
        centralChar_idempotentCoeff hleft.1 hcharacter,
        centralChar_idempotentCoeff hinter.1 hcharacter]
      by_cases hleftMember : character ∈ left <;>
        by_cases hrightMember : character ∈ right <;>
        simp [hleftMember, hrightMember]
  refine ⟨hsubset, ?_⟩
  intro element
  rw [hequal, Pi.sub_apply]
  exact localRing_sub m hm (hleft.2 element) (hinter.2 element)

theorem admissible_finite_inter (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] (family : Set (Set (G → ℂ)))
    (hfinite : family.Finite) (hadmissible : ∀ characters ∈ family,
      BlocksAdmissible m G characters) :
    BlocksAdmissible m G (BlocksIrr G ∩ ⋂₀ family) := by
  induction family, hfinite using Set.Finite.induction_on with
  | empty => simpa only [Set.sInter_empty, Set.inter_univ] using admissible_irr m hm G
  | @insert characters family hnotMember hfinite hinduction =>
      have hcharacters := hadmissible characters (Set.mem_insert characters family)
      have hfamily := hinduction (fun other hother =>
        hadmissible other (Set.mem_insert_of_mem characters hother))
      convert admissible_inter m hm G hcharacters hfamily using 1
      ext character
      simp only [Set.sInter_insert, Set.mem_inter_iff]
      tauto

theorem blockOf_admissible (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {character : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) :
    BlocksAdmissible m G (BlocksBlockOf m G character) := by
  classical
  let family : Set (Set (G → ℂ)) := {characters |
    BlocksAdmissible m G characters ∧ character ∈ characters}
  have hfinite : family.Finite := (irr_finite G).powerset.subset
    (fun _ hmember => Set.mem_powerset hmember.1.1)
  have hfamily := admissible_finite_inter m hm G family hfinite (fun _ hmember => hmember.1)
  have hequal : BlocksBlockOf m G character = BlocksIrr G ∩ ⋂₀ family := by
    ext candidate
    constructor
    · intro hmember
      refine ⟨hmember.1, Set.mem_sInter.mpr ?_⟩
      intro characters hcharacters
      exact (hmember.2 characters hcharacters.1).mp hcharacters.2
    · rintro ⟨hcandidate, hmember⟩
      refine ⟨hcandidate, ?_⟩
      intro characters hcharacters
      constructor
      · intro hcharacterMember
        exact Set.mem_sInter.mp hmember characters ⟨hcharacters, hcharacterMember⟩
      · intro hcandidateMember
        by_contra hcharacterNonmember
        have hcomplement := admissible_diff m hm G (admissible_irr m hm G) hcharacters
        have hcandidateComplement := Set.mem_sInter.mp hmember (BlocksIrr G \ characters)
          ⟨hcomplement, hcharacter, hcharacterNonmember⟩
        exact hcandidateComplement.2 hcandidateMember
  rw [hequal]
  exact hfamily

theorem block_admissible (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {block : Set (G → ℂ)}
    (hblock : BlocksIsBlock m G block) : BlocksAdmissible m G block := by
  obtain ⟨character, hcharacter, rfl⟩ := hblock
  exact blockOf_admissible m hm G hcharacter

end CFSG.BrauerThirdMainTheorem.Helpers
