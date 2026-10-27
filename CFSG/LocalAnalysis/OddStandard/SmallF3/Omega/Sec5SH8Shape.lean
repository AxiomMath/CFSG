module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8Embed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8Front
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8Q3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8Psl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8PglLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8PglCentral

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5sh8_shape
    {X : Type} [Group X] [Finite X] (hO : CFSG.oddCore X = ⊥) (P : Sylow 2 X)
    (hP : Nonempty (↥P ≃* DihedralGroup 4))
    (hgen : Subgroup.normalClosure ((P : Subgroup X) : Set X) = ⊤) : Sec5SH8Shape P := by
  unfold Sec5SH8Shape
  have hDih := sec5sh8_hasDihedralSylowTwo P hP
  rcases sec5sh8_eq_top_or_not_normalComplement hO P with htop | hNC
  · exact Or.inl htop
  refine Or.inr ?_
  rcases sec5sh8_embed hO hDih hNC P hgen with h7 | ⟨F, _, _, hF, ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩⟩
  · exact Or.inl h7
  · by_cases h3 : Nat.card F = 3
    · exact absurd ⟨e⟩ (sec5sh8_q3_not_psl P hP h3)
    · exact Or.inr (Or.inr ⟨F, inferInstance, inferInstance, ⊤,
        sec5sh8_psl P hF (sec5sh8_five_le_of_ne_three hF h3) e⟩)
  · by_cases h3 : Nat.card F = 3
    · exact Or.inr (Or.inl (sec5sh8_q3_pgl h3 e))
    · obtain ⟨J, hJn, hJi, hJc, hJe⟩ := sec5sh8_pgl_layer hF e
      exact Or.inr (Or.inr ⟨F, inferInstance, inferInstance, J,
        ⟨hF, sec5sh8_five_le_of_ne_three hF h3, hJn, hJe, hJc, Or.inr hJi,
          fun z hz _ hc => sec5sh8_central_mem_of_index_two (P : Subgroup X) hP J hJi z hz hc⟩⟩)

theorem sec5sh8_statement :
    Sec5SH8Statement :=
  fun _ _ _ hO P hP hgen => sec5sh8_shape hO P hP hgen

end CFSG.OddStandard.SmallF3.Omega
