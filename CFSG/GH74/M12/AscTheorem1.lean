module

public import CFSG.GH74.M12.T1A8
public import CFSG.GH74.M12.T1NonSimple
public import CFSG.GH74.M12.AscFinal

public section

namespace CFSG.GH74.M12

theorem s_asc03_theorem1 :
    S_Asc03_Theorem1 := by
  intro G _ _ z hyp
  by_cases hs : IsSimpleGroup G
  · obtain ⟨y, hyH, hy3⟩ := Thm1.exists_order_three hyp
    obtain ⟨K₁, K₂, hd⟩ := Thm1.exists_q8Data hyp hyH hy3
    by_cases hM : ∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))),
        K.Normal
    · exact Or.inr (Or.inr ⟨s_asc03_simple G hs z hyp hM, Thm1.all_normal_of_exists hyp hd hM⟩)
    · have := hs
      exact Or.inr (Or.inl ⟨Thm1.a8_case hyp hM, fun K hK hKn => hM ⟨K, hK, hKn⟩⟩)
  · exact Or.inl (Thm1.nonsimple_conclusion hyp hs)

end CFSG.GH74.M12
