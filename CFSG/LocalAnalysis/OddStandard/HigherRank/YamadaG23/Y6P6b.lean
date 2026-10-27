module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem y6_perm6_aut : ∃ ι : Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6)),
    Function.Injective ι ∧
      ∀ a : alternatingGroup (Fin 6), ι (a : Equiv.Perm (Fin 6)) = MulAut.conj a :=
  ⟨MulAut.conjNormal,
    CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num),
    fun _ => MulAut.conjNormal_val⟩

theorem y6_sub_to_autA6 {H : Subgroup (Equiv.Perm (Fin 6))} (hA : alternatingGroup (Fin 6) ≤ H) :
    ∃ X : Subgroup (MulAut (alternatingGroup (Fin 6))),
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ≤ X ∧
        Nonempty (↥H ≃* ↥X) := by
  obtain ⟨ι, hι, hconj⟩ := y6_perm6_aut
  refine ⟨H.map ι, ?_, ⟨Subgroup.equivMapOfInjective H ι hι⟩⟩
  rintro _ ⟨a, rfl⟩
  exact ⟨(a : Equiv.Perm (Fin 6)), hA a.2, hconj a⟩

end CFSG.OddStandard.HigherRank.YamadaG23
