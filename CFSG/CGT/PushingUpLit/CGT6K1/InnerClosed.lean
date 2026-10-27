module

public import CFSG.CGT.PushingUpLit.CGT6K1.Defs
public import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
public import CFSG.CGT.PushingUpLit.CGT6K1.InnerG2

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.EvenBN.GMSK
  CFSG.CGT.PushingUpLit.CGT6

theorem evenLieType_of_classical {D : Type} [Group D] {t : StatedLieTag} {n f : ℕ}
    (ht : t ∈ classicalTags) (h : LieModel D t n 2 f) : EvenLieType D := by
  have hadm : StatedLieAdmissible t n 2 f := by
    rcases h with ⟨-, hadm, -⟩ | ⟨-, h', -⟩ | ⟨-, h', -⟩ | ⟨-, rfl, -⟩
    · exact hadm
    · exact absurd h' (by revert ht; cases t <;> decide)
    · exact absurd h' (by revert ht; cases t <;> decide)
    · exact absurd ht (by decide)
  exact ⟨t, n, f, hadm, h⟩

theorem gmsVList_of_survivors_two {D : Type} [Group D]
    (h : NativeSporadic.IsSporadic D .J1 ∨ NativeSporadic.IsSporadic D .M12 ∨
      Nonempty (D ≃* alternatingGroup (Fin 7)) ∨ LieModel D .PSL 2 5 2 ∨
      LieModel D .PSL 3 5 1 ∨ LieModel D .PSU 3 5 1) : GMSVList D := by
  rcases h with h | h | h | h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))

theorem innerSurvivorsInV_holds :
    InnerSurvivorsInV := by
  intro D _ _ hDs n K _ _ α S hdat hin hsurv
  rcases hsurv with h | h | h | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact (even_lie_type_no_inner_datum hDs (evenLieType_of_classical (by decide) h)
      hdat.two_le K hdat.card_eq α hdat.orderOf_eq hin S hdat.le_fixed hdat.normal
      hdat.nonempty_mulEquiv).elim
  · exact (even_lie_type_no_inner_datum hDs (evenLieType_of_classical (by decide) h)
      hdat.two_le K hdat.card_eq α hdat.orderOf_eq hin S hdat.le_fixed hdat.normal
      hdat.nonempty_mulEquiv).elim
  · exact (even_lie_type_no_inner_datum hDs (evenLieType_of_classical (by decide) h)
      hdat.two_le K hdat.card_eq α hdat.orderOf_eq hin S hdat.le_fixed hdat.normal
      hdat.nonempty_mulEquiv).elim
  · exact ⟨rfl, gmsVList_of_survivors_two h⟩
  · exact (inner_G2_fixed_root_exclusion h (by norm_num) hdat.two_le K hdat.card_eq α
      hdat.orderOf_eq hin S hdat.le_fixed hdat.normal hdat.nonempty_mulEquiv).elim

end CFSG.CGT.PushingUpLit.CGT6K1
