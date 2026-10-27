module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Res
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM10Abs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM10Explicit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM10Griess

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti
  CFSG.QuasithinUnique.SQTK CFSG.LocalAnalysis.GLTheoremA.SFM10

theorem exists_B2_of_isSp4_27 {S : Type} [Group S] (h : catalogIs S isSp4_27) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid), q.card = 27 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | B r q =>
      rcases r with _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      · have hq : q.card = 27 := hi
        exact ⟨q, hv, hq, ⟨e⟩⟩
      · exact hi.elim
    | _ => exact hi.elim

section Main


theorem I1429TwoRankSp4_holds : I1429TwoRankSp4 := by
  intro Q _ _ hQ hcat
  obtain ⟨q, hv, hq27, ⟨e⟩⟩ := exists_B2_of_isSp4_27 hcat
  haveI : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) :=
    finite_validIndex_fixedField _
  have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) = 27 := by
    rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder, LieTypeIndex.fieldOrder_B]
    exact hq27
  let e' : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSp 2 ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)) :=
    e.trans (typeB2GroupEquivStatedProj q hv)
  have hdvd : Nat.card (Subgroup.center Q) ∣ 2 := card_center_dvd_two hQ hK e'
  obtain ⟨t, E, ht2, ht1, hE, hEc, hEt⟩ := exists_involution_and_elemAbelian hK
  let ψ : Q →* StatedProj (StatedSp 2 ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)) :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hψ : Function.Surjective ψ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ x : Q, ψ x = 1 → x ∈ Subgroup.center Q := by
    intro x hx
    have h1 : (QuotientGroup.mk' (Subgroup.center Q) x : Q ⧸ Subgroup.center Q) = 1 := by
      apply e'.injective
      rw [map_one]
      exact hx
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hZ : Nat.Coprime 3 (Nat.card (Subgroup.center Q)) :=
    Nat.Coprime.coprime_dvd_right hdvd (by norm_num)
  exact six_le_glaTwoLocalRank_of_central_extension ψ hψ hker hZ t ht2 ht1 E hE hEc hEt

@[expose] def I1429OuterInner : Prop := I1429SubfieldOut ∧ I1429InnerRest

theorem I1429Residual_of_I1429OuterInner (h : I1429OuterInner) : I1429Residual :=
  ⟨h.1, h.2, I1429TwoRankSp4_holds⟩

end Main

end CFSG.LocalAnalysis.GLTheoremA

end
