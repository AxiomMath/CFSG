module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.Char3
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns CFSG.RankThree.PartTwo.KFacts

theorem excres_false_of_char3_of_index (hKD : KDCharP 3) {P : Type} [Group P] [Finite P]
    {x : P} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) {J : Subgroup P}
    (hJ : GLAPComponent 3 (fixSub (MulAut.conj x)) J) (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1.characteristic = 3) (e : P ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv P e.toEquiv
  have hord : orderOf (e x) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hx3 hx1
  have hker : (e : P →* (TauCeti.CFSGIndex.lie d).Group).ker ≤ Subgroup.center P := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  have hcomm : ∀ y : P, (e : P →* (TauCeti.CFSGIndex.lie d).Group) (MulAut.conj x y) =
      (MulAut.conj (e x) : MulAut (TauCeti.CFSGIndex.lie d).Group)
        ((e : P →* (TauCeti.CFSGIndex.lie d).Group) y) := fun y => by
    simp [MulAut.conj_apply]
  have hcomp := glaPComponent_map_fixSubgroup (e : P →* (TauCeti.CFSGIndex.lie d).Group) hker
    (MulAut.conj x) (MulAut.conj (e x)) hcomm e.surjective Nat.prime_three hJ
  rw [t6char3_fixSubgroup_conj_eq_centralizer] at hcomp
  have hle : J.map (e : P →* (TauCeti.CFSGIndex.lie d).Group) ≤
      GLAPLayer 3 (Subgroup.centralizer ({e x} : Set (TauCeti.CFSGIndex.lie d).Group)) :=
    le_sSup hcomp
  rw [hKD d hd (e x) hord, le_bot_iff] at hle
  exact glaPComponent_ne_bot' hJ
    ((Subgroup.map_eq_bot_iff_of_injective J
      (f := (e : P →* (TauCeti.CFSGIndex.lie d).Group)) e.injective).1 hle)

theorem excres_false_of_char3 (hKD : KDCharP 3) (hB : CFSG.TauCetiBridge.TypewiseBridges)
    {P : Type} [Group P] [Finite P] {t : StatedLieTag} {n f : ℕ}
    (hdup : ¬ TauCetiDuplicate t n 3 f) (hm : CFSG.Blueprint.LieModel P t n 3 f)
    {x : P} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) {J : Subgroup P}
    (hJ : GLAPComponent 3 (fixSub (MulAut.conj x)) J) : False := by
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_tauCeti_index_of_blueprint_lieModel_odd hB hm (by norm_num) hdup
  exact excres_false_of_char3_of_index hKD hx1 hx3 hJ d hd e

theorem excres_not_tauCetiDuplicate {t : StatedLieTag} (ht : t ≠ .PSL ∧ t ≠ .PSp) (n p f : ℕ) :
    ¬ TauCetiDuplicate t n p f := by
  unfold TauCetiDuplicate
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact ht.1 h
  · exact ht.2 h

end CFSG.HardMathSupport.Dickson.Sec6.I1431
