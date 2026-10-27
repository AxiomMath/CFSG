module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section Pure

private theorem s265e_k2Lie_five {d : TauCeti.LieTypeIndex} (h : k2Lie 5 d) :
    d = .tits ∨ d = .reeF4 2 ∨ d = .suzuki 2 := by
  unfold k2Lie at h
  split at h <;> simp_all

private theorem s265e_card_alt_le {S : Type} [Group S] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : S ≃* alternatingGroup (Fin n)) : Nat.card S ≤ 20160 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  rcases hn with rfl | rfl | rfl <;>
    · rw [card_alternatingGroup, Fintype.card_fin]
      norm_num [Nat.factorial]

private theorem s265e_lie_of_card {Q : Type} [Group Q] {d : TauCeti.LieTypeIndex}
    {i : TauCeti.CFSGIndex} (φ : Q ≃* i.Group) (hrel : KD264Lie.compRelC d i)
    (hbig : 20160 < Nat.card Q) :
    ∃ e : TauCeti.ValidLieTypeIndex, Nonempty (Q ≃* e.Group) ∧ KD264Lie.compRel d e.1 := by
  cases i with
  | cyclic _ _ => exact hrel.elim
  | sporadic _ => exact hrel.elim
  | alternating n hn =>
    exfalso
    have := s265e_card_alt_le (KD264Lie.compRelC_alternating hrel).1 φ
    omega
  | lie e => exact ⟨e, ⟨φ⟩, hrel⟩

end Pure

section Models


private theorem s265e_sz_index {Q : Type} [Group Q] (hQ : LieModel Q .twistedB2 0 2 5)
    (e : TauCeti.ValidLieTypeIndex) (φ : Q ≃* e.Group) : e.1 = .suzuki 2 := by
  obtain ⟨t, n, r, f, hadm, hM, -, -, hSz⟩ :=
    CFSG.RankThree.PartOne.CTP.seitzBridge Q e.1 ⟨e.2, ⟨φ⟩⟩
  by_cases hr : r = 2
  · subst hr
    obtain ⟨ht, hn, hf⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.szEvenTypeDet Q 5 t n f hQ hadm hM
    exact hSz ⟨ht, hn, rfl, hf⟩
  · exact (CFSG.LocalAnalysis.EvenBN.GMSK.szNotOddLie hQ ⟨t, n, r, f, hadm.1, hr, hadm, hM⟩).elim

private theorem s265e_tits_index {Q : Type} [Group Q] (hQ : LieModel Q .Tits 0 2 1)
    (e : TauCeti.ValidLieTypeIndex) (φ : Q ≃* e.Group) : e.1 = .tits := by
  obtain ⟨t, n, r, f, hadm, hM, -, hT, -⟩ :=
    CFSG.RankThree.PartOne.CTP.seitzBridge Q e.1 ⟨e.2, ⟨φ⟩⟩
  by_cases hr : r = 2
  · subst hr
    by_cases ht : t = .Tits
    · subst ht
      obtain ⟨-, -, hn, -, hf⟩ := hadm
      exact hT ⟨rfl, hn, rfl, hf⟩
    · exact absurd ((CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM).symm.trans
        (CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hQ))
        (CFSG.LocalAnalysis.GLTheoremA.MI.evenLieOrder_ne_ordTits hadm ht)
  · rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hQ
        ⟨t, n, r, f, hadm.1, hr, hadm, hM⟩ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)

private theorem s265e_sz_d {Q : Type} [Group Q] (hQ : LieModel Q .twistedB2 0 2 5)
    {d : TauCeti.ValidLieTypeIndex} {i : TauCeti.CFSGIndex} (φ : Q ≃* i.Group)
    (hrel : KD264Lie.compRelC d.1 i) : d.1 = .tits ∨ d.1 = .reeF4 2 ∨ d.1 = .suzuki 2 := by
  have hbig : 20160 < Nat.card Q := by
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hQ]
    norm_num [CFSG.SeitzReduction.F4Pilot.evenLieOrder, ordSuzuki]
  obtain ⟨e, ⟨ψ⟩, hrel'⟩ := s265e_lie_of_card φ hrel hbig
  exact s265e_k2Lie_five (KD264Lie.k2Lie_five_of_compRel d hrel' (Or.inl (s265e_sz_index hQ e ψ)))

private theorem s265e_tits_d {Q : Type} [Group Q] (hQ : LieModel Q .Tits 0 2 1)
    {d : TauCeti.ValidLieTypeIndex} {i : TauCeti.CFSGIndex} (φ : Q ≃* i.Group)
    (hrel : KD264Lie.compRelC d.1 i) : d.1 = .tits := by
  have hbig : 20160 < Nat.card Q := by
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hQ]
    show 20160 < ordTits
    norm_num [ordTits]
  obtain ⟨e, ⟨ψ⟩, hrel'⟩ := s265e_lie_of_card φ hrel hbig
  have he := s265e_tits_index hQ e ψ
  rcases s265e_k2Lie_five
    (KD264Lie.k2Lie_five_of_compRel d hrel' (Or.inr he)) with h | h | h
  · exact h
  all_goals
    exfalso
    rw [he] at hrel'
    rcases hrel' with ⟨-, ⟨j, hj, hfs⟩, -⟩ | ⟨-, hcase⟩ | ⟨-, q, hq, -⟩
    · rw [h] at hfs
      have h32 : 32 ≤ 32 ^ j := Nat.le_self_pow (by omega) 32
      norm_num [KD264Lie.fieldSize] at hfs
      omega
    · rcases hcase with ⟨q, hq, -⟩ | ⟨q, hq, -⟩ <;> cases hq
    · cases hq

end Models

section Ident


private theorem s265e_compIdx {X : Type} [Group X] (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (e : X ≃* d.Group) {β : MulAut X} (hβ : β ∈ innAutDerived X)
    (hβp : β ^ 5 = 1) (hβ1 : β ≠ 1) {J : Subgroup X} (hJ : IsComponentOf J (fixSubgroup β)) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧
      KD264Lie.compRelC d.1 i :=
  KD264Lie.compIdxAt_of_mulEquiv e.symm
    (KD264Lie.lieCompIdx_all d 5 Nat.prime_five (by norm_num) (by rw [hd]; norm_num) trivial)
    β hβ hβp hβ1 J hJ

theorem s265e_ident_sz {X : Type} [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (e : X ≃* d.Group) {β : MulAut X} (hβ : β ∈ innAutDerived X)
    (hβp : β ^ 5 = 1) (hβ1 : β ≠ 1) {J : Subgroup X} (hJ : IsComponentOf J (fixSubgroup β))
    (hQ : LieModel (↥J ⧸ Subgroup.center ↥J) .twistedB2 0 2 5) :
    SuzukiModel X 2 5 ∨ ReeTitsModel X .twistedF4 2 5 ∨ ReeTitsModel X .Tits 2 1 := by
  obtain ⟨i, ⟨φ⟩, hrel⟩ := s265e_compIdx d hd e hβ hβp hβ1 hJ
  have hcases := s265e_sz_d hQ φ hrel
  obtain ⟨d1, hv⟩ := d
  rcases hcases with (h | h | h) <;> change d1 = _ at h <;> subst h
  · exact Or.inr (Or.inr (CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e))
  · exact Or.inr (Or.inl (CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 2 hv e))
  · exact Or.inl (CFSG.StandardType.ChevTwo.suzukiModel_of_valid 2 hv e)

theorem s265e_ident_tits {X : Type} [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (e : X ≃* d.Group) {β : MulAut X} (hβ : β ∈ innAutDerived X)
    (hβp : β ^ 5 = 1) (hβ1 : β ≠ 1) {J : Subgroup X} (hJ : IsComponentOf J (fixSubgroup β))
    (hQ : LieModel (↥J ⧸ Subgroup.center ↥J) .Tits 0 2 1) :
    ReeTitsModel X .Tits 2 1 := by
  obtain ⟨i, ⟨φ⟩, hrel⟩ := s265e_compIdx d hd e hβ hβp hβ1 hJ
  have hd1 := s265e_tits_d hQ φ hrel
  obtain ⟨d1, hv⟩ := d
  change d1 = _ at hd1
  subst hd1
  exact CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e

end Ident

end CFSG.LocalAnalysis.GLTheoremA.S265

end
