module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AIvDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp8
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClWit
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AHr
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AIvTop
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AOm8
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AOm10
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQSSp6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA TauCeti S265

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem p_eq_two_of_card_eq_two {q : PrimePower} (h : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 :=
  (Nat.Prime.pow_eq_iff Nat.prime_two).1 (by rw [← PrimePower.card_def]; exact h)

private theorem catalogIs_tyA {G : Type} [Group G] (h : catalogIs G tyA) :
    catalogIs G S9.isD4two ∨ catalogIs G tyOm10m ∨ catalogIs G S9.isSp6two ∨
      catalogIs G tySp8 ∨ catalogIs G tyAlt6 := by
  obtain ⟨i, hi | hi | hi | hi | hi, f⟩ := h
  · exact Or.inl ⟨i, hi, f⟩
  · exact Or.inr (Or.inl ⟨i, hi, f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, f⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, f⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, f⟩)))

private theorem isA6_of_tyAlt6 (i : CFSGIndex) (hi : tyAlt6 i) : S10.isA6 i := by
  cases i <;> try exact hi.elim
  rename_i n hn
  rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> first | exact hi.elim | rfl

omit [Finite Ω] in
private theorem three_dvd_card_of_subgroup {K : Subgroup Ω} (E : Subgroup (PSimple 3 K))
    (hE : 3 ∣ Nat.card E) : 3 ∣ Nat.card ↥K :=
  (hE.trans (Subgroup.card_subgroup_dvd_card E)).trans
    ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))

private theorem three_dvd_card_of_d4two {K : Subgroup Ω}
    (hJ : catalogIs (PSimple 3 K) S9.isD4two) : 3 ∣ Nat.card ↥K := by
  obtain ⟨E, -, -, hEc, -⟩ := D4XF.d4two_rank3 hJ
  exact three_dvd_card_of_subgroup E (by rw [hEc]; norm_num)

omit [Finite Ω] in
private theorem three_dvd_card_of_om10m {K : Subgroup Ω}
    (hJ : catalogIs (PSimple 3 K) tyOm10m) : 3 ∣ Nat.card ↥K := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ : ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedD 5 q).Valid),
      q.card = 2 ∧ Nonempty (PSimple 3 K ≃* ValidLieTypeIndex.Group ⟨.twistedD 5 q, hv⟩) := by
    obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex hJ
    cases d with
    | twistedD r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact ⟨q, hv, hP, ⟨e⟩⟩
      · exact hP.elim
    | _ => exact hP.elim
  obtain ⟨h1, h2⟩ := p_eq_two_of_card_eq_two hq
  obtain ⟨-, -, -, E, -, -, hEc⟩ :=
    I1431C2.Local81.congr e.symm (I1431C2.local81_twistedD 5 q hv h1 h2 le_rfl)
  exact three_dvd_card_of_subgroup E (by rw [hEc]; norm_num)


theorem qsFamA_of_parts (hLie : IvLieRow)
    (h3 : ∀ {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω},
      QSNL 3 S B T x D K → catalogIs (PSimple 3 K) S9.isD4two →
      ¬ (∀ e ∈ B, ∀ he : e ∈ Subgroup.normalizer (K : Set Ω),
        chevAut 3 K ⟨e, he⟩ ∈ D4T.innerAut (PSimple 3 K)) → False) :
    QSFamA := by
  intro p Ω _ _ S B T x D K h hp hcat
  subst hp
  obtain ⟨-, hDe, -, -, -, -, hDK⟩ := h.cfg.std
  have hDJ : D ≤ Subgroup.centralizer (K : Set Ω) := fun d hd => (hDK.le hd).2
  rcases catalogIs_tyA hcat with hJ | hJ | hJ | hJ | hJ
  · exfalso
    have hN := h.nlAct (three_dvd_card_of_d4two hJ)
    by_cases hinn : ∀ e ∈ B, ∀ he : e ∈ Subgroup.normalizer (K : Set Ω),
        chevAut 3 K ⟨e, he⟩ ∈ D4T.innerAut (PSimple 3 K)
    · exact hN.false_of_d4two_inner h.cfg.elem hJ hinn
        ((card_mul_le_rank_d4two hN.comp hDe hDJ hJ).trans h.cfg.rank)
    · exact h3 h hJ hinn
  · exfalso
    have hN := h.nlAct (three_dvd_card_of_om10m hJ)
    have h81 := card_mul_le_rank_om10minus hN.comp hDe hDJ hJ
    have hr := h.cfg.rank
    exact hN.false_of_om10minus h.cfg.elem hJ (by omega)
  · exact (caseIv_false_of_parts hLie ivCoreAt_sp8 ivCoreAt_f4 schurF4_holds h hJ
      (QSNL.card_eq_nine_mul_of_sp6 h hJ) (QSNL.commutator_ne_bot_of_sp6 h hJ)).elim
  · exact qsConcl_of_sp8 h hJ
  · obtain ⟨i, hi, f⟩ := hJ
    exact Or.inr ⟨rfl, Or.inr ⟨i, isA6_of_tyAlt6 i hi, f⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
