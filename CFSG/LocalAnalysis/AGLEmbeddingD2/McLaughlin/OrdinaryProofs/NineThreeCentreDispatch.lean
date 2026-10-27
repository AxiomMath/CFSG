module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.AlternatingNineFree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CentreNineFree
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRankAut

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.AGLEmbedding

theorem card_center_eq_one_of_perfect_of_solvable_quot {Q S : Type} [Group Q] [Finite Q] [Group S]
    [Group.IsSolvable S] (hQ : Group.IsPerfect Q) (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) = 1 := by
  have : Group.IsSolvable (Q ⧸ Subgroup.center Q) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center Q))
      (QuotientGroup.mk'_surjective _)
  have hsub : Subsingleton (Q ⧸ Subgroup.center Q) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (G := Q ⧸ Subgroup.center Q) inferInstance
  have htop : Subgroup.center Q = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have := hsub.elim (QuotientGroup.mk x : Q ⧸ Subgroup.center Q) (QuotientGroup.mk 1)
    simpa using QuotientGroup.eq.mp this
  have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
    (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm
  have hQsol : Group.IsSolvable Q := Group.isSolvable_of_comm hcomm
  have hQsub : Subsingleton Q := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (G := Q) inferInstance
  rw [htop]
  simp

theorem card_center_eq_one_of_perfect_of_solvable {Q : Type} [Group Q] [Finite Q]
    [Group.IsSolvable Q] (hQ : Group.IsPerfect Q) : Nat.card (Subgroup.center Q) = 1 := by
  have hQsub : Subsingleton Q := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (G := Q) inferInstance
  simp

theorem not_nine_dvd_card_center_of_quot_alternating
    {Q : Type} [Group Q] [Finite Q] {m : ℕ} (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin m)) :
    ¬ 9 ∣ Nat.card (Subgroup.center Q) := by
  by_cases hm : 5 ≤ m
  · exact not_nine_dvd_card_center_of_griess hQ e
      (not_nine_dvd_card_griessHopfMultiplier_of_mulEquiv_alternating hm (MulEquiv.refl _))
  · rw [not_le] at hm
    have : Group.IsSolvable (alternatingGroup (Fin m)) :=
      alternatingGroup.isSolvable (by simp; omega)
    rw [card_center_eq_one_of_perfect_of_solvable_quot hQ e]
    norm_num

theorem card_center_eq_one_of_perfect_alternating {Q : Type} [Group Q] [Finite Q] {m : ℕ}
    (hQ : Group.IsPerfect Q) (e : Q ≃* alternatingGroup (Fin m)) :
    Nat.card (Subgroup.center Q) = 1 := by
  by_cases hm : 4 ≤ m
  · have hbot : Subgroup.center Q = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      apply e.injective
      rw [map_one]
      have hc : e z ∈ Subgroup.center (alternatingGroup (Fin m)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := e.surjective g
        have hyz := Subgroup.mem_center_iff.mp hz y
        rw [← map_mul, ← map_mul, hyz]
      rw [alternatingGroup.center_eq_bot (by simpa using hm)] at hc
      exact Subgroup.mem_bot.mp hc
    rw [hbot]
    simp
  · rw [not_le] at hm
    have : Group.IsSolvable (alternatingGroup (Fin m)) :=
      alternatingGroup.isSolvable (by simp; omega)
    have : Group.IsSolvable Q :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact card_center_eq_one_of_perfect_of_solvable hQ

theorem not_nine_dvd_card_center_of_mulEquiv_alternating {Q : Type} [Group Q] [Finite Q] {m : ℕ}
    (hQ : Group.IsPerfect Q) (e : Q ≃* alternatingGroup (Fin m)) :
    ¬ 9 ∣ Nat.card (Subgroup.center Q) := by
  rw [card_center_eq_one_of_perfect_alternating hQ e]
  norm_num

theorem not_nine_dvd_barM_inf_centralizer_of_nineThreeFour {G : Type} [Group G] [Finite G]
    {M S L : Subgroup G} (h : NineThreeFour M S L) :
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
  obtain ⟨-, h3, -, -, -⟩ := h
  rw [card_inf_centralizer_eq_card_center (barM M L), h3]
  norm_num

theorem not_nine_dvd_barM_inf_centralizer_of_alternating
    {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (hperf : Group.IsPerfect ↥(barM M L))
    (h : NineThreeFive M L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L) :
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
  rw [card_inf_centralizer_eq_card_center (barM M L)]
  rcases h with ⟨-, ⟨e⟩, -⟩ | ⟨-, n, ⟨e⟩, -⟩ | ⟨-, n, ⟨e⟩, -⟩ | ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩
  · exact not_nine_dvd_card_center_of_mulEquiv_alternating hperf e
  · exact not_nine_dvd_card_center_of_quot_alternating hperf e
  · exact not_nine_dvd_card_center_of_mulEquiv_alternating hperf e
  · exact not_nine_dvd_card_center_of_mulEquiv_alternating hperf e

theorem not_nine_dvd_barM_inf_centralizer_of_outcome_four_to_eight
    {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (hperf : Group.IsPerfect ↥(barM M L))
    (h : NineThreeFour M S L ∨ NineThreeFive M L ∨ NineThreeSix M S L ∨
      NineThreeSeven M S L ∨ NineThreeEight M S L) :
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
  rcases h with h4 | h
  · exact not_nine_dvd_barM_inf_centralizer_of_nineThreeFour h4
  · exact not_nine_dvd_barM_inf_centralizer_of_alternating hperf h

theorem not_nine_dvd_barM_inf_centralizer_of_nineThreeThree {G : Type} [Group G] [Finite G]
    {M S L : Subgroup G} (hL : IsWeakSBlock M S L) (h : NineThreeThree M S L) :
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
  have hq := hL.component.2.2
  have hperf : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  have hnab : ∃ a b : ↥(barM M L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := OutElemRank.exists_noncomm_of_quasisimple hq
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  rw [card_inf_centralizer_eq_card_center (barM M L),
    center_eq_bot_of_isOrthogonalTwo hperf hnab h.2.1]
  simp

theorem not_nine_dvd_barM_inf_centralizer_of_outcome_three_to_eight
    {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (hL : IsWeakSBlock M S L)
    (h : NineThreeThree M S L ∨ NineThreeFour M S L ∨ NineThreeFive M L ∨
      NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L) :
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
  have hperf : Group.IsPerfect ↥(barM M L) := ⟨hL.component.2.2.1⟩
  rcases h with h3 | h
  · exact not_nine_dvd_barM_inf_centralizer_of_nineThreeThree hL h3
  · exact not_nine_dvd_barM_inf_centralizer_of_outcome_four_to_eight hperf h

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
