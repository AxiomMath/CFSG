module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma102

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem c104_pRank_ge {p k : ℕ} (hp : 1 < p) {R U : Subgroup G} (hU : IsEkIn p k R U) :
    k ≤ CFSG.Open.pRank p U :=
  CFSG.SectionRank.le_pRank hp le_rfl hU.2.1 hU.2.2

theorem c104_exists_isSCp_top {p : ℕ} {Y : Subgroup G} (hY : CFSG.Open.IsElemAbelian p Y) :
    ∃ H : Subgroup G, IsSCp p ⊤ H ∧ Y ≤ H := by
  obtain ⟨H, hYH, hHmax⟩ :=
    (Set.toFinite {X : Subgroup G | CFSG.Open.IsElemAbelian p X}).exists_le_maximal
      (show Y ∈ {X : Subgroup G | CFSG.Open.IsElemAbelian p X} from hY)
  exact ⟨H, ⟨le_top, hHmax.1, fun E _ hE hHE => le_antisymm (hHmax.2 hE hHE) hHE⟩, hYH⟩

theorem c104_rank_inf_le_two {p : ℕ} (hp : p.Prime) {E A : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) (hE3 : CFSG.Open.pRank p E = 3) (hne : E ⊓ A ≠ E) :
    CFSG.Open.pRank p (E ⊓ A) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  have hX3 : 3 ≤ CFSG.Open.pRank p (E ⊓ A) := by omega
  obtain ⟨E'', hE''X, -, hE''card⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (E ⊓ A)
  have hE''ge : p ^ 3 ≤ Nat.card E'' := by
    rw [hE''card]
    exact Nat.pow_le_pow_right hp.pos hX3
  obtain ⟨r, hr⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_card_eq_pow (isPGroup_of_isElemAbelian' hE)
  have hrle : r ≤ CFSG.Open.pRank p E := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hr
  rw [hE3] at hrle
  have hEle : Nat.card E ≤ p ^ 3 := by
    rw [hr]
    exact Nat.pow_le_pow_right hp.pos hrle
  have hEeq : E'' = E :=
    Subgroup.eq_of_le_of_card_ge (hE''X.trans inf_le_left) (hEle.trans hE''ge)
  have hEX : E ≤ E ⊓ A := by
    have h := hE''X
    rw [hEeq] at h
    exact h
  exact hne (le_antisymm inf_le_left hEX)

theorem c104_inf_ne {p : ℕ} {M E A : Subgroup G} (hE : inD p M E) (hA : inDp p M A) :
    E ⊓ A ≠ E ∧ E ⊓ A ≠ A := by
  have hEsc : IsSCp p M E := hE.1.1
  have hAsc : IsSCp p M A := hA.1.1
  have hne : E ≠ A := fun hEA => hA.2 (by rw [← hEA]; exact hE.2)
  constructor
  · intro heq
    have hEA : E ≤ A := inf_eq_left.1 heq
    exact hne (hEsc.2.2 A hAsc.1 hAsc.2.1 hEA).symm
  · intro heq
    have hAE : A ≤ E := inf_eq_right.1 heq
    exact hne (hAsc.2.2 E hEsc.1 hEsc.2.1 hAE)

theorem c104_rank_inf_le_two_of_DD {p : ℕ} {M E A : Subgroup G} (hp : p.Prime)
    (hEA : IsDDpStar p M E A) (h3 : CFSG.Open.pRank p E = 3 ∨ CFSG.Open.pRank p A = 3) :
    CFSG.Open.pRank p (E ⊓ A) ≤ 2 := by
  have hE : inD p M E := hEA.1.1
  have hA : inDp p M A := hEA.1.2.1
  have hne := c104_inf_ne hE hA
  rcases h3 with h3 | h3
  · exact c104_rank_inf_le_two hp hE.1.1.2.1 h3 hne.1
  · have hne' : A ⊓ E ≠ A := by
      rw [inf_comm]
      exact hne.2
    rw [inf_comm]
    exact c104_rank_inf_le_two hp hA.1.1.2.1 h3 hne'

theorem c104_inD_of_pair {p : ℕ} {M E A : Subgroup G} (hp : p.Prime) (hEA : IsDDpStar p M E A)
    (h3 : CFSG.Open.pRank p E = 3 ∨ CFSG.Open.pRank p A = 3)
    {F X : Subgroup G} (hF : inD p M F) (hX : IsSCp p ⊤ X)
    (hFr : 4 ≤ CFSG.Open.pRank p F) (hXr : 4 ≤ CFSG.Open.pRank p X)
    (hFX : 2 ≤ CFSG.Open.pRank p (F ⊓ X)) : inD p M X := by
  have hp1 : 1 < p := hp.one_lt
  have hXM : X ≤ M :=
    (le_centralizer_of_comm' hX.2.1 (inf_le_right : F ⊓ X ≤ X)).trans
      (centralizer_inf_le_M' hF.2 hFX)
  have hXsc : IsSCp p M X :=
    ⟨hXM, hX.2.1, fun E' _ hE' hXE' => hX.2.2 E' le_top hE' hXE'⟩
  have hXstar : IsSCstar p M X := ⟨hXsc, by omega⟩
  by_cases hu : IsUniquenessTwoLocal p X M
  · exact ⟨hXstar, hu⟩
  · exfalso
    have hdd : inDDp p M F X := ⟨hF, ⟨hXstar, hu⟩, hFX⟩
    have hle := hEA.2 F X hdd
    unfold ddKey at hle
    have hb1 := c104_rank_inf_le_two_of_DD hp hEA h3
    have hmin4 : 4 ≤ min (CFSG.Open.pRank p F) (CFSG.Open.pRank p X) := le_min hFr hXr
    have hmin3 : min (CFSG.Open.pRank p E) (CFSG.Open.pRank p A) ≤ 3 := by
      rcases h3 with h3 | h3
      · exact (min_le_left _ _).trans h3.le
      · exact (min_le_right _ _).trans h3.le
    rcases Prod.Lex.toLex_le_toLex.1 hle with h1 | ⟨h1, h2⟩
    · omega
    · rcases Prod.Lex.toLex_le_toLex.1 h2 with h4 | ⟨h4, -⟩
      · omega
      · omega

end Helpers

theorem lemma104_v_of_input31_8 (hI : Input31_8) : Lemma104_vStatement := by
  intro G _ _ m p B M h E A hEA h3 R hR
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hRp : IsPGroup p ↥R := hR.2.1
  have hB : inD p M B := lemma101_ii_holds h
  have hBM : B ≤ M := hB.1.1.1
  have hBp : IsPGroup p ↥B := isPGroup_of_isElemAbelian' hB.1.1.2.1
  have h4B : 4 ≤ CFSG.Open.pRank p B := by
    have h1 : m ≤ CFSG.Open.pRank p B :=
      CFSG.SectionRank.le_pRank hp1 le_rfl hB.1.1.2.1 (h.standing.card_eq h.bOne)
    have h2 : 4 ≤ m := h.standing.four_le
    omega
  obtain ⟨x, hxM, S, hSp, hSM, hRS, hBxS⟩ :=
    exists_conj_le_pGroup' (K := M) (X := R) (Y := B) hR.1 hRp hBM hBp
  have hSR : S = R := hR.2.2 S hSM hSp hRS
  rw [hSR] at hBxS
  obtain ⟨F, hFs, hFn⟩ := h.notStar
  have hBx : inD p M (GLBConj x B) := (lemma101_i_holds h hxM hB ⟨hFs, hFn⟩).1
  have h4Bx : 4 ≤ CFSG.Open.pRank p (GLBConj x B) := by
    rw [pRank_gLBConj' hp1 x B]
    exact h4B
  obtain ⟨B4, hB4Bx, hB4el, hB4c⟩ :=
    exists_elemAbelian_card_pow_of_le_pRank' (p := p) (k := 4) (H := GLBConj x B) h4Bx
  have hB4R : IsEkIn p 4 R B4 := ⟨hB4Bx.trans hBxS, hB4el, hB4c⟩
  have hclaim : ∀ C : Subgroup G,
      Relation.ReflTransGen
        (fun U V : Subgroup G => IsEkIn p 4 R U ∧ IsEkIn p 4 R V ∧ 2 ≤ CFSG.Open.pRank p (U ⊓ V)) B4 C →
        ∀ X : Subgroup G, IsSCp p ⊤ X → C ≤ X → inD p M X := by
    intro C hC
    induction hC with
    | refl =>
      intro X hX hB4X
      have hB4r : 4 ≤ CFSG.Open.pRank p B4 := c104_pRank_ge hp1 hB4R
      have hXr : 4 ≤ CFSG.Open.pRank p X := le_trans hB4r (CFSG.SectionRank.pRank_mono hp1 hB4X)
      have hFX : 2 ≤ CFSG.Open.pRank p (GLBConj x B ⊓ X) :=
        le_trans (by omega) (CFSG.SectionRank.pRank_mono hp1 (le_inf hB4Bx hB4X))
      exact c104_inD_of_pair hp hEA h3 hBx hX h4Bx hXr hFX
    | @tail U V _ hstep ih =>
      intro X' hX' hVX'
      obtain ⟨hU4, hV4, hUV⟩ := hstep
      obtain ⟨X0, hX0, hUX0⟩ := c104_exists_isSCp_top hU4.2.1
      have hX0D : inD p M X0 := ih X0 hX0 hUX0
      have hU4r : 4 ≤ CFSG.Open.pRank p U := c104_pRank_ge hp1 hU4
      have hV4r : 4 ≤ CFSG.Open.pRank p V := c104_pRank_ge hp1 hV4
      exact c104_inD_of_pair hp hEA h3 hX0D hX'
        (le_trans hU4r (CFSG.SectionRank.pRank_mono hp1 hUX0))
        (le_trans hV4r (CFSG.SectionRank.pRank_mono hp1 hVX'))
        (le_trans hUV (CFSG.SectionRank.pRank_mono hp1 (inf_le_inf hUX0 hVX')))
  have hfirst : ∀ E4 : Subgroup G, IsEkIn p 4 R E4 → inD0 p M E4 := by
    intro E4 hE4
    have hchain := hI G p 4 hp (by norm_num) R hRp B4 E4 hB4R hE4
    obtain ⟨X, hX, hE4X⟩ := c104_exists_isSCp_top hE4.2.1
    exact ⟨hE4.1.trans hR.1, hE4.2.1, X, hclaim E4 hchain X hX hE4X, hE4X⟩
  refine ⟨hfirst, ?_⟩
  unfold GLBCore
  apply sSup_le
  rintro N ⟨Q, hQR, hk, rfl⟩
  have hQp : IsPGroup p ↥Q := IsPGroup.to_le hRp hQR
  obtain ⟨E4, hE4Q, hE4el, hE4c⟩ :=
    exists_elemAbelian_card_pow_of_le_pRank' (p := p) (k := 4) (H := Q) hk
  exact lemma102_holds h (hQR.trans hR.1) hQp (by norm_num : (2 : ℕ) ≤ 4) ⟨E4, hE4Q, hE4el, hE4c⟩
    (fun E hE => hfirst E ⟨hE.1.trans hQR, hE.2.1, hE.2.2⟩)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
