module

public import CFSG.CGT.PushingUpLit.T2KR.Sec66Lin
public import CFSG.CGT.PushingUpLit.T2KR.GenFourFinal
public import CFSG.CGT.PushingUpLit.E3A.Borel
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.CGT.PushingUpLit.T2KR.Sec66Setup

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedLieTag)
open MData (QM)

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

theorem false_of_card_sixteen (hE1 : FooteNonsolvableSimple) (hs : Sec6 G L M T n)
    (hQV : QOf L M = blockU L) (h16 : Nat.card ↥(QOf L M) = 16) : False := by
  set H := MData.ofSec6 hE1 hs with hH
  have hF : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n H.n_ne_zero
  have hQcard : Nat.card ↥(QOf L M) = (2 ^ n) ^ 2 := by
    rw [hQV, H.card_V, hF]
  have h1 : 2 ^ (n * 2) = 2 ^ 4 := by
    rw [pow_mul, ← hQcard, h16]
    norm_num
  have h2 : n * 2 = 4 := Nat.pow_right_injective (le_refl 2) h1
  have hn : n = 2 := by omega
  exact hs.sec4.noG4 (sectionalTwoRankLE_four_of_QV H hn hQV hs.sec4.sylow.le hs.sec4.sylowG)

theorem print66D1_of_list (hE1 : FooteNonsolvableSimple) (hSCL : SimpleCaseListStmt)
    (hL : ListWCIdentification) : Print66D1 := by
  intro G _ _ L M T n g hs
  have hsec : Sec6 G L M T n := hs.sec6
  have h : T2Hyp G L M n := hsec.sec4.hyp
  have := h.simple
  have hna := h.exists_noncomm
  have hQab : IsElemAbelian 2 (QOf L M) := hsec.Q_abelian
  have hQ16 : 16 ≤ Nat.card ↥(QOf L M) := hsec.sixteen_le_card_Q hE1
  have hQ4 : 4 ≤ Nat.card ↥(QOf L M) := by omega
  have hwc : IsWC (QOf L M) :=
    isWC_of_corBHyp (corBHyp_of_ti_of_weaklyClosed hQab hs.ti_form hs.wc_form)
  have hlist : ListGroup G := hSCL G hna (QOf L M) hwc hQ4
  have hstd : StdPair G (QOf L M) := hL G hlist (QOf L M) hwc hQ4
  have hQV : QOf L M = blockU L := hsec.QOf_eq_blockU hE1 hstd.transitive
  have borel : BorelTwoTransitive G (QOf L M) → False := by
    rintro ⟨-, S, hS⟩
    have hMS : M = Subgroup.normalizer ((S : Subgroup G) : Set G) := hsec.N_Q.symm.trans hS
    have hLS : L ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := hMS ▸ h.le
    have hsolv := E3A.isSolvable_normalizer_sylow S
    exact h.natBlock.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLS))
  rcases hlist with ⟨m, s, hm, hs', hmod⟩ | ⟨s, hs', hmod⟩ | ⟨s, hodd, hs3, hmod⟩ |
    ⟨k, hk6, hk9, he⟩ | hM22 | hM23 | hM24
  · by_cases hm3 : 3 ≤ m
    · have hmod' := hmod
      obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod'
      have hcardQ := (hstd.of_psl hm3 K hK e).1
      exact false_of_psl_ge3 hE1 hsec hQV hm3 hmod hcardQ
    · have hm2 : m = 2 := by omega
      subst hm2
      exact borel (hstd.of_psl2 hmod).2.2
  · exact borel (hstd.of_psu3 hs' hmod).2.2
  · exact borel (hstd.of_sz hodd hs3 hmod).2.2
  · have hcard := hstd.card_alternating hk6 hk9 he
    split_ifs at hcard <;> omega
  · exact false_of_card_sixteen hE1 hsec hQV (hstd.card_sporadic (Or.inl hM22))
  · exact false_of_card_sixteen hE1 hsec hQV (hstd.card_sporadic (Or.inr (Or.inl hM23)))
  · exact false_of_card_sixteen hE1 hsec hQV (hstd.card_sporadic (Or.inr (Or.inr hM24)))

end CFSG.CGT.PushingUpLit.T2KR
