module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutBridge
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutLinTwo
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutUnitary
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutAltTen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutSmall
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven
import CFSG.RankThree.PartOne.K159.AutSzIso

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open KFAut

private theorem dvd_card_and_autMFor_psl2GF {p n : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (hn : 1 ≤ n) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    p ∣ Nat.card S ∧ AutMFor p S := by
  have hpS : p ∣ Nat.card S := by
    obtain ⟨T⟩ := Sylow.nonempty (p := p) (G := CFSG.AGLEmbedding.PSL2GF p n)
    have hT := Subgroup.card_subgroup_dvd_card
      (T : Subgroup (CFSG.AGLEmbedding.PSL2GF p n))
    rw [(CFSG.AGLEmbedding.psl2GF_sylow p n hn T).2] at hT
    rw [Nat.card_congr e.toEquiv]
    exact (dvd_pow_self p (by omega)).trans hT
  exact ⟨hpS, KFAut.autMFor_of hpS (fun X _ _ hO N hN e' =>
    KFAut.autMAt_psl2GF h5 hn hO hN (e'.trans e))⟩

private theorem dvd_card_and_autMFor_unitary {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* CFSG.AGLEmbedding.CatGroup d) :
    p ∣ Nat.card S ∧ AutMFor p S := by
  have hpS : p ∣ Nat.card S := by
    have hfe : 0 < d.1.fieldExponent := TauCeti.ValidLieTypeIndex.fieldExponent_pos d
    rw [Nat.card_congr e.toEquiv]
    exact (dvd_pow_self p (by omega : 3 * d.1.fieldExponent ≠ 0)).trans
      (CFSG.AGLEmbedding.pow_dvd_card_catGroup_unitary hd)
  exact ⟨hpS, KFAut.autMFor_of hpS (fun X _ _ hO N hN e' =>
    KFAut.autMAt_unitary h5 hd hO hN (e'.trans e))⟩

private theorem dvd_card_and_autMFor_altTen {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* alternatingGroup (Fin 10)) :
    5 ∣ Nat.card S ∧ AutMFor 5 S := by
  have hpS : 5 ∣ Nat.card S := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  exact ⟨hpS, KFAut.autMFor_of hpS (fun X _ _ hO N hN e' =>
    KFAut.autMAt_altTen hO hN (e'.trans e))⟩

private theorem dvd_card_and_autMFor_sz32
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* CFSG.AGLEmbedding.CatGroup d) :
    5 ∣ Nat.card S ∧ AutMFor 5 S := by
  obtain ⟨d1, hv⟩ := d
  obtain rfl : d1 = .suzuki 2 := hd
  have hpS : 5 ∣ Nat.card S := by
    have hcard : Nat.card S = 32537600 :=
      (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie (S := S) ⟨hv, ⟨e⟩⟩).card
    rw [hcard]
    norm_num
  exact ⟨hpS, KFAut.autMFor_of hpS (fun X _ _ hO N hN e' =>
    KFAut.autMAt_sz32 rfl hO hN (e'.trans e))⟩

private theorem dvd_card_and_autMFor_d2HeisLocalAt {i : TauCeti.CFSGIndex} {p : ℕ}
    [Fact p.Prime] (hp : p = 5 ∨ p = 11)
    (H : CFSG.AGLEmbeddingD2.D2HeisLocalAt i fun q => q = p)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (e : S ≃* i.Group) :
    p ∣ Nat.card S ∧ AutMFor p S := by
  have hC : Subgroup.centralizer ((⊤ : Subgroup S) : Set S) = ⊥ := by
    rw [show ((⊤ : Subgroup S) : Set S) = (Set.univ : Set S) by simp]
    rw [Subgroup.centralizer_univ]
    exact CFSG.AGLEmbedding.center_eq_bot_of_isSimpleGroup_nonabelian hnc
  obtain ⟨R⟩ := Sylow.nonempty (p := p) (G := S)
  obtain ⟨-, hcard, -⟩ :=
    H S ⊤ Subgroup.normal_top hC ⟨Subgroup.topEquiv.trans e⟩ p rfl R
  have hpS : p ∣ Nat.card S := by
    have hR : p ∣ Nat.card (R : Subgroup S) := by
      rw [hcard]
      exact dvd_pow_self p (by norm_num)
    exact hR.trans (Subgroup.card_subgroup_dvd_card (R : Subgroup S))
  exact ⟨hpS, KFAut.autMFor_of hpS (fun X _ _ hO N hN e' =>
    KFAut.autMAt_of_d2HeisLocalAt hp H hO hN (e'.trans e))⟩

private theorem dvd_card_and_autMFor_d2TorusLocalAt [Fact (Nat.Prime 5)]
    {i : TauCeti.CFSGIndex} (H : CFSG.AGLEmbeddingD2.D2TorusLocalAt i fun q => q = 5)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (e : S ≃* i.Group) :
    5 ∣ Nat.card S ∧ AutMFor 5 S := by
  have hC : Subgroup.centralizer ((⊤ : Subgroup S) : Set S) = ⊥ := by
    rw [show ((⊤ : Subgroup S) : Set S) = (Set.univ : Set S) by simp]
    rw [Subgroup.centralizer_univ]
    exact CFSG.AGLEmbedding.center_eq_bot_of_isSimpleGroup_nonabelian hnc
  obtain ⟨R⟩ := Sylow.nonempty (p := 5) (G := S)
  obtain ⟨-, hcard, -⟩ :=
    H S ⊤ Subgroup.normal_top hC ⟨Subgroup.topEquiv.trans e⟩ 5 rfl R
  have hpS : 5 ∣ Nat.card S := by
    have hR : 5 ∣ Nat.card (R : Subgroup S) := by
      rw [hcard]
      norm_num
    exact hR.trans (Subgroup.card_subgroup_dvd_card (R : Subgroup S))
  exact ⟨hpS, KFAut.autMFor_of hpS (fun X _ _ hO N hN e' =>
    KFAut.autMAt_of_d2TorusLocalAt H hO hN (e'.trans e))⟩

theorem kFactNineFourAutM_holds :
    KFactNineFourAutM := by
  refine KFAut.kFactNineFourAutM_of_families ?_
  intro p hp h5 S _ _ hlist hnc
  haveI : Fact p.Prime := hp
  obtain ⟨hS, i, hi, ⟨e⟩⟩ := hlist
  haveI : IsSimpleGroup S := hS
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n _ =>
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · exact dvd_card_and_autMFor_altTen e
  | sporadic s =>
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · exact dvd_card_and_autMFor_d2HeisLocalAt (Or.inl rfl)
        CFSG.AGLEmbeddingD2.d2HeisLocalAt_mcl hnc e
    · exact dvd_card_and_autMFor_d2HeisLocalAt (Or.inr rfl)
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4 hnc e
  | lie d =>
    rcases hi with ⟨q, hqp, h2, hd⟩ | ⟨q, hqp, hd⟩ | ⟨rfl, m, hm⟩ |
      ⟨rfl, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq2', hd⟩⟩ | ⟨rfl, hd | hd⟩
    · obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
        (p := p) (n := q.exponent) (d := d) ⟨q, hd, hqp, rfl⟩
      exact dvd_card_and_autMFor_psl2GF h5 (by omega) (e.trans e2)
    · exact dvd_card_and_autMFor_unitary h5 ⟨q, hqp, hd⟩ e
    · omega
    · omega
    · omega
    · exact dvd_card_and_autMFor_sz32 hd e
    · exact dvd_card_and_autMFor_d2TorusLocalAt
        (CFSG.AGLEmbeddingD2.d2TorusLocalAt_tits d hd) hnc e

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
