module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieProfile
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem kFactJStarElimLie_of (hSch : KFactCatalogSchreier) (hRee : KFactReeOrder)
    (hD4 : JStarResidualD4TwoThree) (hSp : JStarResidualSp48Three)
    (hE6 : JStarResidualE6TwoSix)
    

    : KFactJStarElimLie := by
  intro p n _ hp2 hn3 L _ _ hs d hd hnL ⟨e⟩ hdata
  have hp : p.Prime := Fact.out
  have hdata' : JStarElimDataOf L p (p ^ n * n) (PSL2GF p n) := hdata
  have hTsimple : IsSimpleGroup (PSL2GF p n) := isSimpleGroup_psl2GF_of_two_le (by omega)
  have hcardT : Nat.card (PSL2GF p n) = p ^ n * (((p ^ n) ^ 2 - 1) / 2) :=
    CFSG.SectionRank.OddCover.card_psl_two hp hp2 (GaloisField.card p n (by omega))
  have hTnc : ∃ a b : PSL2GF p n, a * b ≠ b * a := by
    refine nonabelian_of_simple_of_sq_dvd hp ?_
    rw [hcardT]
    exact (pow_dvd_pow p (by omega : 2 ≤ n)).trans (Dvd.intro _ rfl)
  have hcat : Open.IsCatalogGroup L :=
    isCatalogGroup_of_list (p := p) hp.two_le (Or.inl ⟨d, hd, ⟨e⟩⟩)
  obtain ⟨hdvd, hpb⟩ := hdata'.orderTest_of_schreier hTnc (fun hnc => hSch L hs hnc hcat)
  rcases lieListProfile hRee hp2 hd e with
    ⟨m, hm, hmd, hN⟩ | ⟨a, ha, hUd, -, hN⟩ | ⟨a, hp3, ha, hRd, -, hN⟩ | hN |
      ⟨hp3, hN, hD4', hSp', hE6'⟩ | ⟨hp5, hN⟩
  · exact absurd ⟨m, hmd⟩ hnL
  ·
    have hLa : p ^ (3 * a) ∣ Nat.card L := by
      rw [hN]
      have := pow_dvd_ordTwistedA_two (p ^ a) (Nat.one_le_pow _ _ hp.pos)
      rwa [← pow_mul, mul_comm] at this
    rw [hN, hcardT] at hdvd
    exact not_psl_dvd_ordTwistedA_two hp hp2 ha hn3 hdvd (hpb (3 * a) hLa)
  ·
    subst hp3
    have hLa : 3 ^ (3 * a) ∣ Nat.card L := by
      rw [hN]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by rw [← pow_mul, mul_comm]) _) _
    rw [hN, hcardT] at hdvd
    exact not_psl_dvd_ree_order (by omega) hn3 hdvd (hpb (3 * a) hLa)
  ·
    rw [hN, hcardT] at hdvd
    exact not_psl_dvd_ordBC_two hp hp2 hn3 hdvd
  ·
    subst hp3
    rw [hcardT] at hdvd
    rcases chev_three_survivors_psl hN hn3 hdvd hpb with
      ⟨hN1, hn⟩ | ⟨hN1, hn⟩ | ⟨hN1, hn⟩
    · obtain ⟨q, hq, hq1, hdq⟩ := hD4' hN1
      subst hn
      exact hD4 L hs d q hq hq1 hdq ⟨e⟩ hdata
    · subst hn
      exact hSp L hs d (hSp' hN1) ⟨e⟩ hdata
    · obtain ⟨q, hq, hq1, hdq⟩ := hE6' hN1
      subst hn
      exact hE6 L hs d q hq hq1 hdq ⟨e⟩ hdata
  ·
    subst hp5
    rw [hcardT] at hdvd
    rw [hN] at hdvd hpb
    exact not_psl_five_dvd_reeFFive hn3 hdvd hpb

end CFSG.AGLEmbedding
