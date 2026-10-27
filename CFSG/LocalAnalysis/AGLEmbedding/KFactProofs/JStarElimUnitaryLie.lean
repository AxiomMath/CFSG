module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieProfile
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem unitaryTarget_isSimpleGroup {p : ℕ} {d₀ : TauCeti.ValidLieTypeIndex}
    (hd₀ : IsUnitaryIndex p d₀) : IsSimpleGroup (CatGroup d₀) := by
  obtain ⟨-, -, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd₀ ⟨MulEquiv.refl _⟩)
  have := CFSG.UnitaryThreeRecognition.Model.isSimpleGroup_psu J _ hK hfix hq
  exact e.isSimpleGroup

theorem kFactJStarElimUnitaryLie_of (hSch : KFactCatalogSchreier) (hRee : KFactReeOrder)
    (hres : JStarResidualE6TwoTwo)
    

    : KFactJStarElimUnitaryLie := by
  intro p _ d₀ hp2 hd₀ hn2 L _ _ hs d hd hnU ⟨e⟩ hdata
  have hp : p.Prime := Fact.out
  obtain ⟨q₀, hq₀p, hq₀⟩ := hd₀
  have hfe : d₀.1.fieldExponent = q₀.exponent := by rw [hq₀]; simp
  have hcardT : Nat.card (CatGroup d₀) = ordTwistedA 2 (p ^ d₀.1.fieldExponent) := by
    rw [hfe, card_catGroup_twistedA hq₀, hq₀p]
  have hTfin : Finite (CatGroup d₀) := by
    obtain ⟨A, J, -, -, -, φ, hφ, -⟩ := hdata
    exact Finite.of_surjective φ hφ
  have hTp : p ^ (3 * d₀.1.fieldExponent) ∣ Nat.card (CatGroup d₀) :=
    pow_dvd_card_catGroup_unitary ⟨q₀, hq₀p, hq₀⟩
  have hTsimple : IsSimpleGroup (CatGroup d₀) := unitaryTarget_isSimpleGroup ⟨q₀, hq₀p, hq₀⟩
  have hTnc : ∃ a b : CatGroup d₀, a * b ≠ b * a := nonabelian_of_simple_of_sq_dvd hp
    ((pow_dvd_pow p (by omega : 2 ≤ 3 * d₀.1.fieldExponent)).trans hTp)
  have hcat : Open.IsCatalogGroup L :=
    isCatalogGroup_of_list (p := p) hp.two_le (Or.inl ⟨d, hd, ⟨e⟩⟩)
  obtain ⟨hdvd, hpb⟩ := hdata.orderTest_of_schreier hTnc (fun hnc => hSch L hs hnc hcat)
  rcases lieListProfile hRee hp2 hd e with
    ⟨m, hm, -, hN⟩ | ⟨a, ha, hUd, -, hN⟩ | ⟨a, hp3, ha, hRd, -, hN⟩ | hN |
      ⟨hp3, hN, hD4, hSp, hE6⟩ | ⟨hp5, hN⟩
  ·
    rw [hN, hcardT] at hdvd
    exact not_ordTwistedA_two_dvd_psl hp hp2 hn2 hm hdvd (hpb m (by rw [hN]; exact Dvd.intro _ rfl))
  · exact absurd hUd hnU
  ·
    subst hp3
    have hLa : 3 ^ (3 * a) ∣ Nat.card L := by
      rw [hN]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by rw [← pow_mul, mul_comm]) _) _
    rw [hN, hcardT] at hdvd
    exact not_ordTwistedA_two_dvd_ree_order hn2 (by omega) hdvd (hpb (3 * a) hLa)
  ·
    have h4 := le_of_pow_dvd_ordBC_two hp (hN ▸ hTp.trans hdvd)
    omega
  ·
    subst hp3
    rw [hcardT] at hdvd
    obtain ⟨hN6, hn⟩ := chev_three_survivors_unitary hN hn2 hdvd
    obtain ⟨q, hq, hq1, hdq⟩ := hE6 hN6
    exact hres d₀ ⟨q₀, hq₀p, hq₀⟩ (by omega) L hs d q hq hq1 hdq ⟨e⟩ hdata
  ·
    subst hp5
    exact not_five_pow_dvd_reeFFive hn2 (hN ▸ hTp.trans hdvd)

end CFSG.AGLEmbedding
