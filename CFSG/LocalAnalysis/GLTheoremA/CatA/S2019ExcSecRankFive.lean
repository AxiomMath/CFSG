module

public import CFSG.LieType.Chevalley.WeylSectionalTwoRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.GH74 TauCeti

private theorem sectionalTwoRankLE_seventeen_of_index {q : ℕ} (hq2 : q ≠ 2) {K : Type} [Group K]
    (d : LieTypeIndex) (hv : d.Valid) (hchar : d.characteristic = q)
    (hcore : S2019ExcCoreIdx d) (hG2 : ∀ Q, d ≠ .G2 Q)
    (hE8 : (∃ Q, d = .E8 Q) → SectionalTwoRankLE (WeylGroup .E8) 9)
    (e : K ≃* ValidLieTypeIndex.Group ⟨d, hv⟩) : SectionalTwoRankLE K 17 := by
  have hB := CFSG.TauCetiBridge.chevalleyBridges
  have hodd : ∀ Q : PrimePower, Q.p = q → Q.p ≠ 2 ∧ Odd (Q.p ^ Q.exponent) := fun Q hQ =>
    ⟨hQ ▸ hq2, (Q.prime_p.odd_of_ne_two (hQ ▸ hq2)).pow⟩
  cases d with
  | F4 Q =>
    obtain ⟨hQ2, hQo⟩ := hodd Q (by simpa using hchar)
    exact (sectionalTwoRankLE_of_untwistedChevalleyModel sectionalTwoRankLE_weylGroup_F4 hQo
      (CFSG.TauCetiBridge.untwistedModel_of_bridge hB.f4 Q hv hQ2 e)).mono (by decide)
  | E6 Q =>
    obtain ⟨hQ2, hQo⟩ := hodd Q (by simpa using hchar)
    exact (sectionalTwoRankLE_of_untwistedChevalleyModel sectionalTwoRankLE_weylGroup_E6 hQo
      (CFSG.TauCetiBridge.untwistedModel_of_bridge hB.e6 Q hv hQ2 e)).mono (by decide)
  | E7 Q =>
    obtain ⟨hQ2, hQo⟩ := hodd Q (by simpa using hchar)
    exact (sectionalTwoRankLE_of_untwistedChevalleyModel sectionalTwoRankLE_weylGroup_E7 hQo
      (CFSG.TauCetiBridge.untwistedModel_of_bridge hB.e7 Q hv hQ2 e)).mono (by decide)
  | E8 Q =>
    obtain ⟨hQ2, hQo⟩ := hodd Q (by simpa using hchar)
    exact (sectionalTwoRankLE_of_untwistedChevalleyModel (hE8 ⟨Q, rfl⟩) hQo
      (CFSG.TauCetiBridge.untwistedModel_of_bridge hB.e8 Q hv hQ2 e)).mono (by decide)
  | twistedE6 Q =>
    obtain ⟨hQ2, hQo⟩ := hodd Q (by simpa using hchar)
    exact (sectionalTwoRankLE_of_twistedChevalleyModel (t := .E6) sectionalTwoRankLE_weylGroup_E6
      hQo (CFSG.TauCetiBridge.twistedModel_of_bridge hB.twistedE6 Q hv hQ2 (by decide) e)).mono
      (by decide)
  | trialityD4 Q =>
    obtain ⟨hQ2, hQo⟩ := hodd Q (by simpa using hchar)
    exact (sectionalTwoRankLE_of_twistedChevalleyModel (t := .D4) sectionalTwoRankLE_weylGroup_D4
      hQo (CFSG.TauCetiBridge.twistedModel_of_bridge hB.trialityD4 Q hv hQ2 (by decide) e)).mono
      (by decide)
  | G2 Q => exact absurd rfl (hG2 Q)
  | _ => exact absurd hcore id

theorem s2019ExcSecRank_of_weylGroup_E8 (hE8 : SectionalTwoRankLE (WeylGroup .E8) 9) :
    S2019ExcSecRank := by
  intro q _ hq2 K _ _ hK
  obtain ⟨i, hi, ⟨eK⟩⟩ := hK
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  obtain ⟨hchar, hcore, hG2⟩ := hi
  exact sectionalTwoRankLE_seventeen_of_index hq2 d hv hchar hcore hG2 (fun _ => hE8) eK

end CFSG.LocalAnalysis.GLTheoremA.S2019

end
