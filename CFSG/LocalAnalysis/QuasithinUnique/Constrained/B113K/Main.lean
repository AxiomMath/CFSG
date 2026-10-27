module

public import CFSG.Quasithin.Background.B1More13
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.Overgroups
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.SylowCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Wire

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

private theorem bk6_iso_card_three {K : Type} [Group K] (h : Nat.card K = 3) :
    Nonempty (K ≃* Multiplicative (ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨mulEquivOfPrimeCardEq h (by rw [Nat.card_eq_fintype_card]; rfl)⟩

private theorem bk6_odd_of_psu {S : Type} [Group S] (h : IsPSU 3 3 1 S) :
    CFSG.Blueprint.OddLieType S := by
  have h' : StatedClassicalModel S StatedLieTag.PSU 3 3 1 := h
  exact ⟨StatedLieTag.PSU, 3, 3, 1, Nat.prime_three, by norm_num, h'.1,
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], h'⟩⟩

private theorem bk6_lieType_two {S : Type} [Group S]
    (h : CFSG.Blueprint.EvenLieType S ∨ IsPSU 3 3 1 S) :
    CFSG.Blueprint.OddLieType S ∨ CFSG.Blueprint.EvenLieType S :=
  Or.elim h (fun he => Or.inr he) (fun hp => Or.inl (bk6_odd_of_psu hp))

private theorem bk6_lieType_of_char2 {K : Type} [Group K] (h : IsLieChar2Quasi K) :
    CFSG.ASVolI.ChB.IsLieTypeQuasisimple K :=
  And.intro (B1Red.isQuasisimple_to_open h.1) (bk6_lieType_two h.2)

theorem b_1_13_of (hDet : AsB113Det CFSG.SectionRank.IsKGroupCat)
    (hCent : AsLieAltSylowCentralizer) (hOver : AsLieAltOvergroups) : CFSG.ASVolI.B_1_13 := by
  unfold CFSG.ASVolI.B_1_13
  intro V _ _ hV G hGK hO2 T K hT hKG hK hsub hKJ
  have hK' : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3 :=
    hK.imp B1Red.isQuasisimple_of_open id
  have h := B1_13 (𝒦 := CFSG.SectionRank.IsKGroupCat) hV
    ⟨B15P4.asB15Part4, hDet, hCent, hOver⟩ hGK hO2 hT hKG hK' hsub hKJ
  unfold B113Conclusion at h
  rcases h with ⟨h1, h2, h3⟩ | ⟨hC, hL⟩ | ⟨L, hLc, hKL, m, hm, hcase⟩
  · exact Or.inl ⟨bk6_iso_card_three h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨hC, Or.elim hL (fun hx => Or.inl (bk6_lieType_of_char2 hx))
      (fun hx => Or.inr hx)⟩)
  · exact Or.inr (Or.inr ⟨L, hLc, hKL, m, hm, hcase⟩)

theorem b_1_13_of_lie
    (hDet : AsB113Det CFSG.SectionRank.IsKGroupCat)
    (hLie : AsLieTwoOvergroups) (hAut : AsLieTwoSylowAut) : CFSG.ASVolI.B_1_13 :=
  b_1_13_of hDet (asLieAltSylowCentralizer_of hAut) (asLieAltOvergroups_of hLie)

theorem theoremC127_of_lie
    (hDet : AsB113Det CFSG.SectionRank.IsKGroupCat)
    (hLie : AsLieTwoOvergroups) (hAut : AsLieTwoSylowAut) (hblock : C127KBlockType) :
    TheoremC127 :=
  theoremC127_of_b113_blockType (b_1_13_of_lie hDet hLie hAut) hblock

end CFSG.Quasithin
